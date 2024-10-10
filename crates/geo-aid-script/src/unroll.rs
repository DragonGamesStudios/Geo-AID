//! The unroll step is where syntatic sugars are extended, type checks made
//! and general script validity is checked. Technically, a script that makes
//! it past unrolling is elligible to directly compiling and generating with
//! no in-between steps.
//!
//! This is also where all information on how to handle the figure is extracted.

use crate::span;
use flags::FlagSetConstructor;
use geo_aid_derive::CloneWithNode;
use geo_aid_figure::Style;
use num_traits::{One, Zero};
use std::fmt::Formatter;
use std::mem;
use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Deref, DerefMut},
    rc::Rc,
    write,
};

use crate::figure::SpannedMathString;
use crate::ty;
use library::macros::index;

use self::context::CompileContext;
use self::figure::{
    AnyExprNode, BundleNode, CircleNode, CollectionNode, EmptyNode, FromExpr, HierarchyNode,
    LineNode, LineType, MaybeUnset, Node, PCNode, PointNode, ScalarNode,
};
use self::library::Library;

use super::parser::{
    ExprBinop, ExprCall, FieldIndex, FromProperty, InputStream, Name, PointCollectionConstructor,
    RefStatement,
};
use super::token::number::{CompExponent, ProcNum};
use super::token::Number;
use super::{
    parser::{
        BinaryOperator, DisplayProperties, ExplicitIterator, Expression, ImplicitIterator,
        LetStatement, Parse, PredefinedRuleOperator, PropertyValue, Punctuated, RuleOperator,
        RuleStatement, SimpleExpression, SimpleExpressionKind, Statement, Type,
    },
    token::{self, Ident, NamedIdent, PointCollection as PCToken, Span},
    unit, ComplexUnit, Error,
};

pub mod context;
pub mod figure;
pub mod flags;
pub mod library;

/// A helper trait for unrolling syntax nodes.
trait Unroll<T = AnyExpr> {
    fn unroll(
        &self,
        context: &mut CompileContext,
        library: &Library,
        it_index: &HashMap<u8, usize>,
        display: Properties,
    ) -> T;
}

/// A definition for a user-defined rule operator.
#[derive(Debug)]
pub struct RuleOperatorDefinition {
    /// Operator's name.
    pub name: String,
}

/// A variable created with a let statement.
#[derive(Debug)]
pub struct Variable<T: Displayed> {
    /// Variable's name
    pub name: String,
    /// Variable's definition span.
    pub definition_span: Span,
    /// Variable's definition.
    pub definition: Expr<T>,
}

/// Represents complicated iterator structures.
#[derive(Debug)]
pub struct IterTree {
    /// The variants of the top-level iterator.
    pub variants: Vec<IterNode>,
    /// The id of the top-level iterator.
    pub id: u8,
    /// The span of the top-level iterator.
    pub span: Span,
}

/// A single node of `IterTree`. Might have parallel iterator children.
/// `IterNode`s represent single iterator variants.
#[derive(Debug)]
pub struct IterNode(Vec<IterTree>);

impl Deref for IterNode {
    type Target = Vec<IterTree>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for IterNode {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<const ITER: bool> From<&Expression<ITER>> for IterNode {
    fn from(value: &Expression<ITER>) -> Self {
        match value {
            Expression::ImplicitIterator(it) => it.into(),
            Expression::Binop(binop) => Self::from2(binop.lhs.as_ref(), binop.rhs.as_ref()),
        }
    }
}

impl From<&SimpleExpressionKind> for IterNode {
    fn from(value: &SimpleExpressionKind) -> Self {
        match value {
            SimpleExpressionKind::Number(_) => IterNode::new(Vec::new()),
            SimpleExpressionKind::Name(name) => name.into(),
            SimpleExpressionKind::ExplicitIterator(it) => IterNode::new(vec![it.into()]),
            SimpleExpressionKind::PointCollection(col) => IterNode::new(
                col.points
                    .iter()
                    .flat_map(|v| IterNode::from(v).0.into_iter())
                    .collect(),
            ),
        }
    }
}

impl From<&Name> for IterNode {
    fn from(value: &Name) -> Self {
        match value {
            Name::Ident(_) => IterNode::new(Vec::new()),
            Name::FieldIndex(f) => f.name.as_ref().into(),
            Name::Call(expr) => IterNode::new(
                IterNode::from(expr.name.as_ref())
                    .0
                    .into_iter()
                    .chain(
                        expr.params
                            .as_ref()
                            .into_iter()
                            .flat_map(|params| params.iter().flat_map(|v| IterNode::from(v).0)),
                    )
                    .collect(),
            ),
            Name::Expression(expr) => expr.content.as_ref().into(),
        }
    }
}

impl<const ITER: bool> From<&ImplicitIterator<ITER>> for IterNode {
    fn from(value: &ImplicitIterator<ITER>) -> Self {
        if value.exprs.collection.is_empty() {
            (&value.exprs.first.as_ref().kind).into()
        } else {
            IterNode::new(vec![value.into()])
        }
    }
}

impl<const ITER: bool> From<&ImplicitIterator<ITER>> for IterTree {
    fn from(value: &ImplicitIterator<ITER>) -> Self {
        Self {
            id: 0, // Implicit iterators have an id of 0.
            variants: value.exprs.iter().map(|v| (&v.kind).into()).collect(),
            span: value.get_span(),
        }
    }
}

impl From<&ExplicitIterator> for IterTree {
    fn from(value: &ExplicitIterator) -> Self {
        Self {
            id: value.id,
            variants: value.exprs.iter().map(IterNode::from).collect(),
            span: value.get_span(),
        }
    }
}

impl IterTree {
    /// Collect lengths of each iterator mapped to the iterators' ids.
    ///
    /// # Errors
    /// Returns an error when there is an inconsistency in among iterators (same id, different lengths)
    /// or when an iterator with id x contains an iterator with id x.
    pub fn get_iter_lengths(
        &self,
        lengths: &mut HashMap<u8, (usize, Span, Option<Span>)>,
        full_span: Span,
    ) -> Result<(), Error> {
        for variant in &self.variants {
            variant.get_iter_lengths(lengths, full_span)?;
        }

        Ok(())
    }
}

impl IterNode {
    /// Create an empty iterator tree node.
    #[must_use]
    pub fn new(content: Vec<IterTree>) -> Self {
        Self(content)
    }

    /// Create an iterator node from two expressions. Used in binary operation unrolling.
    #[must_use]
    pub fn from2<const ITER1: bool, const ITER2: bool>(
        e1: &Expression<ITER1>,
        e2: &Expression<ITER2>,
    ) -> Self {
        let mut node = Self::from(e1);
        node.extend(Self::from(e2).0);
        node
    }

    /// Collect lengths of each iterator mapped to the iterators' ids.
    ///
    /// # Panics
    /// Never.
    ///
    /// # Errors
    /// Returns an error when there is an inconsistency in among iterators (same id, different lengths)
    /// or when an iterator with id x contains an iterator with id x.
    pub fn get_iter_lengths(
        &self,
        lengths: &mut HashMap<u8, (usize, Span, Option<Span>)>,
        full_span: Span,
    ) -> Result<(), Error> {
        for iter in &self.0 {
            match lengths.entry(iter.id) {
                Entry::Vacant(entry) => {
                    entry.insert((iter.variants.len(), iter.span, Some(iter.span)));
                }
                Entry::Occupied(mut entry) => {
                    if entry.get().0 != iter.variants.len() {
                        return Err(Error::InconsistentIterators {
                            first_span: entry.get().1,
                            first_length: entry.get().0,
                            occurred_span: iter.span,
                            occurred_length: iter.variants.len(),
                            error_span: full_span,
                        });
                    } else if let Some(parent) = entry.get().2 {
                        return Err(Error::IteratorWithSameIdIterator {
                            error_span: full_span,
                            parent_span: parent,
                            contained_span: iter.span,
                        });
                    }

                    entry.get_mut().2 = Some(iter.span);
                }
            }

            iter.get_iter_lengths(lengths, full_span)?;
            lengths.get_mut(&iter.id).unwrap().2 = None;
        }

        Ok(())
    }
}

/// A range-like iterator, except multidimensional. This in an iterator
/// in Rust's sense, not in `GeoScript`'s sense.
#[derive(Debug)]
pub struct MultiRangeIterator {
    /// The maximal indices.
    /// Maximal indices are first non-valid indice.s
    maxes: Vec<usize>,
    /// Current range indices.
    currents: Vec<usize>,
}

impl MultiRangeIterator {
    /// Create a new iterator based on maximal indices.
    #[must_use]
    pub fn new(maxes: Vec<usize>) -> Self {
        let l = maxes.len();

        Self {
            maxes,
            currents: [0].repeat(l),
        }
    }

    /// Increment the iterator.
    pub fn increment(&mut self) -> Option<&Vec<usize>> {
        self.increment_place(self.currents.len() - 1)
    }

    /// Increment the specific range.
    fn increment_place(&mut self, at: usize) -> Option<&Vec<usize>> {
        self.currents[at] += 1;

        if self.currents[at] == self.maxes[at] {
            self.currents[at] = 0;
            if at == 0 {
                None
            } else {
                self.increment_place(at - 1)
            }
        } else {
            Some(&self.currents)
        }
    }

    /// Get current range indices.
    #[must_use]
    pub fn get_currents(&self) -> &Vec<usize> {
        &self.currents
    }
}

/// An iterator (Rust) over iterator (`GeoScript`) variants.
#[derive(Debug)]
pub struct IterTreeIterator<'r> {
    /// List of lists of parallel iterators with their ids, current indices and lengths.
    steps: Vec<(Vec<(&'r IterTree, usize)>, MultiRangeIterator)>,
    /// Current index of each iterator.
    currents: Option<HashMap<u8, usize>>,
}

impl<'r> IterTreeIterator<'r> {
    /// Create a new iterator from a single tree node.
    #[must_use]
    pub fn new(tree: &'r IterNode) -> Self {
        let mut this = Self {
            steps: Vec::new(),
            currents: Some(HashMap::new()),
        };

        this.add_node(tree);

        this
    }

    /// Add a iterator tree node.
    fn add_node(&mut self, node: &'r IterNode) {
        if node.len() > 0 {
            let mut visited = Vec::new();
            let mut lengths = Vec::new();

            for tree in node.iter() {
                if !visited.contains(&tree.id) {
                    visited.push(tree.id);
                    lengths.push(tree.variants.len());
                }
            }

            self.steps.push((
                // `visited` will be in order. We can use that.
                node.iter()
                    .map(|v| {
                        (
                            v,
                            visited
                                .iter()
                                .enumerate()
                                .find(|(_, x)| **x == v.id)
                                .unwrap()
                                .0,
                        )
                    })
                    .collect(),
                MultiRangeIterator::new(lengths),
            ));
            self.update_currents();

            self.update_iterators();
        }
    }

    /// Update all iterators.
    fn update_iterators(&mut self) {
        let nodes = if let Some(node) = self.steps.last() {
            node.0
                .iter()
                .map(|iter| &iter.0.variants[node.1.get_currents()[iter.1]])
                .collect()
        } else {
            Vec::new()
        };

        for node in nodes {
            self.add_node(node);
        }
    }

    /// Update current indices.
    fn update_currents(&mut self) {
        let node = self.steps.last().unwrap();
        let currents = node.1.get_currents();

        for v in &node.0 {
            self.currents
                .as_mut()
                .unwrap()
                .entry(v.0.id)
                .and_modify(|x| *x = currents[v.1])
                .or_insert(currents[v.1]);
        }
    }

    /// Increment this iterator.
    pub fn next(&mut self) {
        while let Some(node) = self.steps.last_mut() {
            if node.1.increment().is_some() {
                self.update_currents();
                self.update_iterators();
                return;
            }

            self.steps.pop();
        }

        self.currents = None;
    }

    /// Get current iterator indices.
    #[must_use]
    pub fn get_currents(&self) -> Option<&HashMap<u8, usize>> {
        self.currents.as_ref()
    }
}

/// The kind on the unrolled rule.
#[derive(Debug)]
pub enum UnrolledRuleKind {
    /// A point equality rule (distance of 0)
    PointEq(Expr<Point>, Expr<Point>),
    /// A scalar equality
    ScalarEq(Expr<Scalar>, Expr<Scalar>),
    /// a > b
    Gt(Expr<Scalar>, Expr<Scalar>),
    /// One of the rules must be true.
    Alternative(Vec<UnrolledRule>),
    /// Bias entities in an expression. Can alter behavior of some engines.
    Bias(AnyExpr),
}

/// Helper trait for unrolled expression conversions.
pub trait ConvertFrom<T>: Displayed {
    /// Convert a value to `Self`.
    ///
    /// # Errors
    /// Returns an error if the conversion is invalid.
    fn convert_from(value: T, context: &CompileContext) -> Expr<Self>;

    /// Check if conversion from a value to `Self` can be made.
    fn can_convert_from(value: &T) -> bool;
}

/// Helper trait for unrolled expression conversions. Automatically implemented.
/// Kinda like `Into`
pub trait Convert
where
    Self: Sized,
{
    /// Convert `self` into a specific type.
    ///
    /// # Errors
    /// Returns an error if the conversion is invalid.
    fn convert<T: ConvertFrom<Self>>(self, context: &CompileContext) -> Expr<T>;

    /// Check if `self` can be converted into a specific type.
    ///
    /// # Errors
    /// Returns an error if the conversion is invalid.
    fn can_convert<T: ConvertFrom<Self>>(&self) -> bool;
}

impl<T> Convert for T {
    fn convert<U: ConvertFrom<Self>>(self, context: &CompileContext) -> Expr<U> {
        U::convert_from(self, context)
    }

    fn can_convert<U: ConvertFrom<Self>>(&self) -> bool {
        U::can_convert_from(self)
    }
}

/// Helper trait for getting the type of a value.
pub trait GetValueType {
    fn get_value_type(&self) -> Type;
}

/// Helper trait for Geo-AID type representations.
pub trait GeoType: From<Expr<Self::Target>> {
    /// The target Geo-AID type this type can be converted to.
    type Target: ConvertFrom<AnyExpr>;

    fn get_type() -> Type;
}

macro_rules! impl_x_from_x {
    ($what:ident) => {
        impl ConvertFrom<Expr<$what>> for $what {
            fn convert_from(value: Expr<$what>, _context: &CompileContext) -> Expr<Self> {
                value
            }

            fn can_convert_from(_value: &Expr<$what>) -> bool {
                true
            }
        }
    };
}

macro_rules! impl_from_any {
    ($what:ident) => {
        impl ConvertFrom<AnyExpr> for $what {
            fn convert_from(value: AnyExpr, context: &CompileContext) -> Expr<Self> {
                match value {
                    AnyExpr::Point(v) => v.convert(context),
                    AnyExpr::Line(v) => v.convert(context),
                    AnyExpr::Scalar(v) => v.convert(context),
                    AnyExpr::Circle(v) => v.convert(context),
                    AnyExpr::PointCollection(v) => v.convert(context),
                    AnyExpr::Bundle(v) => v.convert(context),
                    AnyExpr::Unknown(v) => v.convert(context),
                }
            }

            fn can_convert_from(value: &AnyExpr) -> bool {
                match value {
                    AnyExpr::Point(v) => Self::can_convert_from(v),
                    AnyExpr::Line(v) => Self::can_convert_from(v),
                    AnyExpr::Scalar(v) => Self::can_convert_from(v),
                    AnyExpr::Circle(v) => Self::can_convert_from(v),
                    AnyExpr::PointCollection(v) => Self::can_convert_from(v),
                    AnyExpr::Bundle(v) => Self::can_convert_from(v),
                    AnyExpr::Unknown(v) => Self::can_convert_from(v),
                }
            }
        }
    };
}

macro_rules! convert_err {
    ($from:ident($v:expr) -> $to:ident with $context:ident) => {{
        let v = $v;

        $context.push_error(Error::ImplicitConversionDoesNotExist {
            error_span: v.span,
            from: v.data.get_value_type(),
            to: Self::get_type(),
        });

        Expr {
            span: v.span,
            data: Rc::new($to::dummy()),
            node: None,
        }
    }};
}

macro_rules! impl_convert_err {
    ($from:ident -> $to:ident) => {
        impl ConvertFrom<Expr<$from>> for $to {
            fn convert_from(value: Expr<$from>, context: &CompileContext) -> Expr<Self> {
                convert_err!($from(value) -> $to with context)
            }

            fn can_convert_from(_value: &Expr<$from>) -> bool {
                false
            }
        }
    }
}

macro_rules! impl_from_unknown {
    {$what:ident} => {
        impl ConvertFrom<Expr<Unknown>> for $what {
            fn convert_from(value: Expr<Unknown>, _context: &CompileContext) -> Expr<Self> {
                Expr {
                    span: value.span,
                    data: Rc::new($what::dummy()),
                    node: None
                }
            }

            fn can_convert_from(_value: &Expr<Unknown>) -> bool {
                true
            }
        }
    }
}

macro_rules! impl_make_variable {
    ($what:ident) => {
        impl Expr<$what> {
            #[must_use]
            pub fn make_variable(self, name: String) -> Self {
                let sp = self.span;

                Expr {
                    span: sp,
                    data: Rc::new($what::Generic(Generic::VariableAccess(Rc::new(Variable {
                        name,
                        definition: self,
                        definition_span: sp,
                    })))),
                    node: None, // Variable references are NEVER displayed
                }
            }
        }
    };
    ($what:ident { other: $other:ident, data: $data:ident }) => {
        impl Expr<$what> {
            #[must_use]
            pub fn make_variable(self, name: String) -> Self {
                let sp = self.span;

                Expr {
                    span: sp,
                    data: Rc::new($what {
                        $other: self.data.$other,
                        data: $data::Generic(Generic::VariableAccess(Rc::new(Variable {
                            name,
                            definition: self,
                            definition_span: sp,
                        }))),
                    }),
                    node: None, // Variable references are NEVER displayed
                }
            }
        }
    };
}

macro_rules! impl_any_from_x {
    ($what:ident) => {
        impl From<Expr<$what>> for AnyExpr {
            fn from(value: Expr<$what>) -> Self {
                AnyExpr::$what(value)
            }
        }
    };
}

/// A generic expression, used with other types.
#[derive(Debug, CloneWithNode)]
pub enum Generic<T>
where
    T: Displayed,
{
    /// A reference to a variable.
    VariableAccess(Rc<Variable<T>>),
    /// A boxed expression. Used for artificial expression spanning.
    Boxed(Expr<T>),
    /// Dummy is a value specifically for continued unrolling after error occurrence.
    /// It should never show up in compilation step.
    Dummy,
}

impl<T: Display + Displayed> Display for Generic<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::VariableAccess(name) => write!(f, "{}", name.name),
            Self::Boxed(expr) => {
                write!(f, "{expr}")
            }
            Self::Dummy => write!(f, "invalid (dummy)"),
        }
    }
}

/// An unrolled point expression
#[derive(Debug, CloneWithNode)]
pub enum Point {
    /// A generic expression
    Generic(Generic<Self>),
    /// Arithmetic mean of points as complex numbers.
    Average(ClonedVec<Expr<Point>>),
    /// Intersection of two lines.
    LineLineIntersection(Expr<Line>, Expr<Line>),
    /// Center of a circle.
    CircleCenter(Expr<Circle>),
    /// A free point.
    Free,
}

impl Point {
    #[must_use]
    pub fn get_type() -> Type {
        Type::Point
    }
}

impl Dummy for Point {
    fn dummy() -> Self {
        Self::Generic(Generic::Dummy)
    }

    fn is_dummy(&self) -> bool {
        matches!(self, Self::Generic(Generic::Dummy))
    }
}

impl Displayed for Point {
    type Node = PointNode;
}

impl GetData for Point {
    fn get_data(&self) -> &Self {
        match self {
            Point::Generic(v) => match v {
                Generic::Boxed(v) => v.get_data(),
                Generic::VariableAccess(v) => v.definition.get_data(),
                Generic::Dummy => self,
            },
            _ => self,
        }
    }
}

impl Expr<Point> {
    /// Box this expression with a given span.
    #[must_use]
    pub fn boxed(mut self, span: Span) -> Self {
        let node = self.node.take();

        Self {
            span,
            data: Rc::new(Point::Generic(Generic::Boxed(self))),
            node,
        }
    }

    /// Get the point's x coordinate expression.
    #[must_use]
    pub fn x(self, span: Span, display: Properties, context: &CompileContext) -> Expr<Scalar> {
        let mut expr = Expr {
            span,
            node: None,
            data: Rc::new(Scalar {
                unit: Some(unit::DISTANCE),
                data: ScalarData::PointX(self),
            }),
        };

        expr.node = Some(HierarchyNode::from_expr(&expr, display, context));
        expr
    }

    /// Get the point's y coordinate expression.
    #[must_use]
    pub fn y(self, span: Span, display: Properties, context: &CompileContext) -> Expr<Scalar> {
        let mut expr = Expr {
            span,
            node: None,
            data: Rc::new(Scalar {
                unit: Some(unit::DISTANCE),
                data: ScalarData::PointY(self),
            }),
        };

        expr.node = Some(HierarchyNode::from_expr(&expr, display, context));
        expr
    }
}

impl GeoType for Expr<Point> {
    type Target = Point;

    fn get_type() -> Type {
        ty::POINT
    }
}

impl GetValueType for Point {
    fn get_value_type(&self) -> Type {
        ty::POINT
    }
}

impl Display for Point {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Generic(v) => write!(f, "{v}"),
            Self::Average(exprs) => write!(
                f,
                "average({})",
                exprs
                    .iter()
                    .map(|v| format!("{v}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Self::LineLineIntersection(l1, l2) => {
                write!(f, "intersection({l1}, {l2})")
            }
            Self::CircleCenter(circle) => {
                write!(f, "{circle}.center")
            }
            Self::Free => write!(f, "Free point"),
        }
    }
}

impl_x_from_x! {Point}
impl_from_any! {Point}
impl_from_unknown! {Point}
impl_convert_err! {Circle -> Point}
impl_convert_err! {Line -> Point}
impl_convert_err! {Bundle -> Point}
impl_convert_err! {Scalar -> Point}

impl_make_variable! {Point}

impl ConvertFrom<Expr<PointCollection>> for Point {
    fn convert_from(mut value: Expr<PointCollection>, context: &CompileContext) -> Expr<Self> {
        if value.data.length == 1 {
            let mut expr = index!(node value, 0);

            if let Some(pc_node) = value.node {
                if let Some(mut props) = pc_node.root.props {
                    if let Some(pt_node) = &mut expr.node {
                        pt_node.children = pc_node.children;
                        pt_node.root.display = pc_node.root.display;

                        pt_node.root.display_label = props.get("display_label").maybe_unset(true);
                        pt_node.root.label = props
                            .get("label")
                            .maybe_unset(SpannedMathString::new(span!(0, 0, 0, 0)));
                        pt_node.root.display_dot = props.get("display_dot").maybe_unset(true);
                        pt_node.root.default_label = props
                            .get("default-label")
                            .ok_or(SpannedMathString::new(span!(0, 0, 0, 0)));
                    }

                    props.ignore("default-label");
                    props.finish(context);
                }
            }

            expr
        } else {
            convert_err!(PointCollection(value) -> Point with context)
        }
    }

    fn can_convert_from(value: &Expr<PointCollection>) -> bool {
        value.data.length == 1
    }
}

/// An unrolled circle expression.
#[derive(Debug, CloneWithNode)]
pub enum Circle {
    /// A generic expression
    Generic(Generic<Self>),
    /// A circle constructed from its center and radius.
    Circle(Expr<Point>, Expr<Scalar>),
}

impl_x_from_x! {Circle}
impl_from_any! {Circle}
impl_from_unknown! {Circle}

impl_convert_err! {Point -> Circle}
impl_convert_err! {Line -> Circle}
impl_convert_err! {Bundle -> Circle}
impl_convert_err! {Scalar -> Circle}
impl_convert_err! {PointCollection -> Circle}

impl_make_variable! {Circle}

impl Circle {
    #[must_use]
    pub fn get_type() -> Type {
        ty::CIRCLE
    }
}

impl Dummy for Circle {
    fn dummy() -> Self {
        Self::Generic(Generic::Dummy)
    }

    fn is_dummy(&self) -> bool {
        matches!(self, Self::Generic(Generic::Dummy))
    }
}

impl Displayed for Circle {
    type Node = CircleNode;
}

impl GetData for Circle {
    fn get_data(&self) -> &Self {
        match self {
            Circle::Generic(v) => match v {
                Generic::Boxed(v) => v.get_data(),
                Generic::VariableAccess(v) => v.definition.get_data(),
                Generic::Dummy => self,
            },
            Circle::Circle(..) => self,
        }
    }
}

impl Expr<Circle> {
    /// Box this expression with a given span.
    #[must_use]
    pub fn boxed(mut self, span: Span) -> Self {
        let node = self.node.take();

        Self {
            span,
            data: Rc::new(Circle::Generic(Generic::Boxed(self))),
            node,
        }
    }

    /// Get the circle's center expression.
    #[must_use]
    pub fn center(self, span: Span, display: Properties, context: &CompileContext) -> Expr<Point> {
        let mut expr = Expr {
            span,
            node: None,
            data: Rc::new(Point::CircleCenter(self)),
        };

        expr.node = Some(HierarchyNode::from_expr(&expr, display, context));
        expr
    }

    /// Get the circle's radius expression.
    #[must_use]
    pub fn radius(self, span: Span, display: Properties, context: &CompileContext) -> Expr<Scalar> {
        let mut expr = Expr {
            span,
            node: None,
            data: Rc::new(Scalar {
                unit: Some(unit::DISTANCE),
                data: ScalarData::CircleRadius(self),
            }),
        };

        expr.node = Some(HierarchyNode::from_expr(&expr, display, context));
        expr
    }
}

impl GetValueType for Circle {
    fn get_value_type(&self) -> Type {
        ty::CIRCLE
    }
}

impl Display for Circle {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Generic(v) => write!(f, "{v}"),
            Self::Circle(center, radius) => {
                write!(f, "circle({center}, {radius})")
            }
        }
    }
}

impl GeoType for Expr<Circle> {
    type Target = Circle;

    fn get_type() -> Type {
        ty::CIRCLE
    }
}
/// An unrolled line expression.
#[derive(Debug, CloneWithNode)]
pub enum Line {
    /// A generic expression
    Generic(Generic<Self>),
    /// A line going through two points.
    LineFromPoints(Expr<Point>, Expr<Point>),
    /// A bisector line of an angle defined by three points.
    AngleBisector(Expr<Point>, Expr<Point>, Expr<Point>),
    /// A line perpendicular to another one, going through a specific point
    PerpendicularThrough(Expr<Line>, Expr<Point>),
    /// A line perpendicular to another one, going through a specific point
    ParallelThrough(Expr<Line>, Expr<Point>),
}

impl Line {
    #[must_use]
    pub fn get_type() -> Type {
        ty::LINE
    }
}

impl Dummy for Line {
    fn dummy() -> Self {
        Self::Generic(Generic::Dummy)
    }

    fn is_dummy(&self) -> bool {
        matches!(self, Self::Generic(Generic::Dummy))
    }
}

impl Displayed for Line {
    type Node = LineNode;
}

impl GetData for Line {
    fn get_data(&self) -> &Self {
        match self {
            Line::Generic(v) => match v {
                Generic::Boxed(v) => v.get_data(),
                Generic::VariableAccess(v) => v.definition.get_data(),
                Generic::Dummy => self,
            },
            _ => self,
        }
    }
}

impl Expr<Line> {
    /// Box the expression with a span.
    #[must_use]
    pub fn boxed(mut self, span: Span) -> Self {
        let node = self.node.take();

        Self {
            span,
            data: Rc::new(Line::Generic(Generic::Boxed(self))),
            node,
        }
    }
}

impl_x_from_x! {Line}
impl_from_any! {Line}
impl_from_unknown! {Line}
impl_convert_err! {Bundle -> Line}
impl_convert_err! {Circle -> Line}
impl_convert_err! {Point -> Line}
impl_convert_err! {Scalar -> Line}

impl_make_variable! {Line}

impl ConvertFrom<Expr<PointCollection>> for Line {
    fn convert_from(mut value: Expr<PointCollection>, context: &CompileContext) -> Expr<Self> {
        if value.data.length == 2 {
            let mut expr = context.line(index!(node value, 0), index!(node value, 1));
            if let Some(pc_node) = value.node {
                if let Some(mut props) = pc_node.root.props {
                    if let Some(ln_node) = &mut expr.node {
                        ln_node.children = pc_node.children;
                        ln_node.root.display = pc_node.root.display;

                        ln_node.root.display_label = props.get("display_label").maybe_unset(true);
                        ln_node.root.label = props
                            .get("label")
                            .maybe_unset(SpannedMathString::new(span!(0, 0, 0, 0)));
                        ln_node.root.default_label = props
                            .get("default-label")
                            .get_or(SpannedMathString::new(span!(0, 0, 0, 0)));
                        ln_node.root.style = props.get("style").maybe_unset(Style::default());
                        ln_node.root.line_type = props.get("type").maybe_unset(LineType::default());
                    }

                    props.finish(context);
                }
            }

            expr
        } else {
            convert_err!(PointCollection(value) -> Line with context)
        }
    }

    fn can_convert_from(value: &Expr<PointCollection>) -> bool {
        value.data.length == 2
    }
}

impl GetValueType for Line {
    fn get_value_type(&self) -> Type {
        ty::LINE
    }
}

impl Display for Line {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Generic(v) => write!(f, "{v}"),
            Self::LineFromPoints(e1, e2) => write!(f, "line({e1}, {e2})"),
            Self::AngleBisector(e1, e2, e3) => {
                write!(f, "angle-bisector({e1}, {e2}, {e3})")
            }
            Self::PerpendicularThrough(l, p) => {
                write!(f, "perpendicular-through({l}, {p})")
            }
            Self::ParallelThrough(l, p) => {
                write!(f, "parallel-through({l}, {p})")
            }
        }
    }
}

impl GeoType for Expr<Line> {
    type Target = Line;

    fn get_type() -> Type {
        ty::LINE
    }
}

/// An unrolled scalar expression
#[derive(Debug, CloneWithNode)]
pub enum ScalarData {
    /// A generic expression
    Generic(Generic<Scalar>),
    /// A constant
    Number(ProcNum),
    /// A distance literal not meant to be multiplied by the distance unit.
    DstLiteral(ProcNum),
    /// Override the expression's unit.
    SetUnit(Expr<Scalar>, ComplexUnit),
    /// Distance between two points.
    PointPointDistance(Expr<Point>, Expr<Point>),
    /// Distance of a point from a line.
    PointLineDistance(Expr<Point>, Expr<Line>),
    /// Minus expression
    Negate(Expr<Scalar>),
    /// a + b
    Add(Expr<Scalar>, Expr<Scalar>),
    /// a - b
    Subtract(Expr<Scalar>, Expr<Scalar>),
    /// a * b
    Multiply(Expr<Scalar>, Expr<Scalar>),
    /// a / b
    Divide(Expr<Scalar>, Expr<Scalar>),
    /// Angle defined by three points.
    ThreePointAngle(Expr<Point>, Expr<Point>, Expr<Point>),
    /// Directed angle defined by three points.
    ThreePointAngleDir(Expr<Point>, Expr<Point>, Expr<Point>),
    /// Angle between two lines.
    TwoLineAngle(Expr<Line>, Expr<Line>),
    /// The arithmetic mean of scalars.
    Average(ClonedVec<Expr<Scalar>>),
    /// Radius of a circle
    CircleRadius(Expr<Circle>),
    /// Raise a scalar to a power
    Pow(Expr<Scalar>, CompExponent),
    /// X coordinate of a point
    PointX(Expr<Point>),
    /// Y coordinate of a point
    PointY(Expr<Point>),
    /// A free scalar.
    Free,
}

impl Display for ScalarData {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Generic(v) => write!(f, "{v}"),
            Self::Average(exprs) => write!(
                f,
                "average({})",
                exprs
                    .iter()
                    .map(|v| format!("{v}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Self::Number(num) => write!(f, "{num}"),
            Self::DstLiteral(dst) => write!(f, "={dst}"),
            Self::SetUnit(expr, _) => {
                write!(f, "{expr}")
            }
            Self::PointPointDistance(e1, e2) => write!(f, "dst({e1}, {e2})"),
            Self::PointLineDistance(e1, e2) => write!(f, "dst({e1}, {e2})"),
            Self::Negate(e) => write!(f, "-{e}"),
            Self::Add(e1, e2) => write!(f, "{e1} + {e2}"),
            Self::Multiply(e1, e2) => write!(f, "{e1} * {e2}"),
            Self::Divide(e1, e2) => write!(f, "{e1} / {e2}"),
            Self::Subtract(e1, e2) => write!(f, "{e1} - {e2}"),
            Self::ThreePointAngle(e1, e2, e3) => {
                write!(f, "angle({e1}, {e2}, {e3})")
            }
            Self::ThreePointAngleDir(e1, e2, e3) => {
                write!(f, "dir_angle({e1}, {e2}, {e3})")
            }
            Self::TwoLineAngle(e1, e2) => write!(f, "angle({e1}, {e2})"),
            Self::CircleRadius(circle) => {
                write!(f, "{circle}.radius")
            }
            Self::Pow(base, exponent) => write!(f, "({base})^{exponent}"),
            Self::PointX(expr) => write!(f, "{expr}.x"),
            Self::PointY(expr) => write!(f, "{expr}.y"),
            Self::Free => write!(f, "Free scalar"),
        }
    }
}

/// A scalar with a unit.
#[derive(Debug, CloneWithNode)]
pub struct Scalar {
    pub unit: Option<ComplexUnit>,
    pub data: ScalarData,
}

impl_x_from_x! {Scalar}
impl_from_any! {Scalar}
impl_from_unknown! {Scalar}

impl_convert_err! {Point -> Scalar}
impl_convert_err! {Circle -> Scalar}
impl_convert_err! {Line -> Scalar}
impl_convert_err! {Bundle -> Scalar}

impl_make_variable! {Scalar {other: unit, data: ScalarData}}

impl Dummy for Scalar {
    fn dummy() -> Self {
        Self {
            unit: None,
            data: ScalarData::Generic(Generic::Dummy),
        }
    }

    fn is_dummy(&self) -> bool {
        matches!(self.data, ScalarData::Generic(Generic::Dummy))
    }
}

impl Displayed for Scalar {
    type Node = ScalarNode;
}

impl ConvertFrom<Expr<PointCollection>> for Scalar {
    fn convert_from(mut value: Expr<PointCollection>, context: &CompileContext) -> Expr<Self> {
        if value.data.length == 2 {
            // IMPORTANT: unwrap_or_else MUST be used to prevent
            // unnecessary props creation and drop errors.
            let display = value
                .node
                .as_mut()
                .and_then(|x| x.root.props.take())
                .unwrap_or_default();

            let mut expr = library::dst::distance_function_pp(
                index!(node value, 0),
                index!(node value, 1),
                context,
                display,
            );

            if let Some(pc_node) = value.node {
                if let Some(sc_node) = &mut expr.node {
                    sc_node.children = pc_node.children;
                    sc_node.root.display = pc_node.root.display;
                }
            }

            expr.0
        } else {
            convert_err!(PointCollection(value) -> Scalar with context)
        }
    }

    fn can_convert_from(value: &Expr<PointCollection>) -> bool {
        value.data.length == 2
    }
}

impl Scalar {
    #[must_use]
    pub fn get_type() -> Type {
        ty::SCALAR
    }
}

impl GetData for Scalar {
    fn get_data(&self) -> &Self {
        match &self.data {
            ScalarData::Generic(v) => match v {
                Generic::Boxed(v) => v.get_data(),
                Generic::VariableAccess(v) => v.definition.get_data(),
                Generic::Dummy => self,
            },
            _ => self,
        }
    }
}

impl Expr<Scalar> {
    /// Box the expression with a span.
    #[must_use]
    pub fn boxed(mut self, span: Span) -> Self {
        let node = self.node.take();

        Self {
            span,
            data: Rc::new(Scalar {
                unit: self.data.unit,
                data: ScalarData::Generic(Generic::Boxed(self)),
            }),
            node,
        }
    }

    /// Try to convert this scalar to the given unit.
    ///
    /// # Errors
    /// Returns a conversion error if it is invalid.
    ///
    /// Only valid conversions are `None` to another unit or `self` to `self`
    #[must_use]
    pub fn convert_unit(mut self, unit: Option<ComplexUnit>, context: &CompileContext) -> Self {
        let err = Error::ImplicitConversionDoesNotExist {
            error_span: self.span,
            from: self.get_value_type(),
            to: Type::Scalar(unit),
        };

        if self.data.unit == unit {
            self
        } else if unit.is_none() || self.data.unit.is_some() && self.data.unit != unit {
            context.push_error(err);

            // And pretend the conversion is valid.
            Expr {
                span: self.span,
                data: Rc::new(Scalar {
                    unit,
                    data: self.data.data.clone_without_node(),
                }),
                node: self.node.take(),
            }
        } else {
            // `unit` is concrete and self.unit is not
            Self {
                data: Rc::new(Scalar {
                    unit,
                    data: match &self.data.data {
                        ScalarData::Generic(generic) => match generic {
                            Generic::VariableAccess(_) => unreachable!(), // Always concrete
                            Generic::Boxed(v) => ScalarData::Generic(Generic::Boxed(
                                v.clone_without_node().convert_unit(unit, context),
                            )),
                            Generic::Dummy => ScalarData::Generic(Generic::Dummy),
                        },
                        v @ ScalarData::Number(_) => v.clone_without_node(),
                        ScalarData::Free => {
                            ScalarData::SetUnit(self.clone_without_node(), unit.unwrap_or_default())
                        }
                        ScalarData::DstLiteral(_)
                        | ScalarData::PointPointDistance(_, _)
                        | ScalarData::PointLineDistance(_, _)
                        | ScalarData::ThreePointAngle(_, _, _)
                        | ScalarData::ThreePointAngleDir(_, _, _)
                        | ScalarData::TwoLineAngle(_, _)
                        | ScalarData::CircleRadius(_)
                        | ScalarData::PointX(_)
                        | ScalarData::PointY(_)
                        | ScalarData::SetUnit(_, _) => unreachable!(), // Always concrete
                        ScalarData::Negate(v) => {
                            ScalarData::Negate(v.clone_without_node().convert_unit(unit, context))
                        }
                        ScalarData::Add(a, b) => {
                            // Both operands are guaranteed to be unit-less here.
                            ScalarData::Add(
                                a.clone_without_node().convert_unit(unit, context),
                                b.clone_without_node().convert_unit(unit, context),
                            )
                        }
                        ScalarData::Subtract(a, b) => {
                            // Both operands are guaranteed to be unit-less here.
                            ScalarData::Subtract(
                                a.clone_without_node().convert_unit(unit, context),
                                b.clone_without_node().convert_unit(unit, context),
                            )
                        }
                        ScalarData::Multiply(a, b) => {
                            // Both operands are guaranteed to be unit-less here.
                            ScalarData::Multiply(
                                a.clone_without_node().convert_unit(unit, context),
                                b.clone_without_node()
                                    .convert_unit(Some(unit::SCALAR), context),
                            )
                        }
                        ScalarData::Divide(a, b) => {
                            // Both operands are guaranteed to be unit-less here.
                            ScalarData::Divide(
                                a.clone_without_node().convert_unit(unit, context),
                                b.clone_without_node()
                                    .convert_unit(Some(unit::SCALAR), context),
                            )
                        }
                        ScalarData::Average(exprs) => {
                            // All will be unit-less.
                            ScalarData::Average(
                                exprs
                                    .iter()
                                    .map(|v| v.clone_without_node().convert_unit(unit, context))
                                    .collect::<Vec<_>>()
                                    .into(),
                            )
                        }
                        ScalarData::Pow(base, exponent) => ScalarData::Pow(
                            base.clone_without_node()
                                .convert_unit(unit.map(|x| x.pow(exponent.recip())), context),
                            *exponent,
                        ),
                    },
                }),
                ..self
            }
        }
    }

    /// Checks whether a unit conversion can be performed
    #[must_use]
    pub fn can_convert_unit(&self, unit: Option<ComplexUnit>) -> bool {
        !(unit.is_none() || self.data.unit.is_some() && self.data.unit != unit)
    }

    /// Make the unit concrete. If the unit is a `None`, will make it
    /// a unitless scalar. Otherwise will do nothing.
    ///
    /// # Panics
    /// If bugged
    #[must_use]
    pub fn specify_unit(self, context: &CompileContext) -> Self {
        if self.data.unit.is_none() {
            self.convert_unit(Some(unit::SCALAR), context)
        } else {
            self
        }
    }
}

impl GetValueType for Scalar {
    fn get_value_type(&self) -> Type {
        Type::Scalar(self.unit)
    }
}

impl Display for Scalar {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.data)
    }
}

/// Unrolled point collection expression data.
#[derive(Debug, CloneWithNode)]
pub enum PointCollectionData {
    /// A generic expression
    Generic(Generic<PointCollection>),
    /// A point collection in the form of a list of points.
    PointCollection(ClonedVec<Expr<Point>>),
}

impl PointCollectionData {
    #[must_use]
    pub fn as_collection(&self) -> Option<&ClonedVec<Expr<Point>>> {
        match self {
            PointCollectionData::PointCollection(v) => Some(v),
            PointCollectionData::Generic(_) => None,
        }
    }

    #[must_use]
    pub fn as_collection_mut(&mut self) -> Option<&mut ClonedVec<Expr<Point>>> {
        match self {
            PointCollectionData::PointCollection(v) => Some(v),
            PointCollectionData::Generic(_) => None,
        }
    }

    /// Get the point at the given index.
    ///
    /// # Panics
    /// If the collection isn't long enough
    #[must_use]
    pub fn index(&self, index: usize) -> Expr<Point> {
        match self {
            PointCollectionData::Generic(generic) => match generic {
                Generic::VariableAccess(var) => var.definition.index_without_node(index),
                Generic::Boxed(expr) => expr.index_without_node(index),
                Generic::Dummy => Expr::new_spanless(Point::Generic(Generic::Dummy)),
            },
            PointCollectionData::PointCollection(col) => col.get(index).map_or_else(
                || Expr::new_spanless(Point::dummy()),
                CloneWithNode::clone_without_node,
            ),
        }
    }
}

impl Display for PointCollectionData {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Generic(v) => write!(f, "{v}"),
            Self::PointCollection(col) => write!(
                f,
                "col({})",
                col.iter()
                    .map(|v| format!("{v}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
        }
    }
}

/// An unrolled point collection with size information.
#[derive(Debug, CloneWithNode)]
pub struct PointCollection {
    /// How many points this point collection has
    pub length: usize,
    /// The defining data.
    pub data: PointCollectionData,
}

impl_from_any! {PointCollection}
impl_from_unknown! {PointCollection}

impl_convert_err! {Circle -> PointCollection}
impl_convert_err! {Line -> PointCollection}
impl_convert_err! {Scalar -> PointCollection}
impl_convert_err! {Bundle -> PointCollection}

impl_make_variable! {PointCollection {other: length, data: PointCollectionData}}

impl Displayed for PointCollection {
    type Node = PCNode;
}

impl Dummy for PointCollection {
    fn dummy() -> Self {
        Self {
            length: 0,
            data: PointCollectionData::Generic(Generic::Dummy),
        }
    }

    fn is_dummy(&self) -> bool {
        matches!(self.data, PointCollectionData::Generic(Generic::Dummy))
    }
}

impl GetData for PointCollection {
    fn get_data(&self) -> &Self {
        match &self.data {
            PointCollectionData::Generic(v) => match v {
                Generic::Boxed(v) => v.get_data(),
                Generic::VariableAccess(v) => v.definition.get_data(),
                Generic::Dummy => self,
            },
            PointCollectionData::PointCollection(_) => self,
        }
    }
}

impl ConvertFrom<Expr<Point>> for PointCollection {
    fn convert_from(mut value: Expr<Point>, _context: &CompileContext) -> Expr<Self> {
        let mut node = PCNode::new();
        node.push(value.node.take());

        Expr {
            span: value.span,
            data: Rc::new(PointCollection {
                length: 1,
                data: PointCollectionData::PointCollection(vec![value].into()),
            }),
            node: Some(HierarchyNode::new(node)),
        }
    }

    fn can_convert_from(_value: &Expr<Point>) -> bool {
        true
    }
}

impl ConvertFrom<Expr<PointCollection>> for PointCollection {
    fn convert_from(mut value: Expr<PointCollection>, context: &CompileContext) -> Expr<Self> {
        if let Some(node) = &mut value.node {
            if let Some(props) = node.root.props.take() {
                props.finish(context);
            }
        }

        value
    }

    fn can_convert_from(_value: &Expr<PointCollection>) -> bool {
        true
    }
}

impl PointCollection {
    /// An associated type getter doesn't know the collection length
    /// so it returns a generic length of 0.
    #[must_use]
    pub fn get_type() -> Type {
        ty::collection(0)
    }
}

impl Expr<PointCollection> {
    /// Box the expression with the given span.
    #[must_use]
    pub fn boxed(mut self, span: Span) -> Self {
        let node = self.node.take();

        Self {
            span,
            data: Rc::new(PointCollection {
                length: self.data.length,
                data: PointCollectionData::Generic(Generic::Boxed(self)),
            }),
            node,
        }
    }

    /// Check if the collection's length matches the given length.
    /// If `length` is zero, any length is found matching.
    ///
    /// # Errors
    /// Returns an error if lengths don't match up.
    #[must_use]
    pub fn check_len(self, length: usize, context: &CompileContext) -> Self {
        if self.data.length == length
            || length == 0
            || matches!(self.data.data, PointCollectionData::Generic(Generic::Dummy))
        {
            self
        } else {
            context.push_error(Error::ImplicitConversionDoesNotExist {
                error_span: self.span,
                from: self.get_value_type(),
                to: ty::collection(length),
            });

            Self {
                data: Rc::new(PointCollection::dummy()),
                ..self
            }
        }
    }

    /// Get the point at a given index without taking the collection's node.
    #[must_use]
    pub fn index_without_node(&self, index: usize) -> Expr<Point> {
        self.data.data.index(index)
    }

    /// Get the point at a given index and take the collection's node.
    #[must_use]
    pub fn index_with_node(&mut self, index: usize) -> Expr<Point> {
        let mut point = self.data.data.index(index);
        point.node = self
            .node
            .as_mut()
            .and_then(|x| x.root.children[index].take());

        point
    }
}

impl GetValueType for PointCollection {
    fn get_value_type(&self) -> Type {
        ty::collection(self.length)
    }
}

impl Display for PointCollection {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.data)
    }
}

/// An unrolled bundle expression data
#[derive(Debug, CloneWithNode)]
pub enum BundleData {
    /// A generic expression
    Generic(Generic<Bundle>),
    /// An explicit bundle construction.
    ConstructBundle(ClonedMap<String, AnyExpr>),
}

impl Display for BundleData {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Generic(v) => write!(f, "{v}"),
            Self::ConstructBundle(fields) => {
                write!(
                    f,
                    "{{ {} }}",
                    fields
                        .iter()
                        .map(|(field, value)| format!("{field}: {value}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

/// An unrolled bundle expression with the bundle type's name.
#[derive(Debug, CloneWithNode)]
pub struct Bundle {
    pub name: &'static str,
    pub data: BundleData,
}

impl_x_from_x! {Bundle}
impl_from_any! {Bundle}
impl_from_unknown! {Bundle}

impl_convert_err! {Point -> Bundle}
impl_convert_err! {Line -> Bundle}
impl_convert_err! {Circle -> Bundle}
impl_convert_err! {Scalar -> Bundle}
impl_convert_err! {PointCollection -> Bundle}

impl_make_variable! {Bundle {other: name, data: BundleData}}

impl Bundle {
    /// Associated type getter doesn't know the specific name, so always returns `"{}"`
    #[must_use]
    pub fn get_type() -> Type {
        ty::bundle("{}")
    }

    /// Get the given field without taking its node.
    #[must_use]
    pub fn index(&self, field: &str) -> AnyExpr {
        match &self.data {
            BundleData::Generic(generic) => match &generic {
                Generic::VariableAccess(var) => var.definition.index_without_node(field),
                Generic::Boxed(expr) => expr.index_without_node(field),
                Generic::Dummy => AnyExpr::Unknown(Expr::new_spanless(Unknown::dummy())),
            },
            BundleData::ConstructBundle(map) => map.get(field).map_or_else(
                || AnyExpr::Unknown(Expr::new_spanless(Unknown::dummy())),
                CloneWithNode::clone_without_node,
            ),
        }
    }
}

impl Displayed for Bundle {
    type Node = BundleNode;
}

impl Dummy for Bundle {
    fn dummy() -> Self {
        Self {
            name: "dummy",
            data: BundleData::Generic(Generic::Dummy),
        }
    }

    fn is_dummy(&self) -> bool {
        matches!(self.data, BundleData::Generic(Generic::Dummy))
    }
}

impl Expr<Bundle> {
    /// Box the expression with the given span.
    #[must_use]
    pub fn boxed(mut self, span: Span) -> Self {
        let node = self.node.take();

        Self {
            span,
            data: Rc::new(Bundle {
                name: self.data.name,
                data: BundleData::Generic(Generic::Boxed(self)),
            }),
            node,
        }
    }

    /// Get a field's value without taking the bundle's node.
    #[must_use]
    pub fn index_without_node(&self, field: &str) -> AnyExpr {
        self.data.index(field)
    }

    /// Get a field's value and take the bundle's node.
    ///
    /// # Panics
    /// If the given field does not exist.
    #[must_use]
    pub fn index_with_node(&mut self, field: &str) -> AnyExpr {
        let mut expr = self.data.index(field);

        if let Some(self_node) = self.take_node() {
            let node: AnyExprNode = match &expr {
                AnyExpr::Point(_) => {
                    let mut n = HierarchyNode::new(<Point as Displayed>::Node::dummy());
                    n.push_child(self_node);
                    n.into()
                }
                AnyExpr::Line(_) => {
                    let mut n = HierarchyNode::new(<Line as Displayed>::Node::dummy());
                    n.push_child(self_node);
                    n.into()
                }
                AnyExpr::Scalar(_) => {
                    let mut n = HierarchyNode::new(<Scalar as Displayed>::Node::dummy());
                    n.push_child(self_node);
                    n.into()
                }
                AnyExpr::Circle(_) => {
                    let mut n = HierarchyNode::new(<Circle as Displayed>::Node::dummy());
                    n.push_child(self_node);
                    n.into()
                }
                AnyExpr::PointCollection(_) => {
                    let mut n = HierarchyNode::new(<PointCollection as Displayed>::Node::dummy());
                    n.push_child(self_node);
                    n.into()
                }
                AnyExpr::Bundle(_) => {
                    let mut n = HierarchyNode::new(<Bundle as Displayed>::Node::dummy());
                    n.push_child(self_node);
                    n.into()
                }
                AnyExpr::Unknown(_) => {
                    let mut n = HierarchyNode::new(<Unknown as Displayed>::Node::dummy());
                    n.push_child(self_node);
                    n.into()
                }
            };

            expr.replace_node(Some(node));
        }

        expr
    }

    /// Check if the bundle's name matches the given name.
    ///
    /// # Errors
    /// Returns an error if the bundle names don't match
    #[must_use]
    pub fn check_name(self, name: &'static str, context: &CompileContext) -> Self {
        if self.data.name == name || matches!(self.data.data, BundleData::Generic(Generic::Dummy)) {
            self
        } else {
            context.push_error(Error::ImplicitConversionDoesNotExist {
                error_span: self.span,
                from: self.get_value_type(),
                to: ty::bundle(name),
            });

            Self {
                data: Rc::new(Bundle::dummy()),
                ..self
            }
        }
    }
}

impl GetValueType for Bundle {
    fn get_value_type(&self) -> Type {
        ty::bundle(self.name)
    }
}

impl Display for Bundle {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.name, self.data)
    }
}

/// A special unknown type used for pushing unrolling as far as possible.
#[derive(Debug, CloneWithNode)]
pub enum Unknown {
    /// Can only be a generic expression.
    Generic(Generic<Unknown>),
}

impl_make_variable! {Unknown}

impl Dummy for Unknown {
    fn dummy() -> Self {
        Self::Generic(Generic::Dummy)
    }

    fn is_dummy(&self) -> bool {
        true
    }
}

impl Display for Unknown {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Generic(v) => write!(f, "{v}"),
        }
    }
}

impl Displayed for Unknown {
    type Node = EmptyNode;
}

impl GetValueType for Unknown {
    fn get_value_type(&self) -> Type {
        Type::Unknown
    }
}

impl Expr<Unknown> {
    /// Box the expression with the given span.
    #[must_use]
    pub fn boxed(mut self, span: Span) -> Self {
        let node = self.take_node();

        Self {
            data: Rc::new(Unknown::Generic(Generic::Boxed(self))),
            span,
            node,
        }
    }
}

/// A type-erased unrolled expression.
#[derive(Debug, CloneWithNode)]
pub enum AnyExpr {
    Point(Expr<Point>),
    Line(Expr<Line>),
    Scalar(Expr<Scalar>),
    Circle(Expr<Circle>),
    PointCollection(Expr<PointCollection>),
    Bundle(Expr<Bundle>),
    Unknown(Expr<Unknown>),
}

impl_any_from_x! {Point}
impl_any_from_x! {Line}
impl_any_from_x! {Scalar}
impl_any_from_x! {Circle}
impl_any_from_x! {PointCollection}
impl_any_from_x! {Bundle}
impl_any_from_x! {Unknown}

impl AnyExpr {
    /// Clones the expression and sets its own span. This will be treated as a separate expression now.
    #[must_use]
    pub fn get_span_mut(&mut self) -> &mut Span {
        match self {
            Self::Point(v) => &mut v.span,
            Self::Line(v) => &mut v.span,
            Self::Scalar(v) => &mut v.span,
            Self::Circle(v) => &mut v.span,
            Self::PointCollection(v) => &mut v.span,
            Self::Bundle(v) => &mut v.span,
            Self::Unknown(v) => &mut v.span,
        }
    }

    /// Get the expression's span.
    #[must_use]
    pub fn get_span(&self) -> Span {
        match self {
            Self::Point(v) => v.span,
            Self::Line(v) => v.span,
            Self::Scalar(v) => v.span,
            Self::Circle(v) => v.span,
            Self::PointCollection(v) => v.span,
            Self::Bundle(v) => v.span,
            Self::Unknown(v) => v.span,
        }
    }

    /// Replace the display node with the given node. Also returns the old node.
    pub fn replace_node(&mut self, with: Option<AnyExprNode>) -> Option<AnyExprNode> {
        Some(match self {
            Self::Point(v) => {
                AnyExprNode::Point(mem::replace(&mut v.node, with.map(AnyExprNode::to_point))?)
            }
            Self::Line(v) => {
                AnyExprNode::Line(mem::replace(&mut v.node, with.map(AnyExprNode::to_line))?)
            }
            Self::Scalar(v) => {
                AnyExprNode::Scalar(mem::replace(&mut v.node, with.map(AnyExprNode::to_scalar))?)
            }
            Self::Circle(v) => {
                AnyExprNode::Circle(mem::replace(&mut v.node, with.map(AnyExprNode::to_circle))?)
            }
            Self::PointCollection(v) => AnyExprNode::PointCollection(mem::replace(
                &mut v.node,
                with.map(AnyExprNode::to_point_collection),
            )?),
            Self::Bundle(v) => {
                AnyExprNode::Bundle(mem::replace(&mut v.node, with.map(AnyExprNode::to_bundle))?)
            }
            Self::Unknown(v) => AnyExprNode::Unknown(mem::replace(
                &mut v.node,
                with.map(AnyExprNode::to_unknown),
            )?),
        })
    }

    /// Get the node without taking it (reference).
    #[must_use]
    pub fn get_node(&self) -> Option<&dyn Node> {
        match self {
            Self::Point(x) => x.node.as_ref().map(|c| c as &dyn Node),
            Self::Line(x) => x.node.as_ref().map(|c| c as &dyn Node),
            Self::Scalar(x) => x.node.as_ref().map(|c| c as &dyn Node),
            Self::Circle(x) => x.node.as_ref().map(|c| c as &dyn Node),
            Self::PointCollection(x) => x.node.as_ref().map(|c| c as &dyn Node),
            Self::Bundle(x) => x.node.as_ref().map(|c| c as &dyn Node),
            Self::Unknown(x) => x.node.as_ref().map(|c| c as &dyn Node),
        }
    }

    #[must_use]
    pub fn to_scalar(self) -> Option<Expr<Scalar>> {
        match self {
            Self::Scalar(v) => Some(v),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_point(&self) -> Option<&Expr<Point>> {
        match self {
            Self::Point(v) => Some(v),
            _ => None,
        }
    }

    /// Get the expression's value type.
    #[must_use]
    pub fn get_type(&self) -> Type {
        match self {
            AnyExpr::Point(v) => v.get_value_type(),
            AnyExpr::Line(v) => v.get_value_type(),
            AnyExpr::Scalar(v) => v.get_value_type(),
            AnyExpr::Circle(v) => v.get_value_type(),
            AnyExpr::PointCollection(v) => v.get_value_type(),
            AnyExpr::Bundle(v) => v.get_value_type(),
            AnyExpr::Unknown(v) => v.get_value_type(),
        }
    }

    /// Convert this expression to the given type.
    ///
    /// # Errors
    /// Returns an error if the conversion is invalid.
    #[must_use]
    pub fn convert_to(self, to: Type, context: &CompileContext) -> Self {
        match to {
            Type::Point => Self::Point(self.convert(context)),
            Type::Line => Self::Line(self.convert(context)),
            Type::Scalar(unit) => Self::Scalar(self.convert(context).convert_unit(unit, context)),
            Type::PointCollection(len) => {
                Self::PointCollection(self.convert(context).check_len(len, context))
            }
            Type::Circle => Self::Circle(self.convert(context)),
            Type::Bundle(name) => Self::Bundle(self.convert(context).check_name(name, context)),
            Type::Unknown => Self::Unknown(Expr::dummy()),
        }
    }

    /// Check if this expression is convertible to the given type.
    #[must_use]
    pub fn can_convert_to(&self, to: Type) -> bool {
        match to {
            Type::Point => self.can_convert::<Point>(),
            Type::Line => self.can_convert::<Line>(),
            Type::Scalar(unit) => self.can_convert_to_scalar(unit).is_some(),
            Type::PointCollection(len) => self.can_convert_to_collection(len),
            Type::Circle => self.can_convert::<Circle>(),
            Type::Bundle(name) => self.can_convert_to_bundle(name),
            Type::Unknown => true,
        }
    }

    /// Check if the expression is convertible to the given type.
    /// Note that `unit` of `None` is ANY scalar, not UNKNOWN-UNIT scalar here.
    /// Returns `None` if conversion isn't possible and `Some` with a unit
    /// this value would be converted to. If `unit` is `None` and the value
    /// is also an unknown-unit scalar, `Some(None)` is returned.
    #[must_use]
    pub fn can_convert_to_scalar(&self, unit: Option<ComplexUnit>) -> Option<Option<ComplexUnit>> {
        match self {
            Self::Line(_) | Self::Bundle(_) | Self::Circle(_) | Self::Point(_) => None,
            Self::PointCollection(v) => (v.data.length == 2
                && (unit == Some(unit::DISTANCE) || unit.is_none()))
            .then_some(Some(unit::DISTANCE)),
            Self::Scalar(u) => (u.data.unit == unit || u.data.unit.is_none() || unit.is_none())
                .then_some(u.data.unit.or(unit)),
            Self::Unknown(_) => Some(unit),
        }
    }

    /// Check if the expression is convertible to a point collection of the given length.
    #[must_use]
    pub fn can_convert_to_collection(&self, len: usize) -> bool {
        match self {
            Self::Line(_) | Self::Bundle(_) | Self::Circle(_) | Self::Scalar(_) => false,
            Self::PointCollection(v) => v.data.length == len || len == 0,
            Self::Point(_) => len == 1,
            Self::Unknown(_) => true,
        }
    }

    /// Check if the expression is convertible to a bundle with the given name.
    #[must_use]
    pub fn can_convert_to_bundle(&self, name: &str) -> bool {
        match self {
            Self::Bundle(bundle) => bundle.data.name == name,
            Self::Unknown(_) => true,
            _ => false,
        }
    }

    /// Box an expression with the given span.
    #[must_use]
    pub fn boxed(self, span: Span) -> Self {
        match self {
            Self::Point(v) => Self::Point(v.boxed(span)),
            Self::Line(v) => Self::Line(v.boxed(span)),
            Self::Scalar(v) => Self::Scalar(v.boxed(span)),
            Self::Circle(v) => Self::Circle(v.boxed(span)),
            Self::PointCollection(v) => Self::PointCollection(v.boxed(span)),
            Self::Bundle(v) => Self::Bundle(v.boxed(span)),
            Self::Unknown(v) => Self::Unknown(v.boxed(span)),
        }
    }

    /// Get the underlying variable's defining span.
    ///
    /// # Panics
    /// Panics if not a variable.
    #[must_use]
    pub fn get_variable_span(&self) -> Span {
        match self {
            Self::Point(v) => match v.data.as_ref() {
                Point::Generic(Generic::VariableAccess(var)) => var.definition_span,
                _ => panic!("not a variable"),
            },
            Self::Line(v) => match v.data.as_ref() {
                Line::Generic(Generic::VariableAccess(var)) => var.definition_span,
                _ => panic!("not a variable"),
            },
            Self::Scalar(v) => match &v.data.data {
                ScalarData::Generic(Generic::VariableAccess(var)) => var.definition_span,
                _ => panic!("not a variable"),
            },
            Self::Circle(v) => match v.data.as_ref() {
                Circle::Generic(Generic::VariableAccess(var)) => var.definition_span,
                _ => panic!("not a variable"),
            },
            Self::PointCollection(v) => match &v.data.data {
                PointCollectionData::Generic(Generic::VariableAccess(var)) => var.definition_span,
                _ => panic!("not a variable"),
            },
            Self::Bundle(v) => match &v.data.data {
                BundleData::Generic(Generic::VariableAccess(var)) => var.definition_span,
                _ => panic!("not a variable"),
            },
            Self::Unknown(v) => match v.data.as_ref() {
                Unknown::Generic(Generic::VariableAccess(var)) => var.definition_span,
                Unknown::Generic(_) => panic!("not a variable"),
            },
        }
    }

    /// Turn this expression into a variable with the given name.
    #[must_use]
    pub fn make_variable(self, name: String) -> Self {
        match self {
            Self::Point(v) => Self::Point(v.make_variable(name)),
            Self::Line(v) => Self::Line(v.make_variable(name)),
            Self::Scalar(v) => Self::Scalar(v.make_variable(name)),
            Self::Circle(v) => Self::Circle(v.make_variable(name)),
            Self::PointCollection(v) => Self::PointCollection(v.make_variable(name)),
            Self::Bundle(v) => Self::Bundle(v.make_variable(name)),
            Self::Unknown(v) => Self::Unknown(v.make_variable(name)),
        }
    }
}

impl Dummy for AnyExpr {
    fn dummy() -> Self {
        Self::Unknown(Expr::dummy())
    }

    fn is_dummy(&self) -> bool {
        match self {
            Self::Point(v) => v.is_dummy(),
            Self::Line(v) => v.is_dummy(),
            Self::Scalar(v) => v.is_dummy(),
            Self::Circle(v) => v.is_dummy(),
            Self::PointCollection(v) => v.is_dummy(),
            Self::Bundle(v) => v.is_dummy(),
            Self::Unknown(v) => v.is_dummy(),
        }
    }
}

impl Display for AnyExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Point(v) => write!(f, "{v}"),
            Self::Line(v) => write!(f, "{v}"),
            Self::Scalar(v) => write!(f, "{v}"),
            Self::Circle(v) => write!(f, "{v}"),
            Self::PointCollection(v) => write!(f, "{v}"),
            Self::Bundle(v) => write!(f, "{v}"),
            Self::Unknown(v) => write!(f, "{v}"),
        }
    }
}

/// Helper function for displaying vectors.
pub fn display_vec<T: Display>(v: &[T]) -> String {
    v.iter()
        .map(|x| format!("{x}"))
        .collect::<Vec<String>>()
        .join(", ")
}

/// A helper trait with functions for dummy values that pretend to be valid.
pub trait Dummy {
    /// Create a dummy value pretending to be a valid one.
    #[must_use]
    fn dummy() -> Self;

    /// Check if this is a dummy value.
    #[must_use]
    fn is_dummy(&self) -> bool;
}

/// A trait with a single associated type. Used with expressions that can be displayed.
pub trait Displayed: Sized {
    /// The display node type to use for displaying `Self`
    type Node: Node;
}

/// Get the underlying data with no indirections.
pub trait GetData {
    /// Get the underlying data with no indirections.
    #[must_use]
    fn get_data(&self) -> &Self;
}

/// Used for distinction between cloning an expression AND taking its node
/// and cloning an expression WITHOUT taking its node.
pub trait CloneWithNode {
    /// Clone `self` and take its node.
    #[must_use]
    fn clone_with_node(&mut self) -> Self;

    /// Clone `self` without taking its node.
    #[must_use]
    fn clone_without_node(&self) -> Self;
}

/// Wrapper struct for a cloned vec for use with the [`CloneWithNode`]
#[derive(Debug)]
pub struct ClonedVec<T>(pub Vec<T>);

impl<T> From<Vec<T>> for ClonedVec<T> {
    fn from(value: Vec<T>) -> Self {
        Self(value)
    }
}

impl<T> Deref for ClonedVec<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for ClonedVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Wrapper struct for a cloned map used with the [`CloneWithNode`] trait.
#[derive(Debug)]
pub struct ClonedMap<K, V>(pub HashMap<K, V>);

impl<K, V> From<HashMap<K, V>> for ClonedMap<K, V> {
    fn from(value: HashMap<K, V>) -> Self {
        Self(value)
    }
}

impl<K, V> Deref for ClonedMap<K, V> {
    type Target = HashMap<K, V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K, V> DerefMut for ClonedMap<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: Clone> CloneWithNode for T {
    fn clone_with_node(&mut self) -> Self {
        self.clone()
    }

    fn clone_without_node(&self) -> Self {
        self.clone()
    }
}

impl<T: CloneWithNode> CloneWithNode for ClonedVec<T> {
    fn clone_with_node(&mut self) -> Self {
        self.iter_mut()
            .map(CloneWithNode::clone_with_node)
            .collect::<Vec<_>>()
            .into()
    }

    fn clone_without_node(&self) -> Self {
        self.iter()
            .map(CloneWithNode::clone_without_node)
            .collect::<Vec<_>>()
            .into()
    }
}

impl<K: Hash + CloneWithNode + Eq, V: CloneWithNode> CloneWithNode for ClonedMap<K, V> {
    fn clone_with_node(&mut self) -> Self {
        self.iter_mut()
            .map(|(k, v)| (k.clone_without_node(), v.clone_with_node()))
            .collect::<HashMap<_, _>>()
            .into()
    }

    fn clone_without_node(&self) -> Self {
        self.iter()
            .map(|(k, v)| (k.clone_without_node(), v.clone_without_node()))
            .collect::<HashMap<_, _>>()
            .into()
    }
}

/// An unrolled expression with a span and a display node.
#[derive(Debug)]
pub struct Expr<T: Displayed> {
    /// The expression kind.
    pub data: Rc<T>,
    /// The expression's span.
    pub span: Span,
    /// The expression's display node, if any.
    pub node: Option<HierarchyNode<T::Node>>,
}

impl<T: GetData + Displayed> Expr<T> {
    /// Get the underlying data without any indirections.
    #[must_use]
    pub fn get_data(&self) -> &T {
        self.data.get_data()
    }
}

impl<T: Displayed> CloneWithNode for Expr<T> {
    fn clone_with_node(&mut self) -> Self {
        Self {
            data: Rc::clone(&self.data),
            span: self.span,
            node: self.node.take(),
        }
    }

    fn clone_without_node(&self) -> Self {
        Self {
            data: Rc::clone(&self.data),
            span: self.span,
            node: None,
        }
    }
}

impl<T: GetValueType + Displayed> GetValueType for Expr<T> {
    fn get_value_type(&self) -> Type {
        self.data.get_value_type()
    }
}

impl<T: Display + Displayed> Display for Expr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.data)
    }
}

impl<T: CloneWithNode + Displayed> Expr<T> {
    /// Creates a new expression without a declared span. WARNING: the expression has no node.
    #[must_use]
    pub fn new_spanless(data: T) -> Self {
        Self {
            span: span!(0, 0, 0, 0),
            data: Rc::new(data),
            node: None,
        }
    }

    /// Take the expression's display node.
    pub fn take_node(&mut self) -> Option<HierarchyNode<T::Node>> {
        self.node.take()
    }
}

impl<T: CloneWithNode + Displayed + Dummy> Dummy for Expr<T> {
    fn dummy() -> Self {
        Self::new_spanless(T::dummy())
    }

    fn is_dummy(&self) -> bool {
        self.data.is_dummy()
    }
}

/// An unrolled rule with a kind and additional data.
#[derive(Debug)]
pub struct UnrolledRule {
    /// The kind of this rule
    pub kind: UnrolledRuleKind,
    /// Whether the rule is inverted
    pub inverted: bool,
    /// The rule's weight
    pub weight: ProcNum,
}

impl Display for UnrolledRule {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let inv = if self.inverted { "!" } else { "" };

        match &self.kind {
            UnrolledRuleKind::PointEq(a, b) => write!(f, "{a} {inv}= {b}"),
            UnrolledRuleKind::ScalarEq(a, b) => write!(f, "{a} {inv}= {b}"),
            UnrolledRuleKind::Gt(a, b) => {
                write!(f, "{a} {} {b}", if self.inverted { "<=" } else { ">" })
            }
            UnrolledRuleKind::Alternative(v) => {
                write!(
                    f,
                    "{}",
                    v.iter()
                        .map(|x| format!("{x}"))
                        .collect::<Vec<String>>()
                        .join(" || ")
                )
            }
            UnrolledRuleKind::Bias(v) => write!(f, "bias {v}"),
        }
    }
}

// /// A point id is a 64-bit integer. First 32 bits are for the letter codepoint, next 8 for the amount of primes, next 16 for the point index.
// fn construct_point_id(letter: char, primes: u8) -> u64 {
//     ((letter as u64) << 8) | u64::from(primes)
// }

/// Constructs the point name based on the letter and the primes.
#[must_use]
pub fn construct_point_name(letter: char, primes: u8) -> String {
    String::from(letter) + &"'".repeat(primes as usize)
}

/// Fetch the variable's defining expression by its name.
fn fetch_variable(context: &CompileContext, name: &str, variable_span: Span) -> AnyExpr {
    let mut var = if let Some(var) = context.variables.get(name) {
        var.clone_without_node()
    } else {
        let suggested = most_similar(context.variables.keys(), name);

        context.push_error(Error::UndefinedVariable {
            error_span: variable_span,
            variable_name: name.to_string(),
            suggested: suggested.cloned(),
        });

        Expr::new_spanless(Unknown::dummy())
            .make_variable(name.to_string())
            .into()
    };

    *var.get_span_mut() = variable_span;
    var
}

impl Unroll for SimpleExpression {
    fn unroll(
        &self,
        context: &mut CompileContext,
        library: &Library,
        it_index: &HashMap<u8, usize>,
        display: Properties,
    ) -> AnyExpr {
        let display = Properties::from(self.display.clone()).merge_with(display);

        let unrolled = self.kind.unroll(context, library, it_index, display);
        let unrolled = if let Some(exponent) = &self.exponent {
            let mut unrolled: Expr<Scalar> = unrolled.convert(context);
            let node = unrolled.node.take();

            let exponent = match exponent.exponent.as_comp() {
                Ok(v) => {
                    if self.minus.is_some() {
                        -v
                    } else {
                        v
                    }
                }
                Err(err) => {
                    context.push_error(err);
                    CompExponent::one()
                }
            };

            AnyExpr::Scalar(Expr {
                span: self.get_span(),
                data: Rc::new(Scalar {
                    unit: unrolled.data.unit.map(|v| v.pow(exponent)),
                    data: ScalarData::Pow(unrolled, exponent),
                }),
                node,
            })
        } else {
            unrolled
        };

        if self.minus.is_some() {
            let mut unrolled: Expr<Scalar> = unrolled.convert(context);
            let node = unrolled.node.take();

            AnyExpr::Scalar(Expr {
                span: self.get_span(),
                data: Rc::new(Scalar {
                    unit: unrolled.data.unit,
                    data: ScalarData::Negate(unrolled),
                }),
                node,
            })
        } else {
            unrolled
        }
    }
}

/// A function reference: either a named one or a method.
#[derive(Debug)]
pub enum FuncRef {
    Function(String),
    /// Method with the given name on the given value.
    Method(String, AnyExpr),
    /// An invalid function reference
    Invalid,
}

impl Unroll for Ident {
    fn unroll(
        &self,
        context: &mut CompileContext,
        _library: &Library,
        _it_index: &HashMap<u8, usize>,
        display: Properties,
    ) -> AnyExpr {
        match self {
            Ident::Named(named) => {
                // No options are expected, as var refs don't generate nodes.
                display.finish(context);

                fetch_variable(context, &named.ident, named.span)
            }
            Ident::Collection(col) => {
                let mut display = display;
                let display_pc = display.get("display").maybe_unset(true);

                let mut pc_children = Vec::new();
                pc_children.resize_with(col.collection.len(), || None);

                // No options are expected, as pcs don't generate nodes.
                AnyExpr::PointCollection(Expr {
                    data: Rc::new(PointCollection {
                        length: col.collection.len(),
                        data: PointCollectionData::PointCollection(
                            col.collection
                                .iter()
                                .map(|item| {
                                    fetch_variable(context, &format!("{item}"), col.span)
                                        .convert::<Point>(context)
                                })
                                .collect::<Vec<_>>()
                                .into(),
                        ),
                    }),
                    span: col.span,
                    node: Some(HierarchyNode::new(PCNode {
                        display: display_pc,
                        children: pc_children,
                        props: Some(display),
                    })),
                })
            }
        }
    }
}

impl Unroll for ExprCall {
    fn unroll(
        &self,
        context: &mut CompileContext,
        library: &Library,
        it_index: &HashMap<u8, usize>,
        mut display: Properties,
    ) -> AnyExpr {
        let name = self
            .name
            .unroll(context, library, it_index, Properties::default());

        let (func_name, self_param) = match name {
            FuncRef::Function(x) => (x, None),
            FuncRef::Method(x, y) => (x, Some(y)),
            FuncRef::Invalid => return AnyExpr::Unknown(Expr::new_spanless(Unknown::dummy())),
        };

        let self_type = self_param.as_ref().map(AnyExpr::get_type);

        let mut params = Vec::new();
        params.extend(self_param);

        if let Some(parsed) = &self.params {
            for p in parsed.iter() {
                params.push(p.unroll(context, library, it_index, Properties::default()));
            }
        }

        let func = match self_type {
            Some(t) => library.get_method(t, &func_name),
            None => library.get_function(&func_name)
        };

        let res = match func {
            Ok(func) => {
                if let Some(overload) = func.get_overload(&params) {
                    let ret = overload.unroll(params, context, display);

                    return ret.boxed(self.get_span());
                }

                context.push_error(Error::OverloadNotFound {
                    error_span: self.get_span(),
                    function_name: func_name.clone(),
                    params: params.iter().map(AnyExpr::get_type).collect(),
                });

                Expr {
                    data: Rc::new(Unknown::dummy()),
                    span: self.get_span(),
                    node: None,
                }
                .into()
            }
            Err(suggested) => {
                if let Some(self_type) = self_type {
                    context.push_error(Error::UndefinedMethod {
                        error_span: self.name.get_span(),
                        function_name: func_name,
                        on_type: self_type,
                        suggested,
                    });
                } else {
                    context.push_error(Error::UndefinedFunction {
                        error_span: self.name.get_span(),
                        function_name: func_name.clone(),
                        suggested,
                    });
                }

                Expr::new_spanless(Unknown::dummy()).into()
            }
        };

        for mut param in params {
            if let Some(AnyExprNode::PointCollection(mut pc)) = param.replace_node(None) {
                if let Some(props) = pc.root.props.take() {
                    props.finish(context);
                }
            }
        }

        display.ignore_all();
        display.finish(context);

        res
    }
}

impl Unroll for FieldIndex {
    fn unroll(
        &self,
        context: &mut CompileContext,
        library: &Library,
        it_index: &HashMap<u8, usize>,
        display: Properties,
    ) -> AnyExpr {
        let name: AnyExpr = self
            .name
            .unroll(context, library, it_index, Properties::default());

        let name = if name.get_type() == Type::PointCollection(1) {
            name.convert_to(Type::Point, context)
        } else {
            name
        };

        match name {
            AnyExpr::Circle(circle) => match &self.field {
                Ident::Named(named) => match named.ident.as_str() {
                    "center" => circle.center(self.get_span(), display, context).into(),
                    "radius" => circle.radius(self.get_span(), display, context).into(),
                    x => {
                        display.finish(context);

                        context.push_error(Error::UndefinedField {
                            error_span: self.get_span(),
                            field: x.to_string(),
                            on_type: ty::CIRCLE,
                            suggested: most_similar(["center", "radius"], x),
                        });

                        AnyExpr::dummy()
                    }
                },
                Ident::Collection(x) => {
                    display.finish(context);

                    context.push_error(Error::UndefinedField {
                        error_span: self.get_span(),
                        field: x.to_string(),
                        on_type: ty::CIRCLE,
                        suggested: most_similar(["center", "radius"], &x.to_string()),
                    });

                    AnyExpr::dummy()
                }
            },
            AnyExpr::Point(point) => match &self.field {
                Ident::Named(named) => match named.ident.as_str() {
                    "x" => point.x(self.get_span(), display, context).into(),
                    "y" => point.y(self.get_span(), display, context).into(),
                    x => {
                        display.finish(context);

                        context.push_error(Error::UndefinedField {
                            error_span: self.get_span(),
                            field: x.to_string(),
                            on_type: ty::CIRCLE,
                            suggested: most_similar(["x", "y"], x),
                        });

                        AnyExpr::dummy()
                    }
                },
                Ident::Collection(x) => {
                    display.finish(context);

                    context.push_error(Error::UndefinedField {
                        error_span: self.get_span(),
                        field: x.to_string(),
                        on_type: ty::POINT,
                        suggested: most_similar(["x", "y"], &x.to_string()),
                    });

                    AnyExpr::dummy()
                }
            },
            AnyExpr::Bundle(mut bundle) => {
                display.finish(context);
                let field_name = self.field.to_string();
                let bundle_fields = library.get_bundle(bundle.data.name);

                if bundle_fields.contains(field_name.as_str()) {
                    bundle
                        .index_with_node(&self.field.to_string())
                        .boxed(self.get_span())
                } else {
                    let suggested = most_similar(bundle_fields.iter().copied(), &field_name);

                    context.push_error(Error::UndefinedField {
                        error_span: self.get_span(),
                        field: field_name,
                        on_type: bundle.get_value_type(),
                        suggested,
                    });

                    AnyExpr::dummy()
                }
            }
            AnyExpr::Unknown(_) => {
                display.finish(context);
                AnyExpr::dummy()
            }
            v @ (AnyExpr::Scalar(_) | AnyExpr::Line(_) | AnyExpr::PointCollection(_)) => {
                display.finish(context);

                context.push_error(Error::NoFieldsOnType {
                    error_span: self.get_span(),
                    on_type: v.get_type(),
                });

                AnyExpr::dummy()
            }
        }
    }
}

impl Unroll for Name {
    fn unroll(
        &self,
        context: &mut CompileContext,
        library: &Library,
        it_index: &HashMap<u8, usize>,
        display: Properties,
    ) -> AnyExpr {
        match self {
            Self::Ident(i) => i.unroll(context, library, it_index, display),
            Self::Call(expr) => expr.unroll(context, library, it_index, display),
            Self::Expression(v) => v.content.unroll(context, library, it_index, display),
            Self::FieldIndex(v) => v.unroll(context, library, it_index, display),
        }
    }
}

impl Unroll<FuncRef> for Name {
    fn unroll(
        &self,
        context: &mut CompileContext,
        library: &Library,
        it_index: &HashMap<u8, usize>,
        display: Properties,
    ) -> FuncRef {
        display.finish(context);

        match self {
            Self::Ident(Ident::Named(n)) => FuncRef::Function(n.ident.clone()),
            Self::FieldIndex(f) => {
                let self_param: AnyExpr =
                    f.name
                        .unroll(context, library, it_index, Properties::default());
                let name = match &f.field {
                    Ident::Named(n) => n.ident.clone(),
                    Ident::Collection(_) => {
                        context.push_error(Error::ExpectedFunction {
                            error_span: self.get_span(),
                        });

                        return FuncRef::Invalid;
                    }
                };

                match self_param {
                    AnyExpr::Unknown(_) => FuncRef::Invalid,
                    self_param => {
                        FuncRef::Method(name, self_param)
                    }
                }
            }
            _ => {
                context.push_error(Error::ExpectedFunction {
                    error_span: self.get_span(),
                });

                FuncRef::Invalid
            }
        }
    }
}

impl Unroll for Number {
    fn unroll(
        &self,
        context: &mut CompileContext,
        _library: &Library,
        _it_index: &HashMap<u8, usize>,
        display: Properties,
    ) -> AnyExpr {
        display.finish(context);

        AnyExpr::Scalar(Expr {
            data: Rc::new(Scalar {
                unit: None,
                data: ScalarData::Number(self.into()),
            }),
            span: self.get_span(),
            node: None,
        })
    }
}

impl Unroll for ExplicitIterator {
    fn unroll(
        &self,
        context: &mut CompileContext,
        library: &Library,
        it_index: &HashMap<u8, usize>,
        display: Properties,
    ) -> AnyExpr {
        self.get(it_index[&self.id])
            .unwrap()
            .unroll(context, library, it_index, display)
    }
}

impl Unroll for PointCollectionConstructor {
    fn unroll(
        &self,
        context: &mut CompileContext,
        library: &Library,
        it_index: &HashMap<u8, usize>,
        mut display: Properties,
    ) -> AnyExpr {
        let display_pc = display.get("display").maybe_unset(true);

        let mut pc_children = Vec::new();
        pc_children.resize_with(self.points.len(), || None);

        AnyExpr::PointCollection(Expr {
            span: self.get_span(),
            data: Rc::new(PointCollection {
                length: self.points.len(),
                data: PointCollectionData::PointCollection({
                    let mut points = Vec::new();

                    for expr in self.points.iter() {
                        let mut unrolled =
                            expr.unroll(context, library, it_index, Properties::default());

                        if unrolled.can_convert_to(ty::POINT) {
                            points.push(unrolled.convert(context));
                        } else {
                            context.push_error(Error::NonPointInPointCollection {
                                error_span: self.get_span(),
                                received: (expr.get_span(), unrolled.get_type()), // (span, from)
                            });

                            // Pretend the point is valid.
                            points.push(Expr {
                                span: unrolled.get_span(),
                                data: Rc::new(Point::dummy()),
                                node: unrolled.replace_node(None).map(AnyExprNode::to_point),
                            });
                        }
                    }

                    for pt in &mut points {
                        pc_children.push(pt.take_node());
                    }

                    points.into()
                }),
            }),
            node: Some(HierarchyNode::new(PCNode {
                display: display_pc,
                children: pc_children,
                props: Some(display),
            })),
        })
    }
}

impl Unroll for SimpleExpressionKind {
    fn unroll(
        &self,
        context: &mut CompileContext,
        library: &Library,
        it_index: &HashMap<u8, usize>,
        display: Properties,
    ) -> AnyExpr {
        match self {
            Self::Name(name) => name.unroll(context, library, it_index, display),
            Self::Number(num) => num.unroll(context, library, it_index, display),
            Self::ExplicitIterator(it) => it.unroll(context, library, it_index, display),
            Self::PointCollection(col) => col.unroll(context, library, it_index, display),
        }
    }
}

impl<const ITER: bool> Unroll for ExprBinop<ITER> {
    fn unroll(
        &self,
        context: &mut CompileContext,
        library: &Library,
        it_index: &HashMap<u8, usize>,
        display: Properties,
    ) -> AnyExpr {
        let lhs = self
            .lhs
            .unroll(context, library, it_index, Properties::default());
        let rhs = self
            .rhs
            .unroll(context, library, it_index, Properties::default());

        let mut lhs = if lhs.can_convert_to(ty::SCALAR_UNKNOWN) {
            lhs.convert::<Scalar>(context)
        } else {
            context.push_error(Error::InvalidOperandType {
                error_span: Box::new(self.get_span()),
                got: (lhs.get_type(), Box::new(lhs.get_span())),
                op: self.operator.to_string(),
            });

            Expr {
                span: lhs.get_span(),
                data: Rc::new(Scalar::dummy()),
                node: None,
            }
        };

        let mut rhs = if rhs.can_convert_to(ty::SCALAR_UNKNOWN) {
            rhs.convert::<Scalar>(context)
        } else {
            context.push_error(Error::InvalidOperandType {
                error_span: Box::new(self.get_span()),
                got: (rhs.get_type(), Box::new(rhs.get_span())),
                op: self.operator.to_string(),
            });

            Expr {
                span: rhs.get_span(),
                data: Rc::new(Scalar::dummy()),
                node: None,
            }
        };

        // Binary operators generate collection nodes for the lhs and rhs nodes.
        let lhs_node = lhs.take_node();
        let rhs_node = rhs.take_node();

        match &self.operator {
            BinaryOperator::Add(_) | BinaryOperator::Sub(_) => {
                let lhs = if lhs.data.unit.is_none() {
                    lhs.convert_unit(rhs.data.unit, context)
                } else {
                    lhs
                };

                let rhs = rhs.convert_unit(lhs.data.unit, context);
                let mut expr = Expr {
                    span: self.get_span(),
                    data: Rc::new(Scalar {
                        unit: rhs.data.unit,
                        data: match &self.operator {
                            BinaryOperator::Add(_) => ScalarData::Add(lhs, rhs),
                            BinaryOperator::Sub(_) => ScalarData::Subtract(lhs, rhs),
                            _ => unreachable!(),
                        },
                    }),
                    node: None,
                };

                let mut node = HierarchyNode::new(ScalarNode::from_expr(&expr, display, context));
                node.extend_children(lhs_node);
                node.extend_children(rhs_node);

                expr.node = Some(node);

                AnyExpr::Scalar(expr)
            }
            BinaryOperator::Mul(_) | BinaryOperator::Div(_) => {
                let lhs = lhs.specify_unit(context);

                let rhs = rhs.specify_unit(context);
                let mut expr = Expr {
                    span: self.get_span(),
                    data: Rc::new(Scalar {
                        unit: Some(lhs.data.unit.unwrap() * rhs.data.unit.as_ref().unwrap()),
                        data: match &self.operator {
                            BinaryOperator::Mul(_) => ScalarData::Multiply(lhs, rhs),
                            BinaryOperator::Div(_) => ScalarData::Divide(lhs, rhs),
                            _ => unreachable!(),
                        },
                    }),
                    node: None,
                };

                let mut node = HierarchyNode::new(ScalarNode::from_expr(&expr, display, context));
                node.extend_children(lhs_node);
                node.extend_children(rhs_node);

                expr.node = Some(node);

                AnyExpr::Scalar(expr)
            }
        }
    }
}

impl<const ITER: bool> Unroll for ImplicitIterator<ITER> {
    fn unroll(
        &self,
        context: &mut CompileContext,
        library: &Library,
        it_index: &HashMap<u8, usize>,
        display: Properties,
    ) -> AnyExpr {
        if self.exprs.collection.is_empty() {
            self.exprs.first.as_ref()
        } else {
            // Implicits always have id=0
            self.get(it_index[&0]).unwrap()
        }
        .unroll(context, library, it_index, display)
    }
}

impl<const ITER: bool> Unroll for Expression<ITER> {
    fn unroll(
        &self,
        context: &mut CompileContext,
        library: &Library,
        it_index: &HashMap<u8, usize>,
        display: Properties,
    ) -> AnyExpr {
        match self {
            Expression::ImplicitIterator(it) => it.unroll(context, library, it_index, display),
            Expression::Binop(op) => op.unroll(context, library, it_index, display),
        }
    }
}

// /// Unpacks the expressed type as a point collection.
// fn unpack_expression(
//     expr: &AnyExpr,
//     _context: &CompileContext,
// ) -> Result<Vec<Expr<Point>>, Error> {
//     match expr {
//
//         Type::Point => Ok(vec![expr.clone()]),
//         Type::PointCollection(l) => Ok((0..*l)
//             .map(|i| Expr {
//                 weight: FastFloat::One, // Weight propagated through `IndexCollection`
//                 data: Rc::new(UnrolledExpressionData::IndexCollection(expr.clone(), i)),
//                 ty: ty::POINT,
//                 span: expr.span,
//             })
//             .collect()),
//         ty => Err(Error::cannot_unpack(
//             expr.span,
//             *ty,
//         )),
//     }
// }

/// A generic helper function for finding the string most similar to the given one
/// from a list of strings.
pub fn most_similar<'r, I: IntoIterator<Item = &'r T>, T: AsRef<str> + ?Sized + 'r>(
    expected: I,
    received: &str,
) -> Option<&'r T> {
    #[allow(clippy::cast_possible_truncation)]
    expected
        .into_iter()
        .map(|v| {
            (
                v,
                (strsim::jaro(v.as_ref(), received) * 1000.0).floor() as i64,
            )
        })
        .filter(|v| v.1 > 600)
        .max_by_key(|v| v.1)
        .map(|v| v.0)
}

/// Properties, commonly used for display options.
#[derive(Debug)]
pub struct Properties {
    /// Name-(span, value) pairs.
    props: HashMap<String, (Span, PropertyValue)>,
    /// Whether the properties are safe to close.
    finished: bool,
    /// Errors encountered when parsing properties
    errors: Vec<Error>,
    /// Expected properties (not mandatory). Used for finding most similar
    /// properties to the ones that were never read.
    expected: Vec<&'static str>,
}

impl Display for Properties {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;

        for (k, v) in &self.props {
            write!(f, "{k} = {}, ", v.1)?;
        }

        write!(f, "]")
    }
}

impl Clone for Properties {
    fn clone(&self) -> Self {
        Self {
            props: self.props.clone(),
            finished: false,
            errors: Vec::new(),
            expected: Vec::new(),
        }
    }
}

// Just in case.
#[allow(clippy::derivable_impls)]
impl Default for Properties {
    fn default() -> Self {
        Self {
            props: HashMap::new(),
            finished: false,
            errors: Vec::new(),
            expected: Vec::new(),
        }
    }
}

impl Properties {
    /// Finish parsing these properties and submit all their errors.
    pub fn finish(mut self, context: &CompileContext) {
        self.finished = true;

        let props = mem::take(&mut self.props);
        let expected = mem::take(&mut self.expected);

        self.errors.extend(props.into_iter().map(|(key, value)| {
            let suggested = most_similar(expected.iter().copied(), &key);

            Error::UnexpectedDisplayOption {
                error_span: value.0,
                option: key,
                suggested,
            }
        }));

        context.extend_errors(mem::take(&mut self.errors));
    }

    /// Get a property value by its name.
    #[must_use]
    pub fn get<T: FromProperty>(&mut self, property: &'static str) -> Property<T> {
        if let Some((_, prop)) = self.props.remove(property) {
            let prop_span = prop.get_span();

            Property {
                value: match T::from_property(prop) {
                    Ok(v) => Some(v),
                    Err(err) => {
                        self.errors.push(err);
                        None
                    }
                },
                span: Some(prop_span),
            }
        } else {
            self.expected.push(property);

            Property {
                value: None,
                span: None,
            }
        }
    }

    /// Ignore the given property.
    pub fn ignore(&mut self, property: &'static str) {
        self.props.remove(property);
    }

    /// Add a property along with a value if it is not present yet.
    pub fn add_if_not_present(
        &mut self,
        property: &'static str,
        (key_span, value): (Span, PropertyValue),
    ) {
        self.props
            .entry(property.to_string())
            .or_insert((key_span, value));
    }

    /// Merge the properties with other properties. Automatically finished the other properties.
    #[must_use]
    pub fn merge_with(mut self, mut other: Properties) -> Self {
        self.errors.extend(mem::take(&mut other.errors));

        for (k, v) in mem::take(&mut other.props) {
            let error_span = v.0;
            let option = k.clone();
            let old = self.props.insert(k, v);

            if let Some(old) = old {
                self.errors.push(Error::RepeatedDisplayOption {
                    error_span,
                    first_span: old.0,
                    option,
                });
            }
        }

        // no finish(), because that would require CompileContext. Here, however, no errors would happen anyway.
        other.finished = true;

        self
    }

    /// Ignore all unread properties.
    fn ignore_all(&mut self) {
        self.props.clear();
    }
}

impl From<Option<DisplayProperties>> for Properties {
    fn from(value: Option<DisplayProperties>) -> Self {
        Self {
            props: value
                .into_iter()
                .flat_map(|x| x.properties.into_parsed_iter())
                .map(|v| (v.name.ident.clone(), (v.name.span, v.value.clone())))
                .collect(),
            finished: false,
            errors: Vec::new(),
            expected: Vec::new(),
        }
    }
}

impl Drop for Properties {
    fn drop(&mut self) {
        if !self.finished {
            eprintln!(
                "Properties dropped before finishing parsing: {:#?}. Please report this error.",
                self.props
            );
        }
    }
}

/// A single property with an optional value and an optional span.
#[derive(Debug, Clone)]
pub struct Property<T> {
    value: Option<T>,
    span: Option<Span>,
}

impl<T> Property<T> {
    /// Get the property's value, consuming it.
    #[must_use]
    pub fn get(self) -> Option<T> {
        self.value
    }

    /// Get the property's value or a default if the value is not present.
    #[must_use]
    pub fn get_or(self, default: T) -> T {
        self.value.unwrap_or(default)
    }

    /// Get the property's span if it exists.
    #[must_use]
    pub fn get_span(&self) -> Option<Span> {
        self.span
    }

    /// Make this property into a [`MaybeUnset`]
    #[must_use]
    pub fn maybe_unset(self, default: T) -> MaybeUnset<T> {
        let mut value = MaybeUnset::new(default);
        value.try_set(self.get());

        value
    }
}

impl<T> Property<Result<T, Error>> {
    /// Get the value or, in case of an error, a default alternative.
    #[must_use]
    pub fn ok_or(self, default: T) -> T {
        self.value.and_then(Result::ok).unwrap_or(default)
    }
}

/// Create a named variable from the unrolled expression in a `let` statement.
fn create_variable_named(
    stat: &LetStatement,
    context: &mut CompileContext,
    named: &NamedIdent,
    mut rhs_unrolled: AnyExpr,
    variable_nodes: &mut Vec<Box<dyn Node>>,
) -> Result<(), Error> {
    let convert = if let AnyExpr::PointCollection(pc) = &mut rhs_unrolled {
        if pc.data.length == 1 {
            true
        } else {
            if let Some(node) = &mut pc.node {
                if let Some(mut props) = node.root.props.take() {
                    let _ = props.get::<Result<SpannedMathString, Error>>("default-label");
                    props.finish(context);
                }
            }

            // Point collection variables are ambiguous and therefore cause compilation errors.
            // They do not, however prevent the program from running properly.
            context.push_error(Error::InvalidPC {
                error_span: stat.get_span(),
            });
            false
        }
    } else {
        false
    };

    if convert {
        rhs_unrolled = rhs_unrolled.convert_to(Type::Point, context);
    }

    match context.variables.entry(named.ident.clone()) {
        // If the variable already exists, it's a redefinition error.
        Entry::Occupied(entry) => Err(Error::RedefinedVariable {
            defined_at: entry.get().get_variable_span(),
            error_span: stat.get_span(),
            variable_name: entry.key().clone(),
        }),
        // Otherwise, create a new variable
        Entry::Vacant(entry) => {
            variable_nodes.extend(rhs_unrolled.replace_node(None).map(AnyExprNode::to_dyn));

            let var = rhs_unrolled.make_variable(entry.key().clone());
            entry.insert(var);

            Ok(())
        }
    }
}

/// Create a point collection variable based from an unrolled expression in a `let` statement.
/// If the `lhs` of let statement is a point collection, the `rhs` has to be unpacked.
fn create_variable_collection(
    stat: &LetStatement,
    context: &mut CompileContext,
    col: &PCToken,
    rhs_unrolled: AnyExpr,
    variable_nodes: &mut Vec<Box<dyn Node>>,
) -> Result<(), Error> {
    // let display = Properties::from(display);

    let maybe_error = Error::CannotUnpack {
        error_span: rhs_unrolled.get_span(),
        ty: rhs_unrolled.get_type(),
    };
    let mut rhs_unpacked = rhs_unrolled.convert::<PointCollection>(context);

    if rhs_unpacked.data.length != col.len()
        && !matches!(
            rhs_unpacked.data.data,
            PointCollectionData::Generic(Generic::Dummy)
        )
    {
        return Err(maybe_error);
    }

    // let pt_node = if col.collection.len() == 1 {
    //     Some(FigureNode::new_point(
    //         rhs_unpacked.index(0),
    //         display,
    //         IdentOrItem::PointCollectionItem(col.collection[0].clone())
    //     )?)
    // } else {
    //     None
    // };

    let mut rhs_node = rhs_unpacked.take_node();
    let mut rhs_unpacked: Box<dyn Iterator<Item = Expr<Point>>> =
        match &rhs_unpacked.data.get_data().data {
            PointCollectionData::PointCollection(collection) => {
                Box::new(collection.clone_without_node().0.into_iter())
                    as Box<dyn Iterator<Item = Expr<Point>>>
            }
            PointCollectionData::Generic(Generic::Dummy) => {
                Box::new(std::iter::repeat_with(|| Expr {
                    data: Rc::new(Point::dummy()),
                    span: rhs_unpacked.span,
                    node: None,
                }))
            }
            PointCollectionData::Generic(_) => unreachable!(),
        };

    for (i, pt) in col.collection.iter().enumerate() {
        let id = format!("{pt}");

        match context.variables.entry(id.clone()) {
            // If the variable already exists, it's a redefinition error.
            Entry::Occupied(entry) => {
                return Err(Error::RedefinedVariable {
                    defined_at: entry.get().get_variable_span(),
                    error_span: stat.get_span(),
                    variable_name: id,
                })
            }
            // Otherwise, create a new variable
            Entry::Vacant(entry) => {
                let var = rhs_unpacked.next().unwrap();

                if let Some(rhs_node) = &mut rhs_node {
                    let pt_node = rhs_node.root.children.get_mut(i).and_then(Option::take);

                    variable_nodes.extend(pt_node.map(|x| Box::new(x) as Box<dyn Node>));
                }

                let var = var.make_variable(entry.key().clone());

                let var = AnyExpr::Point(var);
                entry.insert(var);
            }
        }
    }

    Ok(())
}

/// Create variables from a `let` statement.
fn create_variables(
    stat: &LetStatement,
    context: &mut CompileContext,
    library: &Library,
) -> Result<Vec<Box<dyn Node>>, Error> {
    let mut variable_nodes = Vec::new();

    let tree = IterNode::from(&stat.expr);

    let ind = if let Some(iter) = tree.first() {
        if stat.ident.len() == 1 {
            context.push_error(Error::LetStatUnexpectedIterator {
                var_span: stat.ident.get_span(),
                error_span: iter.span,
            });

            // Ignore every but first entry in the iterator.
        }

        for it in tree.iter() {
            if iter.id != it.id {
                context.push_error(Error::LetStatMoreThanOneIterator {
                    error_span: stat.expr.get_span(),
                    first_span: iter.span,
                    second_span: it.span,
                });

                // Ignore every other iterator.
            }

            for variant in &it.variants {
                if let Some(it2) = variant.first() {
                    context.push_error(Error::LetStatMoreThanOneIterator {
                        error_span: stat.expr.get_span(),
                        first_span: iter.span,
                        second_span: it2.span,
                    });

                    // Ignore every other iterator.
                }
            }
        }

        let mut lengths = HashMap::new();
        tree.get_iter_lengths(&mut lengths, stat.expr.get_span())?;
        let entry = lengths.get(&iter.id).unwrap();

        if entry.0 != stat.ident.len() {
            return Err(Error::InconsistentIterators {
                first_span: stat.ident.get_span(),
                first_length: stat.ident.len(),
                occurred_span: entry.1,
                occurred_length: entry.0,
                error_span: stat.get_span(),
            });
        }

        None
    } else {
        Some(HashMap::new())
    };

    let mut it_index = IterTreeIterator::new(&tree);

    // Iterate over each identifier.
    for def in stat.ident.iter() {
        let mut external = Properties::default();
        external.props.insert(
            String::from("default-label"),
            (Span::empty(), PropertyValue::Ident(def.name.clone())),
        );

        let display = Properties::from(def.display_properties.clone()).merge_with(external);

        let rhs_unrolled = stat.expr.unroll(
            context,
            library,
            ind.as_ref()
                .unwrap_or_else(|| it_index.get_currents().unwrap()),
            display,
        );
        it_index.next();

        // println!("let {} = {rhs_unrolled}", def.name);

        match &def.name {
            Ident::Named(named) => {
                create_variable_named(stat, context, named, rhs_unrolled, &mut variable_nodes)?;
            }
            Ident::Collection(col) => {
                create_variable_collection(stat, context, col, rhs_unrolled, &mut variable_nodes)?;
            }
        }
    }

    Ok(variable_nodes)
}

/// Unroll a ref statement.
fn unroll_ref(
    stat: &RefStatement,
    context: &mut CompileContext,
    library: &Library,
) -> Result<Vec<Box<dyn Node>>, Error> {
    let mut nodes = Vec::new();
    let tree = IterNode::from(&stat.operand);

    // Check the lengths
    tree.get_iter_lengths(&mut HashMap::new(), stat.get_span())?;

    // And create the index
    let mut index = IterTreeIterator::new(&tree);

    while let Some(it_index) = index.get_currents() {
        let mut display = Properties::from(stat.display.clone());
        let weight = display.get("weight").get_or(ProcNum::zero());

        let mut expr = stat.operand.unroll(context, library, it_index, display);

        if let AnyExpr::PointCollection(pc) = &mut expr {
            if let Some(node) = pc.node.take() {
                if let Some(props) = node.root.props {
                    props.finish(context);
                }
            }

            context.push_error(Error::InvalidPC {
                error_span: expr.get_span(),
            });
        }

        let node = expr.replace_node(None).map(AnyExprNode::to_dyn);
        nodes.extend(node);

        // If any weight is given, add a bias
        if !weight.is_zero() {
            context.push_rule(UnrolledRule {
                kind: UnrolledRuleKind::Bias(expr),
                inverted: false,
                weight,
            });
        }

        index.next();
    }

    Ok(nodes)
}

/// Unroll a `let` statement.
fn unroll_let(
    mut stat: LetStatement,
    context: &mut CompileContext,
    library: &Library,
) -> Result<Vec<Box<dyn Node>>, Error> {
    // First, we construct an iterator out of lhs
    let lhs: Expression<true> = Expression::ImplicitIterator(ImplicitIterator {
        exprs: Punctuated {
            first: Box::new(SimpleExpression {
                minus: None,
                kind: SimpleExpressionKind::Name(Name::Ident(stat.ident.first.name.clone())),
                exponent: None,
                display: None,
            }),
            collection: stat
                .ident
                .collection
                .iter()
                .map(|(p, i)| {
                    (
                        *p,
                        SimpleExpression {
                            minus: None,
                            kind: SimpleExpressionKind::Name(Name::Ident(i.name.clone())),
                            exponent: None,
                            display: None,
                        },
                    )
                })
                .collect(),
        },
    });

    let stat_span = stat.get_span();
    let rules = mem::take(&mut stat.rules);

    let mut nodes = create_variables(&stat, context, library)?;

    // Then, we run each rule through a tree iterator.
    for (rule, expr) in rules {
        let tree = IterNode::from2(&lhs, &expr);

        // Check the lengths
        tree.get_iter_lengths(&mut HashMap::new(), stat_span)?;

        // And create the index
        let mut index = IterTreeIterator::new(&tree);

        while let Some(it_index) = index.get_currents() {
            nodes.push(unroll_rule(
                (
                    lhs.unroll(context, library, it_index, Properties::default()),
                    &rule,
                    expr.unroll(context, library, it_index, Properties::default()),
                ),
                context,
                library,
                stat_span,
                false,
                Properties::from(None),
            ));

            index.next();
        }
    }

    Ok(nodes)
}

/// Unroll an equality rule.
fn unroll_eq(
    lhs: AnyExpr,
    rhs: AnyExpr,
    context: &mut CompileContext,
    full_span: Span,
    inverted: bool,
    display: Properties,
) -> Box<dyn Node> {
    let lhs_type = lhs.get_type();
    let rhs_type = rhs.get_type();

    if (lhs_type == ty::collection(2) && rhs_type == ty::collection(2))
        || (lhs_type == ty::collection(2) && rhs_type == ty::SCALAR_UNKNOWN)
        || (lhs_type == ty::SCALAR_UNKNOWN && rhs_type == ty::collection(2))
    {
        // AB = CD must have different logic as it's implied that this means "equality of distances".
        let lhs = lhs
            .convert(context)
            .convert_unit(Some(unit::DISTANCE), context);
        let rhs = rhs
            .convert(context)
            .convert_unit(Some(unit::DISTANCE), context);
        context.scalar_eq_display(lhs, rhs, inverted, display)
    } else if lhs_type == ty::collection(1) && rhs_type == ty::collection(1) {
        let lhs = lhs.convert(context);
        let rhs = rhs.convert(context);

        context.point_eq_display(lhs, rhs, inverted, display)
    } else {
        // If any of the two types can be cast onto the other, cast and compare.
        let (lhs, rhs, new_type) = if rhs.can_convert_to(lhs_type) {
            (lhs, rhs.convert_to(lhs_type, context), lhs_type)
        } else if lhs.can_convert_to(rhs_type) {
            (lhs.convert_to(rhs_type, context), rhs, rhs_type)
        } else {
            context.push_error(Error::InconsistentTypes {
                expected: (lhs_type, Box::new(lhs.get_span())),
                got: (rhs_type, Box::new(rhs.get_span())),
                error_span: Box::new(full_span),
            });

            // "Cast" rhs to lhs.
            (
                lhs,
                AnyExpr::Unknown(Expr {
                    span: rhs.get_span(),
                    data: Rc::new(Unknown::dummy()),
                    node: None,
                })
                .convert_to(lhs_type, context),
                lhs_type,
            )
        };

        match new_type {
            Type::Point => {
                let lhs = lhs.convert(context);
                let rhs = rhs.convert(context);

                context.point_eq_display(lhs, rhs, inverted, display)
            }
            Type::Scalar(_) => {
                let lhs = lhs.convert(context);
                let rhs = rhs.convert(context);

                context.scalar_eq_display(lhs, rhs, inverted, display)
            }
            ty => {
                context.push_error(Error::ComparisonDoesNotExist {
                    error_span: full_span,
                    ty,
                });

                // Pretend there is no rule.
                context.scalar_eq_display(
                    Expr::new_spanless(Scalar::dummy()),
                    Expr::new_spanless(Scalar::dummy()),
                    inverted,
                    display,
                )
            }
        }
    }
}

/// Unroll a greater-than rule.
fn unroll_gt(
    lhs: Expr<Scalar>,
    rhs: Expr<Scalar>,
    context: &mut CompileContext,
    full_span: Span,
    inverted: bool,
    display: Properties,
) -> Box<dyn Node> {
    if lhs.data.unit.is_some() {
        let rhs = if rhs.can_convert_unit(lhs.data.unit) {
            rhs.convert_unit(lhs.data.unit, context)
        } else {
            context.push_error(Error::InconsistentTypes {
                expected: (lhs.get_value_type(), Box::new(lhs.span)),
                got: (rhs.get_value_type(), Box::new(rhs.span)),
                error_span: Box::new(full_span),
            });

            Expr {
                span: rhs.span,
                node: rhs.node,
                data: Rc::new(Scalar::dummy()),
            }
            .convert_unit(lhs.data.unit, context)
        };

        context.gt_display(lhs, rhs, inverted, display)
    } else if rhs.data.unit.is_some() {
        let lhs = lhs.convert_unit(rhs.data.unit, context);
        context.gt_display(lhs, rhs, inverted, display)
    } else {
        let lhs = lhs.convert_unit(Some(unit::SCALAR), context);
        let rhs = rhs.convert_unit(Some(unit::SCALAR), context);
        context.gt_display(lhs, rhs, inverted, display)
    }
}

/// Unroll a generic rule.
fn unroll_rule(
    (lhs, op, rhs): (AnyExpr, &RuleOperator, AnyExpr),
    context: &mut CompileContext,
    library: &Library,
    full_span: Span,
    inverted: bool,
    mut display: Properties,
) -> Box<dyn Node> {
    match op {
        RuleOperator::Predefined(pre) => match pre {
            PredefinedRuleOperator::Eq(_) => {
                unroll_eq(lhs, rhs, context, full_span, inverted, display)
            }
            PredefinedRuleOperator::Lt(_) => unroll_gt(
                rhs.convert(context),
                lhs.convert(context),
                context,
                full_span,
                inverted,
                display,
            ),
            PredefinedRuleOperator::Gt(_) => unroll_gt(
                lhs.convert(context),
                rhs.convert(context),
                context,
                full_span,
                inverted,
                display,
            ),
            PredefinedRuleOperator::Lteq(_) => unroll_gt(
                lhs.convert(context),
                rhs.convert(context),
                context,
                full_span,
                !inverted,
                display,
            ),
            PredefinedRuleOperator::Gteq(_) => unroll_gt(
                rhs.convert(context),
                lhs.convert(context),
                context,
                full_span,
                !inverted,
                display,
            ),
        },
        RuleOperator::Defined(op) => {
            let weight = display.get("weight").get_or(ProcNum::one());

            let overload = match library.get_rule(op.ident.as_str()) {
                Ok(func) => {
                    if let Some(overload) = func.get_overload(&lhs, &rhs) {
                        overload
                    } else {
                        context.push_error(Error::OverloadNotFound {
                            error_span: op.span,
                            function_name: op.ident.clone(),
                            params: vec![lhs.get_type(), rhs.get_type()],
                        });

                        // Pretend the rule doesn't exist.
                        display.finish(context);
                        return Box::new(EmptyNode);
                    }
                }
                Err(suggested) => {
                    context.push_error(Error::UndefinedFunction {
                        error_span: op.span,
                        function_name: op.ident.clone(),
                        suggested,
                    });

                    // Pretend the rule doesn't exist.
                    display.finish(context);
                    return Box::new(EmptyNode);
                }
            };

            overload.unroll(lhs, rhs, context, display, inverted, weight)
        }
        RuleOperator::Inverted(op) => unroll_rule(
            (lhs, &op.operator, rhs),
            context,
            library,
            full_span,
            !inverted,
            display,
        ),
    }
}

/// Unroll a general rule statement.
fn unroll_rule_statement(
    rule: &RuleStatement,
    context: &mut CompileContext,
    library: &Library,
) -> Result<Vec<Box<dyn Node>>, Error> {
    let mut nodes = Vec::new();

    let tree = IterNode::from2(&rule.lhs, &rule.rhs);
    tree.get_iter_lengths(&mut HashMap::new(), rule.get_span())?;

    let mut it_index = IterTreeIterator::new(&tree);

    while let Some(index) = it_index.get_currents() {
        nodes.push(unroll_rule(
            (
                rule.lhs
                    .unroll(context, library, index, Properties::default()),
                &rule.op,
                rule.rhs
                    .unroll(context, library, index, Properties::default()),
            ),
            context,
            library,
            rule.get_span(),
            false,
            Properties::from(rule.display.clone()),
        ));

        it_index.next();
    }

    Ok(nodes)
}

/// Unrolls the given script. All iterators are expanded and all conversions applied. The output can be immediately compiled.
///
/// # Errors
/// Specific error descriptions are in `ScriptError` documentation.
pub fn unroll(input: &str) -> Result<(CompileContext, CollectionNode), Vec<Error>> {
    // Unfortunately, due to how context-dependent geoscript is, the code must be compiled immediately after parsing.
    let mut context = CompileContext::new();
    let library = Library::new();

    let mut figure = CollectionNode::new();

    let tokens = match token::tokenize(input) {
        Ok(v) => v,
        Err(err) => return Err(vec![err]),
    };
    let mut input = InputStream::new(&tokens);

    let mut statements = Vec::new();

    while !input.eof() {
        statements.push(match input.parse() {
            Ok(v) => v,
            Err(err) => return Err(vec![err]),
        });
    }

    let mut flags = FlagSetConstructor::new()
        .add_set(&"optimizations", FlagSetConstructor::new())
        .add_bool_def(&"point_inequalities", true)
        .finish();

    for flag in statements.iter().filter_map(Statement::as_flag) {
        flags::set_flag(&mut flags, flag, &context);
    }

    context.flags = flags;

    for stat in statements {
        // Unroll the statement
        match stat {
            Statement::Noop(_) | Statement::Flag(_) => (),
            Statement::Let(stat) => match unroll_let(stat, &mut context, &library) {
                Ok(nodes) => {
                    for node in nodes {
                        figure.push_boxed(node);
                    }
                }
                Err(err) => context.push_error(err),
            },
            Statement::Rule(stat) => match unroll_rule_statement(&stat, &mut context, &library) {
                Ok(nodes) => {
                    for node in nodes {
                        figure.push_boxed(node);
                    }
                }
                Err(err) => context.push_error(err),
            },
            Statement::Ref(stat) => match unroll_ref(&stat, &mut context, &library) {
                Ok(nodes) => {
                    for node in nodes {
                        figure.push_boxed(node);
                    }
                }
                Err(err) => context.push_error(err),
            },
        }
    }

    // for x in context.rules.borrow().iter() {
    //     println!("{x}");
    // }

    if context.valid() {
        Ok((context, figure))
    } else {
        Err(context.take_errors())
    }
}
