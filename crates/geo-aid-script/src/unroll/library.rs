//! `GeoScript`'s builtin functions and types

use std::{
    collections::{HashMap, HashSet},
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
};

use num_rational::Ratio;

use crate::{
    parser::Type,
    token::number::ProcNum,
    unit,
    unroll::{AnyExpr, Expr, GeoType, PointCollection, Scalar},
    ComplexUnit,
};

use super::{
    context::CompileContext, figure::Node, most_similar, Convert, ConvertFrom, Properties,
};

pub mod angle;
pub mod bisector;
pub mod circle;
pub mod degrees;
pub mod dst;
pub mod intersection;
pub mod lies_on;
pub mod line;
pub mod mid;
pub mod parallel;
pub mod perpendicular;
pub mod point;
pub mod radians;
pub mod segment;

/// A prelude for builtin functions.
pub mod prelude {
    pub(crate) use crate::{
        unit,
        unroll::{
            context::CompileContext,
            figure::{
                BuildAssociated, BundleNode, CollectionNode, HierarchyNode, LineNode, LineType,
                PointNode, ScalarNode,
            },
            library::{macros::*, Angle, Distance, Function, Library, Pc, Rule, Unitless},
            Bundle, Circle, CloneWithNode, Expr, GeoType, Line, Point, Properties, ScalarData,
            UnrolledRule, UnrolledRuleKind,
        },
    };
    pub(crate) use geo_aid_figure::Style;
}
/// A `GeoScript` function.
pub struct Function {
    /// Name of this function.
    pub name: &'static str,
    /// Function's overloads.
    pub overloads: Vec<Box<dyn Overload>>,
    /// Aliases of this function
    pub aliases: Vec<&'static str>,
    /// Method aliases of this function
    pub method_aliases: Vec<(Type, &'static str)>,
}

impl Function {
    /// Create a new function with the given name. The name MUST be ascii and lowercase
    #[must_use]
    pub fn new(name: &'static str) -> Self {
        if name
            .chars()
            .any(|c| !c.is_ascii() || !c.is_lowercase() && c.is_alphabetic())
        {
            panic!("Function name must be ASCII and lowercase. Received name: {name}");
        }

        Self {
            name,
            overloads: Vec::new(),
            aliases: Vec::new(),
            method_aliases: Vec::new()
        }
    }

    /// Create an alias for this function
    #[must_use]
    pub fn alias(mut self, name: &'static str) -> Self {
        if name
            .chars()
            .any(|c| !c.is_ascii() || !c.is_lowercase() && c.is_alphabetic())
        {
            panic!("Function name must be ASCII and lowercase. Received name: {name}");
        }

        self.aliases.push(name);
        self
    }

    /// Create an alias for this function
    #[must_use]
    pub fn alias_method(mut self, self_type: Type, name: &'static str) -> Self {
        if name
            .chars()
            .any(|c| !c.is_ascii() || !c.is_lowercase() && c.is_alphabetic())
        {
            panic!("Function name must be ASCII and lowercase. Received name: {name}");
        }

        self.method_aliases.push((self_type, name));
        self
    }

    /// Add a new overload to this function.
    #[must_use]
    pub fn overload<Marker>(mut self, f: impl IntoOverload<Marker>) -> Self {
        self.overloads.push(Box::new(f.into_overload()));
        self
    }

    /// Tries to find an overload for the given param types.
    #[must_use]
    pub fn get_overload(&self, params: &[AnyExpr]) -> Option<&dyn Overload> {
        self.overloads
            .iter()
            .map(AsRef::as_ref)
            .find(|x| x.get_returned_type(params).is_some())
    }
}

/// Trait for function overloads
pub trait Overload {
    /// Get the return type for the given parameters. Returns `None` if the overload
    /// cannot be called with these parameters.
    #[must_use]
    fn get_returned_type(&self, params: &[AnyExpr]) -> Option<Type>;

    /// Unroll the function for the given params. The resulting expression
    /// matches the type returned by `get_returned_type`.
    #[must_use]
    fn unroll(
        &self,
        params: Vec<AnyExpr>,
        context: &mut CompileContext,
        props: Properties,
    ) -> AnyExpr;
}

/// An overload of a function in `GeoScript`.
#[derive(Debug)]
pub struct FunctionOverload<F, A, R, C>(F, PhantomData<(A, R, C)>);

macro_rules! tuple_size {
    () => {
        0
    };
    ($first:ident $(, $arg:ident)*) => {
        1 + tuple_size!($($arg),*)
    }
}

macro_rules! impl_overload_function {
    ($($arg:ident),* $(,)?) => {
        impl<$($arg,)* R, F> Overload for FunctionOverload<F, ($($arg,)*), R, &mut CompileContext>
        where
            $($arg: GeoType + 'static,)*
            R: GeoType + Into<AnyExpr> + 'static,
            F: Fn($($arg,)* &mut CompileContext, Properties) -> R
        {
            fn get_returned_type(&self, params: &[AnyExpr]) -> Option<Type> {
                let types = [$($arg::get_type()),*];
                if params.len() == tuple_size!($($arg),*)
                    && params
                    .iter()
                    .map(|p| p.get_type())
                    .zip(types)
                    .all(|(a, b)| a.can_cast(&b)) {
                    Some(R::get_type())
                } else {
                    None
                }
            }

            fn unroll(&self, params: Vec<AnyExpr>, context: &mut CompileContext, props: Properties) -> AnyExpr {
                #[allow(unused_mut, unused_variables)]
                let mut param = params.into_iter();
                (self.0)(
                    $($arg::Target::convert_from(param.next().unwrap(), context).into(),)*
                    context, props
                ).into()
            }
        }

        impl<$($arg,)* R, F> Overload for FunctionOverload<F, ($($arg,)*), R, &CompileContext>
        where
            $($arg: GeoType + 'static,)*
            R: GeoType + Into<AnyExpr> + 'static,
            F: Fn($($arg,)* &CompileContext, Properties) -> R
        {
            fn get_returned_type(&self, params: &[AnyExpr]) -> Option<Type> {
                let types = [$($arg::get_type()),*];
                if params.len() == tuple_size!($($arg),*)
                    && params
                    .iter()
                    .map(|p| p.get_type())
                    .zip(types)
                    .all(|(a, b)| a.can_cast(&b)) {
                    Some(R::get_type())
                } else {
                    None
                }
            }

            fn unroll(&self, params: Vec<AnyExpr>, context: &mut CompileContext, props: Properties) -> AnyExpr {
                #[allow(unused_mut, unused_variables)]
                let mut param = params.into_iter();
                (self.0)(
                    $($arg::Target::convert_from(param.next().unwrap().convert_to($arg::get_type(), context), context).into(),)*
                    context, props
                ).into()
            }
        }
    };
}

/// Helper trait for overloading a function. Features a special marker for
/// managing possible different implementations on the same type.
pub trait IntoOverload<Marker>: Sized {
    /// Target overload type
    type Target: Overload + 'static;

    /// Turn this into a function overload.
    fn into_overload(self) -> Self::Target;
}

impl<T: Overload + 'static> IntoOverload<T> for T {
    type Target = T;

    fn into_overload(self) -> Self::Target {
        self
    }
}

macro_rules! impl_into_overload {
    ($($arg:ident),* $(,)?) => {
        impl<$($arg,)* R, F> IntoOverload<(F, ($($arg,)*), R, &mut CompileContext)> for F
        where
            $($arg: GeoType + 'static,)*
            R: GeoType + Into<AnyExpr> + 'static,
            F: Fn($($arg,)* &mut CompileContext, Properties) -> R + 'static
        {
            type Target = FunctionOverload<F, ($($arg,)*), R, &'static mut CompileContext>;

            fn into_overload(self) -> Self::Target {
                FunctionOverload(self, PhantomData)
            }
        }

        impl<$($arg,)* R, F> IntoOverload<(F, ($($arg,)*), R, &CompileContext)> for F
        where
            $($arg: GeoType + 'static,)*
            R: GeoType + Into<AnyExpr> + 'static,
            F: Fn($($arg,)* &CompileContext, Properties) -> R + 'static
        {
            type Target = FunctionOverload<F, ($($arg,)*), R, &'static CompileContext>;

            fn into_overload(self) -> Self::Target {
                FunctionOverload(self, PhantomData)
            }
        }

        impl_overload_function! {$($arg),*}
    };
}

impl_into_overload! {}
impl_into_overload! {T0}
impl_into_overload! {T0, T1}
impl_into_overload! {T0, T1, T2}
impl_into_overload! {T0, T1, T2, T3}

/// A rule operator.
pub struct Rule {
    /// Rule's name
    pub name: &'static str,
    /// Rule's overloads.
    pub overloads: Vec<Box<dyn RuleOverload>>,
    /// Aliases this rule has.
    pub aliases: Vec<&'static str>,
}

impl Rule {
    /// Create a new rule with no overloads. The name must be ascii and all lowercase.
    #[must_use]
    pub fn new(name: &'static str) -> Self {
        if name
            .chars()
            .any(|c| !c.is_ascii() || !c.is_lowercase() && c.is_alphabetic())
        {
            panic!("Function name must be ASCII and lowercase. Received name: {name}");
        }

        Self {
            name,
            overloads: Vec::new(),
            aliases: Vec::new(),
        }
    }

    /// Create an alias for this rule
    #[must_use]
    pub fn alias(mut self, name: &'static str) -> Self {
        if name
            .chars()
            .any(|c| !c.is_ascii() || !c.is_lowercase() && c.is_alphabetic())
        {
            panic!("Rule name must be ASCII and lowercase. Received name: {name}");
        }

        self.aliases.push(name);
        self
    }

    /// Add an overload to this rule
    #[must_use]
    pub fn overload<M>(mut self, f: impl IntoRuleOverload<M>) -> Self {
        self.overloads.push(Box::new(f.into_overload()));
        self
    }

    /// Tries to find an overload for the given param types.
    #[must_use]
    pub fn get_overload(&self, lhs: &AnyExpr, rhs: &AnyExpr) -> Option<&dyn RuleOverload> {
        self.overloads
            .iter()
            .map(AsRef::as_ref)
            .find(|x| x.matches(lhs, rhs))
    }
}

/// Trait for rule overloads
pub trait RuleOverload {
    /// Check if this overload can be called with the given expressions.
    #[must_use]
    fn matches(&self, lhs: &AnyExpr, rhs: &AnyExpr) -> bool;

    /// Unroll this rule.
    #[must_use]
    fn unroll(
        &self,
        lhs: AnyExpr,
        rhs: AnyExpr,
        context: &mut CompileContext,
        props: Properties,
        inverted: bool,
        weight: ProcNum,
    ) -> Box<dyn Node>;
}

/// Trait for things convertible into rule overloads
pub trait IntoRuleOverload<Marker> {
    type Target: RuleOverload + 'static;

    fn into_overload(self) -> Self::Target;
}

impl<T: RuleOverload + 'static> IntoRuleOverload<T> for T {
    type Target = Self;

    fn into_overload(self) -> Self::Target {
        self
    }
}

impl<
        L: GeoType + 'static,
        R: GeoType + 'static,
        N: Node + 'static,
        F: Fn(L, R, &mut CompileContext, Properties, bool, ProcNum) -> N + 'static,
    > IntoRuleOverload<(L, R, F)> for F
{
    type Target = FunctionRuleOverload<L, R, F>;

    fn into_overload(self) -> Self::Target {
        FunctionRuleOverload(self, PhantomData)
    }
}

/// A rule overload made from a function.
pub struct FunctionRuleOverload<L, R, F>(F, PhantomData<(L, R)>);

impl<
        L: GeoType,
        R: GeoType,
        N: Node + 'static,
        F: Fn(L, R, &mut CompileContext, Properties, bool, ProcNum) -> N,
    > RuleOverload for FunctionRuleOverload<L, R, F>
{
    fn matches(&self, lhs: &AnyExpr, rhs: &AnyExpr) -> bool {
        lhs.can_convert_to(L::get_type()) && rhs.can_convert_to(R::get_type())
    }

    fn unroll(
        &self,
        lhs: AnyExpr,
        rhs: AnyExpr,
        context: &mut CompileContext,
        props: Properties,
        inverted: bool,
        weight: ProcNum,
    ) -> Box<dyn Node> {
        Box::new((self.0)(
            L::from(lhs.convert(context)),
            R::from(rhs.convert(context)),
            context,
            props,
            inverted,
            weight,
        ))
    }
}

/// A direct definition or an alias
pub enum Definition<T> {
    /// A direct function definition
    Direct(T),
    Alias(&'static str),
}

/// The library of all rules and functions available in geoscript.
#[derive(Default)]
pub struct Library {
    /// Functions
    functions: HashMap<&'static str, Definition<Function>>,
    /// Methods. Note that methods can only be aliased to functions, never to methods or the other way around.
    methods: HashMap<Type, HashMap<&'static str, Definition<Function>>>,
    /// The rule operators.
    rule_ops: HashMap<&'static str, Definition<Rule>>,
    /// Bundle types.
    bundles: HashMap<&'static str, HashSet<&'static str>>,
}

impl Library {
    /// Create a new empty library.
    #[must_use]
    pub fn new() -> Self {
        let mut library = Self {
            functions: HashMap::new(),
            methods: HashMap::new(),
            rule_ops: HashMap::new(),
            bundles: HashMap::new(),
        };

        point::register(&mut library); // Point()
        dst::register(&mut library); // dst()
        angle::register(&mut library); // angle()
        degrees::register(&mut library); // degrees()
        radians::register(&mut library); // radians()
        mid::register(&mut library); // mid()
        perpendicular::register(&mut library); // perpendicular_through()
        parallel::register(&mut library); // parallel_through()
        intersection::register(&mut library); // intersection()
        bisector::register(&mut library); // bisector()
        circle::register(&mut library); // Circle()
        segment::register(&mut library); // Segment()
        line::register(&mut library); // Line()

        lies_on::register(&mut library); // lies_on

        library
    }

    /// Get the bundle by its name.
    #[must_use]
    pub fn get_bundle(&self, name: &str) -> &HashSet<&'static str> {
        &self.bundles[name]
    }

    /// Add a definition
    pub fn add<T: Addable>(&mut self, def: T) -> &mut Self {
        def.add_to(self);
        self
    }

    /// Get the function by its name. If the function doesn't exist,
    /// return the most similar name if one exists. The search is case-insensitive.
    pub fn get_function(&self, name: &str) -> Result<&Function, Option<&'static str>> {
        self.functions
            .get(name.to_lowercase().as_str())
            .ok_or_else(|| most_similar(self.functions.keys().copied(), name))
            .and_then(|f| match f {
                Definition::Direct(f) => Ok(f),
                Definition::Alias(n) => self.get_function(n),
            })
    }

    /// Get the method by its name and self type. If the method doesn't exist,
    /// return the most similar name if one exists. The search is case-insensitive.
    pub fn get_method(&self, self_type: Type, name: &str) -> Result<&Function, Option<&'static str>> {
        let methods = self.methods
        .get(&self_type).or_else(|| {
            if matches!(self_type, Type::PointCollection(_)) {
                self.methods.get(&Type::PointCollection(0))
            } else {
                None
            }
        }).ok_or(None)?;

        methods
            .get(name.to_lowercase().as_str())
            .ok_or_else(|| most_similar(methods.keys().copied(), name))
            .and_then(|f| match f {
                Definition::Direct(f) => Ok(f),
                Definition::Alias(n) => self.get_function(n),
            })
    }

    /// Get the rule operator by its name. If the rule doesn't exist,
    /// return the most similar name if one exists. The search is case-insensitive.
    pub fn get_rule(&self, name: &str) -> Result<&Rule, Option<&'static str>> {
        self.rule_ops
            .get(name.to_lowercase().as_str())
            .ok_or_else(|| most_similar(self.rule_ops.keys().copied(), name))
            .and_then(|f| match f {
                Definition::Direct(f) => Ok(f),
                Definition::Alias(n) => self.get_rule(n),
            })
    }
}

/// Trait for adding a definition to the library.
pub trait Addable {
    fn add_to(self, library: &mut Library);
}

impl Addable for Function {
    fn add_to(mut self, library: &mut Library) {
        for alias in mem::take(&mut self.aliases) {
            library
                .functions
                .insert(alias, Definition::Alias(self.name));
        }

        for (t, alias) in mem::take(&mut self.method_aliases) {
            library.methods.entry(t).or_default().insert(alias, Definition::Alias(self.name));
        }

        library
            .functions
            .insert(self.name, Definition::Direct(self));
    }
}

impl Addable for Rule {
    fn add_to(mut self, library: &mut Library) {
        for alias in mem::take(&mut self.aliases) {
            library.rule_ops.insert(alias, Definition::Alias(self.name));
        }

        library.rule_ops.insert(self.name, Definition::Direct(self));
    }
}

/// Point collection with a specific size
pub struct Pc<const N: usize>(pub Expr<PointCollection>);

impl<const N: usize> GeoType for Pc<N> {
    type Target = PointCollection;

    fn get_type() -> Type {
        Type::PointCollection(N)
    }
}

impl<const N: usize> From<Expr<PointCollection>> for Pc<N> {
    fn from(value: Expr<PointCollection>) -> Self {
        assert!(value.data.length == N || N == 0);
        Self(value)
    }
}

impl<const N: usize> Deref for Pc<N> {
    type Target = Expr<PointCollection>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const N: usize> DerefMut for Pc<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Scalar with a specific unit.
pub struct ScalarUnit<
    const DST_NUM: i64,
    const DST_DENOM: i64,
    const ANG_NUM: i64,
    const ANG_DENOM: i64,
>(pub Expr<Scalar>);

impl<const DST_NUM: i64, const DST_DENOM: i64, const ANG_NUM: i64, const ANG_DENOM: i64>
    ScalarUnit<DST_NUM, DST_DENOM, ANG_NUM, ANG_DENOM>
{
    #[must_use]
    pub fn get_unit() -> ComplexUnit {
        unit::DISTANCE.pow(Ratio::new(DST_NUM, DST_DENOM))
            * &unit::ANGLE.pow(Ratio::new(ANG_NUM, ANG_DENOM))
    }
}

impl<const DST_NUM: i64, const DST_DENOM: i64, const ANG_NUM: i64, const ANG_DENOM: i64> GeoType
    for ScalarUnit<DST_NUM, DST_DENOM, ANG_NUM, ANG_DENOM>
{
    type Target = Scalar;

    fn get_type() -> Type {
        Type::Scalar(Some(Self::get_unit()))
    }
}

impl<const DST_NUM: i64, const DST_DENOM: i64, const ANG_NUM: i64, const ANG_DENOM: i64>
    From<Expr<Scalar>> for ScalarUnit<DST_NUM, DST_DENOM, ANG_NUM, ANG_DENOM>
{
    fn from(value: Expr<Scalar>) -> Self {
        assert_eq!(value.data.unit, Some(Self::get_unit()));
        Self(value)
    }
}

impl<const DST_NUM: i64, const DST_DENOM: i64, const ANG_NUM: i64, const ANG_DENOM: i64> Deref
    for ScalarUnit<DST_NUM, DST_DENOM, ANG_NUM, ANG_DENOM>
{
    type Target = Expr<Scalar>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const DST_NUM: i64, const DST_DENOM: i64, const ANG_NUM: i64, const ANG_DENOM: i64> DerefMut
    for ScalarUnit<DST_NUM, DST_DENOM, ANG_NUM, ANG_DENOM>
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<const DST_NUM: i64, const DST_DENOM: i64, const ANG_NUM: i64, const ANG_DENOM: i64>
    From<ScalarUnit<DST_NUM, DST_DENOM, ANG_NUM, ANG_DENOM>> for AnyExpr
{
    fn from(value: ScalarUnit<DST_NUM, DST_DENOM, ANG_NUM, ANG_DENOM>) -> Self {
        value.0.into()
    }
}

pub type Distance = ScalarUnit<1, 1, 0, 1>;
pub type Angle = ScalarUnit<0, 1, 1, 1>;
pub type Unitless = ScalarUnit<0, 1, 0, 1>;

/// Returns what size of point collection can the given bundle type be cast onto.
/// 0 signifies that casting is not possible
pub const fn get_bundle_pc(_name: &'static str) -> usize {
    0
}

// macro_rules! ty {
//     (DISTANCE) => {$crate::script::ty::DISTANCE};
//     (ANGLE) => {$crate::script::ty::ANGLE};
//     (SCALAR) => {$crate::script::ty::SCALAR};
//     (SCALAR_UNKNOWN) => {$crate::script::ty::SCALAR_UNKNOWN};
//     (POINT) => {$crate::script::ty::POINT};
//     (LINE) => {$crate::script::ty::LINE};
//     (CIRCLE) => {$crate::script::ty::CIRCLE};
//     ($count:literal-P) => {
//         $crate::script::ty::collection($count)
//     };
//     ($t:ident) => {$crate::script::ty::bundle(stringify!($t))}
// }

/// Helper macros
pub mod macros {
    /// Get the expression at given index in a point collection.
    macro_rules! index {
        (no-node $col:expr, $at:expr) => {
            ($col).index_without_node($at)
        };
        (node $col:expr, $at:expr) => {
            ($col).index_with_node($at)
        };
    }

    /// Get a specific field from a bundle.
    macro_rules! field {
        (node POINT $bundle:expr, $at:ident with $context:ident) => {
            $crate::unroll::Convert::convert::<$crate::unroll::Point>(
                ($bundle).index_with_node(stringify!($at)),
                $context,
            )
        };
        (no-node POINT $bundle:expr, $at:ident with $context:ident) => {
            $crate::unroll::Convert::convert::<$crate::unroll::Point>(
                ($bundle).index_without_node(stringify!($at)),
                $context,
            )
        };
    }

    /// Create a constant number expression
    macro_rules! number {
        ($v:expr) => {
            $crate::builtins::macros::number!(SCALAR $v)
        };
        (=$v:expr) => {
            $crate::unroll::Expr {
                span: $crate::span!(0, 0, 0, 0),
                data: std::rc::Rc::new($crate::unroll::Scalar {
                    unit: Some($crate::unit::DISTANCE),
                    data: $crate::unroll::ScalarData::DstLiteral(
                        $v.clone()
                    )
                }),
                node: None
            }
        };
        ($t:ident $v:expr) => {
            $crate::unroll::Expr {
                span: $crate::span!(0, 0, 0, 0),
                data: std::rc::Rc::new($crate::unroll::Scalar {
                    unit: Some($crate::unit::$t),
                    data: $crate::unroll::ScalarData::Number($v)
                }),
                node: None
            }
        };
    }

    /// Construct a bundle from a name and fields
    macro_rules! construct_bundle {
        ($t:ident { $($field:ident : $value:expr),* $(,)? }) => {{
            let mut fields = std::collections::HashMap::new();
            let mut node = $crate::unroll::figure::BundleNode::new();

            $(
                let mut v = $crate::unroll::CloneWithNode::clone_with_node(&mut $value);
                node.insert(stringify!($field).to_string(), $crate::unroll::CloneWithNode::clone_with_node(&mut v));
                fields.insert(stringify!($field).to_string(), $crate::unroll::AnyExpr::from(v));
            )*

            $t::from($crate::unroll::Expr {
                span: $crate::span!(0, 0, 0, 0),
                data: std::rc::Rc::new($crate::unroll::Bundle {
                    name: stringify!($t),
                    data: $crate::unroll::BundleData::ConstructBundle(fields.into())
                }),
                node: Some($crate::unroll::figure::HierarchyNode::new(node))
            })
        }};
    }

    /// Define a new bundle type
    macro_rules! define_bundle {
        ($t:ident {}) => {
            pub struct $t(Expr<Bundle>);

            impl GeoType for $t {
                type Target = Bundle;

                fn get_type() -> $crate::parser::Type {
                    $crate::parser::Type::Bundle(stringify!($t))
                }
            }

            impl From<Expr<Bundle>> for $t {
                fn from(value: Expr<Bundle>) -> Self {
                    assert_eq!(value.data.name, stringify!($t));
                    Self(value)
                }
            }

            impl std::ops::Deref for $t {
                type Target = Expr<Bundle>;

                fn deref(&self) -> &Self::Target {
                    &self.0
                }
            }

            impl std::ops::DerefMut for $t {
                fn deref_mut(&mut self) -> &mut Self::Target {
                    &mut self.0
                }
            }

            impl From<$t> for $crate::unroll::AnyExpr {
                fn from(value: $t) -> Self {
                    value.0.into()
                }
            }
        };
    }

    pub(crate) use {construct_bundle, define_bundle, field, index, number};
}
