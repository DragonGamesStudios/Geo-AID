/*
Copyright (c) 2023 Michał Wilczek, Michał Margos

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the “Software”), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense,
and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do
so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial
portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS
OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

use std::{cell::RefCell, collections::HashMap, rc::Rc, sync::Arc, unreachable};

use num_traits::{One, ToPrimitive, Zero};

use crate::generator::expression::expr::{PointOnLine, Pow};
use crate::generator::fast_float::FastFloat;
use crate::script::unit;
use crate::script::unroll::{
    context::Definition, AnyExpr as UnrolledAny, Circle, ConvertFrom, Generic, Line, Point, Scalar,
    ScalarData,
};
use crate::{
    generator::{
        self,
        expression::{
            expr::{
                AngleBisector, AngleLine, AnglePoint, AnglePointDir, Average, CenterRadius,
                CircleCenter, CircleRadius, Difference, FreePoint, LineLineIntersection, LinePoint,
                Literal, Negation, ParallelThrough, PerpendicularThrough, PointLineDistance,
                PointOnCircle, PointPointDistance, PointX, PointY, Product, Quotient, Real, Sum,
            },
            AnyExpr, CircleExpr, Expression, LineExpr, PointExpr, ScalarExpr, Weights,
        },
        AdjustableTemplate, Flags, Optimizations,
    },
    span,
};

use super::token::number::CompExponent;
use super::unroll::{
    figure::{CollectionNode, Node},
    CloneWithNode, Displayed, UnrolledRule,
};
use super::{
    figure::Figure,
    unroll::{
        self,
        context::{
            Circle as EntCircle, CompileContext, Entity, Line as EntLine, Point as EntPoint,
            Scalar as EntScalar,
        },
        Expr, Flag, UnrolledRuleKind, Variable,
    },
    Criteria, CriteriaKind, Error, HashableRc, SimpleUnit,
};

trait Mapping<K, T> {
    fn get(&self, key: &HashableRc<K>) -> Option<&Arc<Expression<T>>>;

    fn insert(
        &mut self,
        key: HashableRc<K>,
        value: Arc<Expression<T>>,
    ) -> Option<Arc<Expression<T>>>;
}

#[derive(Debug, Default)]
struct ExpressionRecord {
    points: HashMap<HashableRc<Point>, Arc<Expression<PointExpr>>>,
    lines: HashMap<HashableRc<Line>, Arc<Expression<LineExpr>>>,
    scalars: HashMap<HashableRc<Scalar>, Arc<Expression<ScalarExpr>>>,
    circles: HashMap<HashableRc<Circle>, Arc<Expression<CircleExpr>>>,
}

#[derive(Debug, Default)]
struct VariableRecord {
    points: HashMap<HashableRc<RefCell<Variable<Point>>>, Arc<Expression<PointExpr>>>,
    lines: HashMap<HashableRc<RefCell<Variable<Line>>>, Arc<Expression<LineExpr>>>,
    scalars: HashMap<HashableRc<RefCell<Variable<Scalar>>>, Arc<Expression<ScalarExpr>>>,
    circles: HashMap<HashableRc<RefCell<Variable<Circle>>>, Arc<Expression<CircleExpr>>>,
}

impl Mapping<RefCell<Variable<Point>>, PointExpr> for VariableRecord {
    fn get(
        &self,
        key: &HashableRc<RefCell<Variable<Point>>>,
    ) -> Option<&Arc<Expression<PointExpr>>> {
        self.points.get(key)
    }

    fn insert(
        &mut self,
        key: HashableRc<RefCell<Variable<Point>>>,
        value: Arc<Expression<PointExpr>>,
    ) -> Option<Arc<Expression<PointExpr>>> {
        self.points.insert(key, value)
    }
}

impl Mapping<RefCell<Variable<Line>>, LineExpr> for VariableRecord {
    fn get(&self, key: &HashableRc<RefCell<Variable<Line>>>) -> Option<&Arc<Expression<LineExpr>>> {
        self.lines.get(key)
    }

    fn insert(
        &mut self,
        key: HashableRc<RefCell<Variable<Line>>>,
        value: Arc<Expression<LineExpr>>,
    ) -> Option<Arc<Expression<LineExpr>>> {
        self.lines.insert(key, value)
    }
}

impl Mapping<RefCell<Variable<Scalar>>, ScalarExpr> for VariableRecord {
    fn get(
        &self,
        key: &HashableRc<RefCell<Variable<Scalar>>>,
    ) -> Option<&Arc<Expression<ScalarExpr>>> {
        self.scalars.get(key)
    }

    fn insert(
        &mut self,
        key: HashableRc<RefCell<Variable<Scalar>>>,
        value: Arc<Expression<ScalarExpr>>,
    ) -> Option<Arc<Expression<ScalarExpr>>> {
        self.scalars.insert(key, value)
    }
}

impl Mapping<RefCell<Variable<Circle>>, CircleExpr> for VariableRecord {
    fn get(
        &self,
        key: &HashableRc<RefCell<Variable<Circle>>>,
    ) -> Option<&Arc<Expression<CircleExpr>>> {
        self.circles.get(key)
    }

    fn insert(
        &mut self,
        key: HashableRc<RefCell<Variable<Circle>>>,
        value: Arc<Expression<CircleExpr>>,
    ) -> Option<Arc<Expression<CircleExpr>>> {
        self.circles.insert(key, value)
    }
}

pub type CompiledPoint = Arc<Expression<PointExpr>>;
pub type CompiledScalar = Arc<Expression<ScalarExpr>>;
pub type CompiledCircle = Arc<Expression<CircleExpr>>;
pub type CompiledLine = Arc<Expression<LineExpr>>;

#[derive(Debug, Clone)]
pub enum CompiledEntity {
    Point(CompiledPoint),
    Scalar(CompiledScalar),
    Circle(CompiledCircle),
    Line(CompiledLine),
    None, // Used for not-yet compiled entities.
}

impl CompiledEntity {
    #[must_use]
    pub fn as_point(&self) -> Option<&CompiledPoint> {
        if let Self::Point(v) = self {
            Some(v)
        } else {
            None
        }
    }

    #[must_use]
    pub fn as_scalar(&self) -> Option<&CompiledScalar> {
        if let Self::Scalar(v) = self {
            Some(v)
        } else {
            None
        }
    }

    #[must_use]
    pub fn as_line(&self) -> Option<&CompiledLine> {
        if let Self::Line(v) = self {
            Some(v)
        } else {
            None
        }
    }

    #[must_use]
    pub fn as_circle(&self) -> Option<&CompiledCircle> {
        if let Self::Circle(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the compiled entity is [`None`].
    ///
    /// [`None`]: CompiledEntity::None
    #[must_use]
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
}

pub struct Compiler {
    variables: VariableRecord,
    expressions: ExpressionRecord,
    entities: Vec<CompiledEntity>,
    dst_var: Expr<Scalar>,
    context: CompileContext,
    template: Vec<AdjustableTemplate>,
    // Specifically for bounds.
    adjustable_points: Vec<(Arc<Expression<PointExpr>>, usize)>,
}

impl Compiler {
    #[must_use]
    pub fn new(mut context: CompileContext) -> Self {
        let dst_var = context.add_scalar();

        let dst_var = Expr {
            weight: FastFloat::Other(0.1), // We reduce the weight of distance to reduce its changes.
            data: Rc::new(Scalar {
                unit: Some(unit::DISTANCE),
                data: ScalarData::Entity(dst_var),
            }),
            span: span!(0, 0, 0, 0),
            node: None,
        };

        let mut entities = Vec::new();
        entities.resize(context.entities.len(), CompiledEntity::None);

        Self {
            variables: VariableRecord::default(),
            expressions: ExpressionRecord::default(),
            dst_var,
            entities,
            context,
            template: Vec::new(),
            adjustable_points: Vec::new(),
        }
    }

    fn compile_generic<T, U>(&mut self, generic: &Generic<T>) -> Arc<Expression<U>>
    where
        T: Definition + ConvertFrom<UnrolledAny>,
        Compiler: Compile<T, U>,
        VariableRecord: Mapping<RefCell<Variable<T>>, U>,
    {
        match generic {
            Generic::VariableAccess(var) => self.compile_variable(var),
            Generic::Boxed(expr) => self.compile(expr),
            Generic::Dummy => unreachable!("dummy expression appeared in compile step"),
        }
    }
}

pub trait Compile<T: Displayed, U> {
    fn compile(&mut self, expr: &Expr<T>) -> Arc<Expression<U>>;
}

impl Compile<Point, PointExpr> for Compiler {
    fn compile(&mut self, expr: &Expr<Point>) -> CompiledPoint {
        // First we have to check if this expression has been compiled already.
        let key = HashableRc::new(Rc::clone(&expr.data));

        if let Some(v) = self.expressions.points.get(&key) {
            // If so, we return it.
            return Arc::clone(v);
        }

        // Otherwise we compile.
        let compiled = match expr.data.as_ref() {
            Point::Generic(generic) => self.compile_generic(generic),
            Point::Entity(i) => self.compile_entity(*i).as_point().unwrap().clone(),
            Point::LineLineIntersection(k, l) => Arc::new(Expression::new(
                PointExpr::LineLineIntersection(LineLineIntersection {
                    k: self.compile(k),
                    l: self.compile(l),
                }),
                expr.weight,
            )),
            Point::Average(exprs) => Arc::new(Expression::new(
                PointExpr::Average(Average {
                    items: exprs.iter().map(|expr| self.compile(expr)).collect(),
                }),
                expr.weight,
            )),
            Point::CircleCenter(circle) => Arc::new(Expression::new(
                PointExpr::CircleCenter(CircleCenter {
                    circle: self.compile(circle),
                }),
                expr.weight,
            )),
        };

        // We insert for memory.
        self.expressions.points.insert(key, Arc::clone(&compiled));
        compiled
    }
}

impl Compile<Line, LineExpr> for Compiler {
    fn compile(&mut self, expr: &Expr<Line>) -> Arc<Expression<LineExpr>> {
        // First we have to check if this expression has been compiled already.
        let key = HashableRc::new(Rc::clone(&expr.data));

        if let Some(v) = self.expressions.lines.get(&key) {
            // If so, we return it.
            return Arc::clone(v);
        }

        // Otherwise we compile.
        let compiled = match expr.data.as_ref() {
            Line::Generic(generic) => self.compile_generic(generic),
            Line::Entity(i) => self.compile_entity(*i).as_line().unwrap().clone(),
            Line::LineFromPoints(p1, p2) => Arc::new(Expression::new(
                LineExpr::Line(LinePoint {
                    a: self.compile(p1),
                    b: self.compile(p2),
                }),
                expr.weight,
            )),
            Line::ParallelThrough(line, point) => Arc::new(Expression::new(
                LineExpr::ParallelThrough(ParallelThrough {
                    line: self.compile(line),
                    point: self.compile(point),
                }),
                expr.weight,
            )),
            Line::PerpendicularThrough(line, point) => Arc::new(Expression::new(
                LineExpr::PerpendicularThrough(PerpendicularThrough {
                    line: self.compile(line),
                    point: self.compile(point),
                }),
                expr.weight,
            )),
            Line::AngleBisector(v1, v2, v3) => Arc::new(Expression::new(
                LineExpr::AngleBisector(AngleBisector {
                    arm1: self.compile(v1),
                    origin: self.compile(v2),
                    arm2: self.compile(v3),
                }),
                expr.weight,
            )),
        };

        // We insert for memory.
        self.expressions.lines.insert(key, Arc::clone(&compiled));
        compiled
    }
}

impl Compile<Circle, CircleExpr> for Compiler {
    fn compile(&mut self, expr: &Expr<Circle>) -> CompiledCircle {
        // First we have to check if this expression has been compiled already.
        let key = HashableRc::new(Rc::clone(&expr.data));

        if let Some(v) = self.expressions.circles.get(&key) {
            // If so, we return it.
            return Arc::clone(v);
        }

        let compiled = match expr.data.as_ref() {
            Circle::Generic(generic) => self.compile_generic(generic),
            Circle::Circle(center, radius) => Arc::new(Expression::new(
                CircleExpr::CenterRadius(CenterRadius {
                    center: self.compile(center),
                    radius: self.compile(radius),
                }),
                expr.weight,
            )),
            Circle::Entity(i) => self.compile_entity(*i).as_circle().unwrap().clone(),
        };

        // We insert for memory.
        self.expressions.circles.insert(key, Arc::clone(&compiled));
        compiled
    }
}

impl Compiler {
    #[must_use]
    pub fn fix_distance(&self, expr: Expr<Scalar>, power: CompExponent) -> Expr<Scalar> {
        let sp = expr.span;
        let u = expr.data.unit;

        if power.is_zero() {
            expr
        } else if power.is_one() {
            Expr {
                weight: FastFloat::One,
                data: Rc::new(Scalar {
                    unit: u,
                    data: ScalarData::Multiply(expr, self.dst_var.clone_without_node()),
                }),
                span: sp,
                node: None,
            }
        } else {
            Expr {
                weight: FastFloat::One,
                data: Rc::new(Scalar {
                    unit: u,
                    data: ScalarData::Multiply(
                        expr,
                        Expr {
                            weight: FastFloat::One,
                            data: Rc::new(Scalar {
                                unit: u,
                                data: ScalarData::Pow(self.dst_var.clone_without_node(), power),
                            }),
                            span: sp,
                            node: None,
                        },
                    ),
                }),
                span: sp,
                node: None,
            }
        }
    }

    fn compile_number(&mut self, expr: &Expr<Scalar>, v: f64) -> Arc<Expression<ScalarExpr>> {
        if expr.data.unit == Some(unit::SCALAR) {
            // If a scalar, we treat it as a standard literal.
            Arc::new(Expression::new(
                ScalarExpr::Literal(Literal { value: v }),
                FastFloat::One,
            ))
        } else {
            // Otherwise we pretend it's a scalar literal inside a SetUnit.
            self.compile(&Expr {
                weight: FastFloat::One,
                span: expr.span,
                data: Rc::new(Scalar {
                    unit: expr.data.unit,
                    data: ScalarData::SetUnit(
                        Expr {
                            weight: expr.weight,
                            span: expr.span,
                            data: Rc::new(Scalar {
                                unit: Some(unit::SCALAR),
                                data: expr.data.data.clone_without_node(),
                            }),
                            node: None,
                        },
                        expr.data.unit.unwrap(),
                    ),
                }),
                node: None,
            })
        }
    }

    /// Attempts to compile the variable. If the variable is a `PointCollection`, leaves it unrolled. Otherwise everything is compiled properly.
    fn compile_variable<T: Displayed, U>(
        &mut self,
        var: &Rc<RefCell<Variable<T>>>,
    ) -> Arc<Expression<U>>
    where
        VariableRecord: Mapping<RefCell<Variable<T>>, U>,
        Self: Compile<T, U>,
    {
        // We first have to see if the variable already exists.
        let key = HashableRc::new(Rc::clone(var));

        if let Some(v) = self.variables.get(&key) {
            // So we can return it here.
            return Arc::clone(v);
        }

        // And otherwise compile it.
        let compiled = self.compile(&var.borrow().definition);

        // We insert for memory
        self.variables
            .insert(HashableRc::new(Rc::clone(var)), compiled.clone());
        compiled
    }

    /// Compiles the entity by index.
    #[must_use]
    fn compile_entity(&mut self, entity: usize) -> CompiledEntity {
        // If the expression is compiled, there's no problem
        match self.entities[entity].clone() {
            CompiledEntity::None => {
                let ent = self.context.entities[entity].clone_without_node();

                self.entities[entity] = match &ent {
                    Entity::Scalar(v) => CompiledEntity::Scalar(match v {
                        EntScalar::Free => {
                            self.template.push(AdjustableTemplate::Real);
                            Arc::new(Expression::new(
                                ScalarExpr::Real(Real {
                                    index: self.template.len() - 1,
                                }),
                                FastFloat::One,
                            ))
                        }
                        EntScalar::Bind(expr) => self.compile(expr),
                    }),
                    Entity::Point(v) => CompiledEntity::Point(match v {
                        EntPoint::Free => {
                            self.template.push(AdjustableTemplate::Point);
                            let expr = Arc::new(Expression::new(
                                PointExpr::Free(FreePoint {
                                    index: self.template.len() - 1,
                                }),
                                FastFloat::One,
                            ));
                            self.adjustable_points
                                .push((Arc::clone(&expr), self.template.len() - 1));
                            expr
                        }
                        EntPoint::OnCircle(circle) => {
                            self.template.push(AdjustableTemplate::PointOnCircle);
                            let expr = Arc::new(Expression::new(
                                PointExpr::OnCircle(PointOnCircle {
                                    index: self.template.len() - 1,
                                    circle: self.compile(circle),
                                }),
                                FastFloat::One,
                            ));
                            self.adjustable_points
                                .push((Arc::clone(&expr), self.template.len() - 1));
                            expr
                        }
                        EntPoint::OnLine(line) => {
                            self.template.push(AdjustableTemplate::PointOnLine);
                            let expr = Arc::new(Expression::new(
                                PointExpr::OnLine(PointOnLine {
                                    index: self.template.len() - 1,
                                    line: self.compile(line),
                                }),
                                FastFloat::One,
                            ));
                            self.adjustable_points
                                .push((Arc::clone(&expr), self.template.len() - 1));
                            expr
                        }
                        EntPoint::Bind(expr) => self.compile(expr),
                    }),
                    Entity::Line(v) => CompiledEntity::Line(match v {
                        EntLine::Bind(expr) => self.compile(expr),
                    }),
                    Entity::Circle(v) => CompiledEntity::Circle(match v {
                        EntCircle::Bind(expr) => self.compile(expr),
                        EntCircle::Temporary => unreachable!(),
                    }),
                };

                self.entities[entity].clone()
            }
            v => v,
        }
    }

    fn compile_rule_vec<'r, I: IntoIterator<Item = &'r UnrolledRule>>(
        &mut self,
        rules: I,
    ) -> Vec<Criteria> {
        rules
            .into_iter()
            .map(|rule| self.compile_rule(rule))
            .collect()
    }

    fn compile_rule_kind_vec<'r, I: IntoIterator<Item = &'r UnrolledRuleKind>>(
        &mut self,
        rules: I,
    ) -> Vec<CriteriaKind> {
        rules
            .into_iter()
            .map(|rule| self.compile_rule_kind(rule))
            .collect()
    }

    fn compile_rule_kind(&mut self, rule: &UnrolledRuleKind) -> CriteriaKind {
        match &rule {
            UnrolledRuleKind::PointEq(lhs, rhs) => {
                let lhs = self.compile(lhs);
                let rhs = self.compile(rhs);

                CriteriaKind::EqualPoint(lhs, rhs)
            }
            UnrolledRuleKind::ScalarEq(lhs, rhs) => {
                let lhs = self.compile(lhs);
                let rhs = self.compile(rhs);

                CriteriaKind::EqualScalar(lhs, rhs)
            }
            UnrolledRuleKind::Gt(lhs, rhs) => {
                let lhs = self.compile(lhs);
                let rhs = self.compile(rhs);

                CriteriaKind::Greater(lhs, rhs)
            }
            UnrolledRuleKind::Lt(lhs, rhs) => {
                let lhs = self.compile(lhs);
                let rhs = self.compile(rhs);

                CriteriaKind::Less(lhs, rhs)
            }
            UnrolledRuleKind::Alternative(rules) => {
                CriteriaKind::Alternative(self.compile_rule_kind_vec(rules.iter().map(|x| &x.kind)))
            }
            UnrolledRuleKind::Bias(expr) => CriteriaKind::Bias(match expr {
                UnrolledAny::Point(v) => {
                    let e = self.compile(v);
                    Arc::new(Expression {
                        kind: AnyExpr::Point(e.kind.clone()),
                        weights: e.weights.clone(),
                    })
                }
                UnrolledAny::Line(v) => {
                    let e = self.compile(v);
                    Arc::new(Expression {
                        kind: AnyExpr::Line(e.kind.clone()),
                        weights: e.weights.clone(),
                    })
                }
                UnrolledAny::Scalar(v) => {
                    let e = self.compile(v);
                    Arc::new(Expression {
                        kind: AnyExpr::Scalar(e.kind.clone()),
                        weights: e.weights.clone(),
                    })
                }
                UnrolledAny::Circle(v) => {
                    let e = self.compile(v);
                    Arc::new(Expression {
                        kind: AnyExpr::Circle(e.kind.clone()),
                        weights: e.weights.clone(),
                    })
                }
                _ => unreachable!(),
            }),
        }
    }

    fn compile_rule(&mut self, rule: &UnrolledRule) -> Criteria {
        if rule.inverted {
            Criteria::new(
                CriteriaKind::Inverse(Box::new(self.compile_rule_kind(&rule.kind))),
                rule.weight,
            )
        } else {
            Criteria::new(self.compile_rule_kind(&rule.kind), rule.weight)
        }
    }

    #[must_use]
    fn compile_rules(&mut self) -> Vec<Criteria> {
        let rules = self.context.take_rules();

        self.compile_rule_vec(&rules)
    }

    /// Builds an actual figure.
    fn build_figure(&mut self, figure: CollectionNode, canvas_size: (usize, usize)) -> Figure {
        let mut compiled = Figure {
            canvas_size,
            ..Default::default()
        };

        figure.build_unboxed(self, &mut compiled);

        compiled
    }
}

impl Compile<Scalar, ScalarExpr> for Compiler {
    #[allow(clippy::too_many_lines)]
    fn compile(&mut self, expr: &Expr<Scalar>) -> CompiledScalar {
        // First we have to check if this expression has been compiled already.
        let key = HashableRc::new(Rc::clone(&expr.data));

        if let Some(v) = self.expressions.scalars.get(&key) {
            // If so, we return it.
            return Arc::clone(v);
        }

        // Otherwise we compile.
        let compiled = match &expr.data.data {
            ScalarData::Generic(generic) => self.compile_generic(generic),
            ScalarData::PointX(v) => Arc::new(Expression::new(
                ScalarExpr::PointX(PointX {
                    point: self.compile(v),
                }),
                v.weight,
            )),
            ScalarData::PointY(v) => Arc::new(Expression::new(
                ScalarExpr::PointY(PointY {
                    point: self.compile(v),
                }),
                v.weight,
            )),
            ScalarData::Number(v) => self.compile_number(expr, *v),
            ScalarData::DstLiteral(v) => Arc::new(Expression::new(
                ScalarExpr::Literal(Literal { value: *v }),
                FastFloat::Zero,
            )),
            ScalarData::Entity(i) => self.compile_entity(*i).as_scalar().unwrap().clone(),
            ScalarData::SetUnit(expr, unit) => self.compile(&self.fix_distance(
                expr.clone_without_node(),
                unit[SimpleUnit::Distance as usize]
                    - match expr.data.unit {
                        Some(unit) => unit[SimpleUnit::Distance as usize],
                        None => CompExponent::zero(),
                    },
            )),
            ScalarData::PointPointDistance(p1, p2) => Arc::new(Expression::new(
                ScalarExpr::PointPointDistance(PointPointDistance {
                    a: self.compile(p1),
                    b: self.compile(p2),
                }),
                expr.weight,
            )),
            ScalarData::PointLineDistance(p, l) => Arc::new(Expression::new(
                ScalarExpr::PointLineDistance(PointLineDistance {
                    point: self.compile(p),
                    line: self.compile(l),
                }),
                expr.weight,
            )),
            ScalarData::Negate(expr) => Arc::new(Expression::new(
                ScalarExpr::Negation(Negation {
                    value: self.compile(expr),
                }),
                expr.weight,
            )),
            ScalarData::Pow(expr, exponent) => Arc::new(Expression::new(
                ScalarExpr::Pow(Pow {
                    value: self.compile(expr),
                    exponent: exponent.to_f64().unwrap(),
                }),
                expr.weight,
            )),
            ScalarData::Add(v1, v2) => Arc::new(Expression::new(
                ScalarExpr::Sum(Sum {
                    a: self.compile(v1),
                    b: self.compile(v2),
                }),
                expr.weight,
            )),
            ScalarData::Subtract(v1, v2) => Arc::new(Expression::new(
                ScalarExpr::Difference(Difference {
                    a: self.compile(v1),
                    b: self.compile(v2),
                }),
                expr.weight,
            )),
            ScalarData::Multiply(v1, v2) => Arc::new(Expression::new(
                ScalarExpr::Product(Product {
                    a: self.compile(v1),
                    b: self.compile(v2),
                }),
                expr.weight,
            )),
            ScalarData::Divide(v1, v2) => Arc::new(Expression::new(
                ScalarExpr::Quotient(Quotient {
                    a: self.compile(v1),
                    b: self.compile(v2),
                }),
                expr.weight,
            )),
            ScalarData::ThreePointAngle(v1, v2, v3) => Arc::new(Expression::new(
                ScalarExpr::AnglePoint(AnglePoint {
                    arm1: self.compile(v1),
                    origin: self.compile(v2),
                    arm2: self.compile(v3),
                }),
                expr.weight,
            )),
            ScalarData::ThreePointAngleDir(v1, v2, v3) => Arc::new(Expression::new(
                ScalarExpr::AnglePointDir(AnglePointDir {
                    arm1: self.compile(v1),
                    origin: self.compile(v2),
                    arm2: self.compile(v3),
                }),
                expr.weight,
            )),
            ScalarData::TwoLineAngle(v1, v2) => Arc::new(Expression::new(
                ScalarExpr::AngleLine(AngleLine {
                    k: self.compile(v1),
                    l: self.compile(v2),
                }),
                expr.weight,
            )),
            ScalarData::Average(exprs) => Arc::new(Expression::new(
                ScalarExpr::Average(Average {
                    items: exprs.iter().map(|expr| self.compile(expr)).collect(),
                }),
                expr.weight,
            )),
            ScalarData::CircleRadius(circle) => Arc::new(Expression::new(
                ScalarExpr::CircleRadius(CircleRadius {
                    circle: self.compile(circle),
                }),
                expr.weight,
            )),
        };

        // We insert for memory.
        self.expressions.scalars.insert(key, Arc::clone(&compiled));
        compiled
    }
}

fn read_flags(flags: &HashMap<String, Flag>) -> Flags {
    Flags {
        optimizations: Optimizations {
            identical_expressions: flags["optimizations"].as_set().unwrap()
                ["identical_expressions"]
                .as_bool()
                .unwrap(),
        },
        point_bounds: flags["point_bounds"].as_bool().unwrap(),
    }
}

#[derive(Debug)]
pub struct Compiled {
    pub criteria: Vec<Criteria>,
    pub figure: Figure,
    pub template: Vec<AdjustableTemplate>,
    pub flags: generator::Flags,
}

/// Compiles the given script.
///
/// # Errors
/// Exact descriptions of errors are in `ScriptError` documentation.
///
/// # Panics
/// Never
pub fn compile(input: &str, canvas_size: (usize, usize)) -> Result<Compiled, Vec<Error>> {
    // First, we have to unroll the script.
    let (context, figure) = unroll::unroll(input)?;

    let flags = read_flags(&context.flags);

    // Print rules (debugging)
    // for rule in &context.rules {
    //     println!("{}: {rule}", rule.inverted);
    // }

    let mut compiler = Compiler::new(context);

    // And compile the rules
    let mut criteria = compiler.compile_rules();

    // Check if dst_var is ever used.
    if let CompiledEntity::Scalar(dst) = compiler.entities.last().unwrap() {
        // It's worth noting, that assigning a smaller weight will never be enough. We have to also bias the quality.
        let dst_any = Arc::new(Expression {
            kind: AnyExpr::Scalar(dst.kind.clone()),
            weights: dst.weights.clone(),
        });

        criteria.push(Criteria::new(
            CriteriaKind::Bias(dst_any),
            FastFloat::Other(10.0), // The bias.
        ));
    }

    // println!("{:#?}", criteria);

    // Add standard bounds
    add_bounds(&compiler.adjustable_points, &mut criteria, &flags);

    // Print the compiled (debugging)
    // for rule in &criteria {
    //     println!("{rule}");
    // }

    let figure = compiler.build_figure(figure, canvas_size);
    Ok(Compiled {
        criteria,
        figure,
        template: compiler.template,
        flags,
    })
}

/// Inequality principle and the point plane limit.
fn add_bounds(
    points: &[(Arc<Expression<PointExpr>>, usize)],
    criteria: &mut Vec<Criteria>,
    flags: &Flags,
) {
    // Point inequality principle.
    for (i, (pt_i, adj)) in points.iter().enumerate() {
        // For each of the next points, add an inequality rule.
        for (pt_j, _) in points.iter().skip(i + 1) {
            criteria.push(Criteria::new(
                CriteriaKind::Inverse(Box::new(CriteriaKind::EqualPoint(
                    Arc::clone(pt_i),
                    Arc::clone(pt_j),
                ))),
                FastFloat::One,
            ));
        }

        if flags.point_bounds {
            // For each point, add a rule limiting its range.
            criteria.push(Criteria::new(
                CriteriaKind::Greater(
                    Arc::new(Expression {
                        weights: Weights::one_at(*adj),
                        kind: ScalarExpr::PointX(PointX {
                            point: Arc::clone(pt_i),
                        }),
                    }),
                    Arc::new(Expression {
                        weights: Weights::empty(),
                        kind: ScalarExpr::Literal(Literal { value: 0.0 }),
                    }),
                ),
                FastFloat::One,
            )); // x > 0

            criteria.push(Criteria::new(
                CriteriaKind::Greater(
                    Arc::new(Expression {
                        weights: Weights::one_at(*adj),
                        kind: ScalarExpr::PointY(PointY {
                            point: Arc::clone(pt_i),
                        }),
                    }),
                    Arc::new(Expression {
                        weights: Weights::empty(),
                        kind: ScalarExpr::Literal(Literal { value: 1.0 }),
                    }),
                ),
                FastFloat::One,
            )); // y > 0

            criteria.push(Criteria::new(
                CriteriaKind::Less(
                    Arc::new(Expression {
                        weights: Weights::one_at(*adj),
                        kind: ScalarExpr::PointX(PointX {
                            point: Arc::clone(pt_i),
                        }),
                    }),
                    Arc::new(Expression {
                        weights: Weights::empty(),
                        kind: ScalarExpr::Literal(Literal { value: 1.0 }),
                    }),
                ),
                FastFloat::One,
            )); // x < 1

            criteria.push(Criteria::new(
                CriteriaKind::Less(
                    Arc::new(Expression {
                        weights: Weights::one_at(*adj),
                        kind: ScalarExpr::PointY(PointY {
                            point: Arc::clone(pt_i),
                        }),
                    }),
                    Arc::new(Expression {
                        weights: Weights::empty(),
                        kind: ScalarExpr::Literal(Literal { value: 1.0 }),
                    }),
                ),
                FastFloat::One,
            )); // y < 1
        }
    }
}
