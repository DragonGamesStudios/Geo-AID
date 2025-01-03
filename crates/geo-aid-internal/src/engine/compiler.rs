//! This module contains functionality to compile Math IR
//! into Geo-AID's math backend IR, the last step before
//! compiling to the final form. The final step is performed
//! by the `geo-aid-math` crate.

use crate::geometry::{Circle, Complex, Line, ValueEnum};
use crate::script::figure::Generated;
use crate::script::math::{
    Entity, EntityKind, Expr, ExprKind, ExprType, Intermediate, Rule, RuleKind,
};
use geo_aid_figure::{EntityIndex, VarIndex};
use geo_aid_math::shared::Shared;
use geo_aid_math::{
    shared::Complex as ComplexExpr, shared::Real as RealExpr, Comparison, ComparisonKind,
    Condition, Context,
};
use num_traits::ToPrimitive;
use std::f64::consts::PI;

/// A function that takes in values for all inputs and returns
/// a generated figure
pub type FigureFn = Box<dyn for<'a> Fn(&'a [f64]) -> Generated>;

/// The result of the compilation of a Math IR.
pub struct Compiled {
    /// The figure function
    pub figure_fn: FigureFn,
    /// Errors of each adjustable
    pub errors: Vec<RealExpr>,
    /// The compile context. Can be used for further processing
    pub context: Shared,
    /// The number of inputs of this figure.
    pub input_count: usize,
    /// Errors of each rule (for debugging purposes)
    #[allow(unused)]
    pub rule_errors: Vec<RealExpr>,
}

/// Compile a Math IR into an (almost) compiled form.
#[must_use]
pub fn compile(intermediate: &Intermediate) -> Compiled {
    let inputs = intermediate
        .adjusted
        .entities
        .iter()
        .map(|ent| match ent {
            EntityKind::FreePoint => 2,
            EntityKind::PointOnLine { .. }
            | EntityKind::PointOnCircle { .. }
            | EntityKind::FreeReal
            | EntityKind::DistanceUnit => 1,
            EntityKind::Bind(_) => unreachable!(),
        })
        .sum();

    // for (i, var) in intermediate.figure.variables.iter().enumerate() {
    //     println!("[{i}] = {:?}", var.kind);
    // }

    // We start with constructing the figure function.

    let mut compiler = Compiler::new(
        inputs,
        &intermediate.adjusted.entities,
        &intermediate.figure.variables,
    );

    // Collect all expressions necessary for figure drawing.

    // Including the entities
    let mut entity_values = Vec::new();
    for (i, ent) in intermediate.figure.entities.iter().enumerate() {
        let v = Expr {
            meta: (),
            kind: ExprKind::Entity { id: EntityIndex(i) },
            ty: match ent {
                EntityKind::FreePoint
                | EntityKind::PointOnLine { line: _ }
                | EntityKind::PointOnCircle { circle: _ } => ExprType::Point,
                EntityKind::FreeReal | EntityKind::DistanceUnit => ExprType::Number,
                EntityKind::Bind(_) => unreachable!(),
            },
        };

        entity_values.push(compiler.compile_value(&v));
    }

    let mut exprs = Vec::new();
    for value in compiler.variables.iter().chain(&entity_values) {
        match value {
            ValueExpr::This(this) => exprs.push(this.expr),
            ValueExpr::Line(line) => exprs.extend([
                line.origin.real.expr,
                line.origin.imaginary.expr,
                line.direction.real.expr,
                line.direction.imaginary.expr,
            ]),
            ValueExpr::Complex(complex) => {
                exprs.extend([complex.real.expr, complex.imaginary.expr]);
            }
            ValueExpr::Circle(circle) => {
                exprs.extend([
                    circle.center.real.expr,
                    circle.center.imaginary.expr,
                    circle.radius.expr,
                ]);
            }
        }
    }

    let outs_len = exprs.len();
    let exprs = compiler.context.exec(|ctx| ctx.compute(exprs));
    let fig = intermediate.figure.clone();
    let figure_fn = Box::new(move |inputs: &[f64]| {
        let mut outputs = Vec::new();
        outputs.resize(outs_len, 0.0);
        exprs.call(inputs, outputs.as_mut_slice());

        get_figure(&fig, &outputs)
    });

    // Reset the compiler and gather rule errors.
    compiler = Compiler::new(
        inputs,
        &intermediate.adjusted.entities,
        &intermediate.adjusted.variables,
    );
    let rule_errors: Vec<_> = intermediate
        .adjusted
        .rules
        .iter()
        .map(|rule| (rule, compiler.compile_rule(rule)))
        .collect();

    let rule_error_exprs = rule_errors.iter().map(|v| v.1.clone()).collect();

    // Gather entity errors
    let mut entity_errors: Vec<_> = (0..intermediate.adjusted.entities.len())
        .map(|_| compiler.context.real_zero())
        .collect();
    for (rule, quality) in rule_errors {
        // println!("{rule}");
        for ent in &rule.entities {
            entity_errors[ent.0] += &quality;
        }
    }

    // For now, this is how we calculate errors

    Compiled {
        figure_fn,
        errors: entity_errors,
        context: compiler.context,
        input_count: inputs,
        rule_errors: rule_error_exprs,
    }
}

/// The compiler's state
struct Compiler<'r> {
    entities: &'r [EntityKind],
    context: Shared,
    variables: Vec<ValueExpr>,
    adjustables: Vec<ValueExpr>,
}

impl<'r> Compiler<'r> {
    /// Create a new compiler. Prepares some constants and precomputes all values.
    #[must_use]
    pub fn new(inputs: usize, entities: &'r [EntityKind], variables: &[Expr<()>]) -> Self {
        let mut adjustables = Vec::new();
        let context = Shared::new(inputs);

        let mut index = 0;
        #[allow(unused_variables)]
        for (i, ent) in entities.iter().enumerate() {
            // println!("@[{i}] = {ent:?}");
            match ent {
                EntityKind::FreePoint => {
                    adjustables.push(ValueExpr::Complex(ComplexExpr {
                        real: context.input(index),
                        imaginary: context.input(index + 1),
                    }));
                    index += 2;
                }
                EntityKind::PointOnLine { .. }
                | EntityKind::PointOnCircle { .. }
                | EntityKind::FreeReal
                | EntityKind::DistanceUnit => {
                    adjustables.push(ValueExpr::This(context.input(index)));
                    index += 1;
                }
                EntityKind::Bind(_) => unreachable!(),
            }
        }

        let mut s = Self {
            entities,
            context,
            variables: Vec::new(),
            adjustables,
        };

        #[allow(unused_variables)]
        for (i, var) in variables.iter().enumerate() {
            // println!("[{i}] = {:?}", var.kind);
            let expr = s.compile_value(var);
            s.variables.push(expr);
        }

        s
    }

    /// Compile the error function for a > b
    fn gt(&mut self, a: &VarIndex, b: &VarIndex) -> RealExpr {
        let a = self.variables[a.0].to_complex().real;
        let b = self.variables[b.0].to_complex().real;
        let one_tenth = self.context.constant(0.1);
        let offset = (b.abs() + &one_tenth) * &one_tenth;
        let threshold = b + &offset;
        let a_minus_threshold = a.clone() - &threshold;
        let one_side = a_minus_threshold.clone() * &a_minus_threshold;
        self.context.ternary(
            Condition::Comparison(Comparison {
                a: threshold.expr,
                b: a.expr,
                kind: ComparisonKind::Gt,
            }),
            one_side,
            self.context.real_zero(),
        )
    }

    /// Compile the error function for the given rule kind.
    fn compile_rule_kind(&mut self, kind: &RuleKind) -> RealExpr {
        match kind {
            RuleKind::PointEq(a, b) | RuleKind::NumberEq(a, b) => {
                // Weirdly, enough, these two are actually the same, right now
                let a = self.variables[a.0].to_complex();
                let b = self.variables[b.0].to_complex();
                let five = self.context.constant(5.0);
                (a - &b).norm() * &five
            }
            RuleKind::Gt(a, b) => self.gt(a, b),
            RuleKind::Alternative(rules) => {
                // necessary because borrowing
                let qualities: Vec<_> = rules
                    .iter()
                    .map(|rule| self.compile_rule_kind(rule))
                    .collect();

                qualities.into_iter().reduce(|a, b| a.min(&b)).unwrap()
            }
            RuleKind::Invert(q) => {
                self.context.real_one()
                    / &(self.context.constant(10.0) * &self.compile_rule_kind(q))
            }
            RuleKind::Bias => self.context.real_zero(), // Bias in this approach doesn't really do anything
        }
    }

    /// Compile the error function for the given rule.
    fn compile_rule(&mut self, rule: &Rule) -> RealExpr {
        let quality = self.compile_rule_kind(&rule.kind);
        let weight = self.context.constant(rule.weight.to_complex().real);
        quality * &weight
    }

    /// Compile the sum of given expressions.
    fn compile_sum(&mut self, value: &[VarIndex]) -> ComplexExpr {
        value
            .iter()
            .map(|i| self.variables[i.0].to_complex())
            .reduce(|a, b| a + &b)
            .unwrap_or(self.context.complex_zero())
    }

    /// Compile the product of different expressions
    fn compile_mul(&mut self, value: &[VarIndex]) -> ComplexExpr {
        value
            .iter()
            .map(|i| self.variables[i.0].to_complex())
            .reduce(|a, b| a * &b)
            .unwrap_or(self.context.complex_one())
    }

    /// Compile the specific expression.
    /// Assume all expressions it may depend on are already compiled.
    /// This assumption is true given that expressions are processed
    /// one by one, in a preordered fashion.
    #[allow(clippy::too_many_lines)]
    fn compile_value(&mut self, value: &Expr<()>) -> ValueExpr {
        match &value.kind {
            ExprKind::Entity { id } => {
                let kind = self.entities[id.0].clone();
                match kind {
                    EntityKind::FreePoint => self.adjustables[id.0].clone(),
                    EntityKind::PointOnLine { line } => {
                        let line = self.variables[line.0].to_line();
                        let offset = self.adjustables[id.0].to_single();

                        (line.origin + &(offset * &line.direction)).into()
                    }
                    EntityKind::PointOnCircle { circle } => {
                        let circle = self.variables[circle.0].to_circle();
                        let theta = self.adjustables[id.0].to_single();
                        let two_pi = self.context.constant(2.0 * PI);
                        let theta = theta * &two_pi;

                        let point_rel = ComplexExpr {
                            real: theta.cos(),
                            imaginary: theta.sin(),
                        } * &circle.radius;

                        (point_rel + &circle.center).into()
                    }
                    EntityKind::DistanceUnit | EntityKind::FreeReal => {
                        ComplexExpr::real(self.adjustables[id.0].to_single()).into()
                    }
                    EntityKind::Bind(_) => unreachable!(),
                }
            }
            ExprKind::LineLineIntersection { k, l } => {
                // This is the code in geometry.rs
                // let Line {
                //     origin: a,
                //     direction: b,
                // } = k_ln;
                // let Line {
                //     origin: c,
                //     direction: d,
                // } = l_ln;
                //
                // a - b * ((a - c) / d).imaginary / (b / d).imaginary
                // println!("Broke with k={k}, l={l}");
                // println!("{:#?}", self.variables);
                let k = self.variables[k.0].to_line();
                let l = self.variables[l.0].to_line();
                // a = k.origin;
                // b = k.direction;
                // c = l.origin;
                // d = l.direction;

                let b_by_d = k.direction.clone() / &l.direction;
                let a_sub_c = k.origin.clone() - &l.origin;
                let a_sub_c_by_d = a_sub_c / &l.direction;
                let quotient = a_sub_c_by_d.imaginary / &b_by_d.imaginary;
                let b_times_quotient = k.direction * &quotient;

                (k.origin - &b_times_quotient).into()
            }
            ExprKind::AveragePoint { items } => {
                let sum = self.compile_sum(items);

                #[allow(clippy::cast_precision_loss)]
                let len = self.context.constant(items.len() as f64);
                (sum / &len).into()
            }
            ExprKind::CircleCenter { circle } => self.variables[circle.0].to_circle().center.into(),
            ExprKind::ComplexToPoint { number } => self.variables[number.0].clone(),
            ExprKind::Sum { plus, minus } => {
                (self.compile_sum(plus) - &self.compile_sum(minus)).into()
            }
            ExprKind::Product { times, by } => {
                (self.compile_mul(times) / &self.compile_mul(by)).into()
            }
            ExprKind::Const { value } => {
                let value = value.to_complex();
                ComplexExpr {
                    real: self.context.constant(value.real),
                    imaginary: self.context.constant(value.imaginary),
                }
                .into()
            }
            ExprKind::Exponentiation { value, exponent } => {
                let value = self.variables[value.0].to_complex();
                let exp = self.context.constant(exponent.to_f64().unwrap());

                value.pow(&ComplexExpr::real(exp)).into()
            }
            ExprKind::PointPointDistance { p, q } => {
                let p = self.variables[p.0].to_complex();
                let q = self.variables[q.0].to_complex();

                ComplexExpr::real((p - &q).abs()).into()
            }
            ExprKind::PointLineDistance { point, line } => {
                // ((point - line.origin) / line.direction).imaginary.abs()
                let point = self.variables[point.0].to_complex();
                let line = self.variables[line.0].to_line();

                ComplexExpr::real(((point - &line.origin) / &line.direction).imaginary.abs()).into()
            }
            ExprKind::ThreePointAngle { p, q, r } => {
                // geometry.rs code
                // let arm1_vec = arm1 - origin;
                // let arm2_vec = arm2 - origin;
                //
                // // Get the dot product
                // let dot_product = arm1_vec.real * arm2_vec.real + arm1_vec.imaginary * arm2_vec.imaginary;
                //
                // // Get the argument
                // f64::acos(dot_product / (arm1_vec.magnitude() * arm2_vec.magnitude()))
                let p = self.variables[p.0].to_complex();
                let q = self.variables[q.0].to_complex();
                let r = self.variables[r.0].to_complex();

                let arm1_vec = p - &q;
                let arm2_vec = r - &q;

                let mag_product = arm1_vec.abs() * &arm2_vec.abs();
                let dot_product_alpha = arm1_vec.real * &arm2_vec.real;
                let dot_product_beta = arm1_vec.imaginary * &arm2_vec.imaginary;
                let dot_product = dot_product_alpha + &dot_product_beta;
                let quotient = dot_product / &mag_product;
                ComplexExpr::real(quotient.acos()).into()
            }
            ExprKind::ThreePointAngleDir { p, q, r } => {
                // geometry.rs code
                // Get the vectors to calculate the angle between them.
                // let arm1_vec = arm1 - origin;
                // let arm2_vec = arm2 - origin;
                //
                // // decrease p2's angle by p1's angle:
                // let p2_rotated = arm2_vec / arm1_vec;
                //
                // // Get the argument
                // p2_rotated.arg()
                let p = self.variables[p.0].to_complex();
                let q = self.variables[q.0].to_complex();
                let r = self.variables[r.0].to_complex();

                let arm1_vec = p - &q;
                let arm2_vec = r - &q;

                let rotated = arm2_vec / &arm1_vec;
                ComplexExpr::real(rotated.arg()).into()
            }
            ExprKind::TwoLineAngle { k, l } => {
                // (k.direction / l.direction).arg().abs()
                let k = self.variables[k.0].to_line();
                let l = self.variables[l.0].to_line();
                let quotient = k.direction / &l.direction;
                ComplexExpr::real(quotient.arg().abs()).into()
            }
            ExprKind::PointX { point } => {
                let point = self.variables[point.0].to_complex();
                ComplexExpr::real(point.real).into()
            }
            ExprKind::PointY { point } => {
                let point = self.variables[point.0].to_complex();
                ComplexExpr::real(point.imaginary).into()
            }
            ExprKind::PointToComplex { point } => self.variables[point.0].clone(),
            ExprKind::Real { number } => {
                ComplexExpr::real(self.variables[number.0].to_complex().real).into()
            }
            ExprKind::Imaginary { number } => {
                ComplexExpr::real(self.variables[number.0].to_complex().imaginary).into()
            }
            ExprKind::Log { number } => self.variables[number.0].to_complex().log().into(),
            ExprKind::Exp { number } => self.variables[number.0].to_complex().exp().into(),
            ExprKind::Sin { angle } => {
                let angle = self.variables[angle.0].to_complex();
                angle.sin().into()
            }
            ExprKind::Cos { angle } => {
                let angle = self.variables[angle.0].to_complex();
                angle.cos().into()
            }
            ExprKind::Atan2 { y, x } => {
                // Atan2 is never expected to take complex arguments.
                let y = self.variables[y.0].to_complex().real;
                let x = self.variables[x.0].to_complex().real;

                ComplexExpr::real(RealExpr::atan2(&y, &x)).into()
            }
            ExprKind::DirectionVector { line } => self.variables[line.0].to_line().direction.into(),
            ExprKind::PointPoint { p, q } => {
                let p = self.variables[p.0].to_complex();
                let q = self.variables[q.0].to_complex();
                let q_minus_p = q - &p;
                LineExpr {
                    origin: p,
                    direction: q_minus_p.clone() / &q_minus_p.abs(),
                }
                .into()
            }
            ExprKind::PointVector { point, vector } => {
                let point = self.variables[point.0].to_complex();
                let vector = self.variables[vector.0].to_complex();

                LineExpr {
                    origin: point,
                    direction: vector.clone() / &vector.abs(),
                }
                .into()
            }
            ExprKind::AngleBisector { p, q, r } => {
                // let a = arm1 - origin;
                // let b = arm2 - origin;
                //
                // // Get the bisector using the geometric mean.
                // let bi_dir = (a * b).sqrt_norm();
                //
                // Line::new(origin, bi_dir)
                //
                // Where sqrt_norm looks like this:
                // // The formula used here doesn't work for negative reals. We can use a trick here to bypass that restriction.
                // // If the real part is negative, we simply negate it to get a positive part and then multiply the result by `i`.
                // if self.real > 0.0 {
                //     // Use the generic formula (https://math.stackexchange.com/questions/44406/how-do-i-get-the-square-root-of-a-complex-number)
                //     let r = self.magnitude();
                //
                //     // We simply don't multiply by the square root of r.
                //     (self + r).normalize()
                // } else {
                //     (-self).sqrt_norm().mul_i() // Normalization isn't lost here.
                // }
                let arm1 = self.variables[p.0].to_complex();
                let origin = self.variables[q.0].to_complex();
                let arm2 = self.variables[r.0].to_complex();

                let ab = (arm1 - &origin) * &(arm2 - &origin);

                // sqrt_norm time
                let minus_ab = -ab.clone();

                let condition = Condition::Comparison(Comparison {
                    a: ab.real.expr,
                    b: Context::zero(),
                    kind: ComparisonKind::Gt,
                });
                let self_ = self.context.complex_ternary(condition, ab, minus_ab);

                let self_plus_r = self_.clone() + &self_.abs();
                let normalized = self_plus_r.clone() / &self_plus_r.abs();
                let normalized_mul_i = normalized.mul_i();

                // Another ternary
                let direction =
                    self.context
                        .complex_ternary(condition, normalized, normalized_mul_i);

                LineExpr { origin, direction }.into()
            }
            ExprKind::ParallelThrough { point, line } => {
                let point = self.variables[point.0].to_complex();
                let mut line = self.variables[line.0].to_line();

                line.origin = point;
                line.into()
            }
            ExprKind::PerpendicularThrough { point, line } => {
                let point = self.variables[point.0].to_complex();
                let line = self.variables[line.0].to_line();

                LineExpr {
                    origin: point,
                    direction: line.direction.mul_i(),
                }
                .into()
            }
            ExprKind::ConstructCircle { center, radius } => {
                let center = self.variables[center.0].to_complex();
                let radius = self.variables[radius.0].to_complex();

                CircleExpr {
                    center,
                    radius: radius.real,
                }
                .into()
            }
        }
    }
}

/// A generic compiled value of an expression.
#[derive(Debug, Clone)]
enum ValueExpr {
    This(RealExpr),
    Line(LineExpr),
    Complex(ComplexExpr),
    Circle(CircleExpr),
}

impl ValueExpr {
    /// Returns a line if the expression is one. Panics otherwise.
    #[must_use]
    fn to_line(&self) -> LineExpr {
        if let Self::Line(x) = self {
            x.clone()
        } else {
            panic!("self was not a line");
        }
    }

    /// Returns a point if the expression is one. Panics otherwise.
    #[must_use]
    fn to_complex(&self) -> ComplexExpr {
        if let Self::Complex(x) = self {
            x.clone()
        } else {
            panic!("self was not a complex");
        }
    }

    /// Returns a circle if the expression is one. Panics otherwise.
    #[must_use]
    fn to_circle(&self) -> CircleExpr {
        if let Self::Circle(x) = self {
            x.clone()
        } else {
            panic!("self was not a circle");
        }
    }

    /// Returns a scalar if the expression is one. Panics otherwise.
    fn to_single(&self) -> RealExpr {
        if let Self::This(x) = self {
            x.clone()
        } else {
            panic!("self was not a single expression");
        }
    }
}

impl From<ComplexExpr> for ValueExpr {
    fn from(value: ComplexExpr) -> Self {
        Self::Complex(value)
    }
}

impl From<LineExpr> for ValueExpr {
    fn from(value: LineExpr) -> Self {
        Self::Line(value)
    }
}

impl From<CircleExpr> for ValueExpr {
    fn from(value: CircleExpr) -> Self {
        Self::Circle(value)
    }
}

/// A line with an origin point and a normalized direction vector.
#[derive(Debug, Clone)]
struct LineExpr {
    origin: ComplexExpr,
    direction: ComplexExpr,
}

/// A circle with an origin and a radius.
#[derive(Debug, Clone)]
struct CircleExpr {
    center: ComplexExpr,
    radius: RealExpr,
}

// impl ComplexExpr {
//     /// Create a complex value from a real.
//     #[must_use]
//     fn real(real: CompiledExpr) -> Self {
//         Self {
//             real,
//             imaginary: Context::zero(),
//         }
//     }

//     /// Subtract complex values.
//     #[must_use]
//     fn sub(self, other: Self, context: &mut Context) -> Self {
//         Self {
//             real: context.sub(self.real, other.real),
//             imaginary: context.sub(self.imaginary, other.imaginary),
//         }
//     }

//     /// Add complex values.
//     #[must_use]
//     fn add(self, other: Self, context: &mut Context) -> Self {
//         Self {
//             real: context.add(self.real, other.real),
//             imaginary: context.add(self.imaginary, other.imaginary),
//         }
//     }

//     /// Add a real to a complex.
//     #[must_use]
//     fn add_real(self, other: CompiledExpr, context: &mut Context) -> Self {
//         Self {
//             real: context.add(self.real, other),
//             ..self
//         }
//     }

//     /// Multiply complex values.
//     #[must_use]
//     fn mul(self, other: Self, context: &mut Context) -> Self {
//         // self = a + bi
//         // other = c + di
//         // quotient = (ac - bd) + (ad + bc)i
//         let Self {
//             real: a,
//             imaginary: b,
//         } = self;
//         let Self {
//             real: c,
//             imaginary: d,
//         } = other;

//         let ac = context.mul(a, c);
//         let bd = context.mul(b, d);
//         let bc = context.mul(b, c);
//         let ad = context.mul(a, d);

//         let ac_sub_bd = context.sub(ac, bd);
//         let bc_plus_ad = context.add(bc, ad);

//         Self {
//             real: ac_sub_bd,
//             imaginary: bc_plus_ad,
//         }
//     }

//     /// Divide complex values.
//     #[must_use]
//     fn div(self, other: Self, context: &mut Context) -> Self {
//         // self = a + bi
//         // other = c + di
//         // quotient = ((ac + bd) + (bc - ad)i)/(c^2 + d^2)
//         let Self {
//             real: a,
//             imaginary: b,
//         } = self;
//         let Self {
//             real: c,
//             imaginary: d,
//         } = other;

//         let ac = context.mul(a, c);
//         let bd = context.mul(b, d);
//         let bc = context.mul(b, c);
//         let ad = context.mul(a, d);
//         let c2 = context.mul(c, c);
//         let d2 = context.mul(d, d);

//         let ac_plus_bd = context.add(ac, bd);
//         let bc_sub_ad = context.sub(bc, ad);
//         let c2_plus_d2 = context.add(c2, d2);

//         let real = context.div(ac_plus_bd, c2_plus_d2);
//         let imaginary = context.div(bc_sub_ad, c2_plus_d2);

//         Self { real, imaginary }
//     }

//     /// Multiply a complex by a real.
//     #[must_use]
//     fn mul_real(self, other: CompiledExpr, context: &mut Context) -> Self {
//         Self {
//             real: context.mul(self.real, other),
//             imaginary: context.mul(self.imaginary, other),
//         }
//     }

//     /// Divide a complex by a real.
//     #[must_use]
//     fn div_real(self, other: CompiledExpr, context: &mut Context) -> Self {
//         Self {
//             real: context.div(self.real, other),
//             imaginary: context.div(self.imaginary, other),
//         }
//     }

//     /// Get the magnitude of a complex as vector (distance from 0)
//     fn modulus(self, context: &mut Context) -> CompiledExpr {
//         // |a + bi| = (a^2 + b^2)^0.5
//         let a2 = context.mul(self.real, self.real);
//         let b2 = context.mul(self.imaginary, self.imaginary);
//         let a2_plus_b2 = context.add(a2, b2);
//         context.pow(a2_plus_b2, 0.5)
//     }

//     /// Negate the complex
//     #[must_use]
//     fn neg(self, context: &mut Context) -> Self {
//         Self {
//             real: context.neg(self.real),
//             imaginary: context.neg(self.imaginary),
//         }
//     }

//     /// A ternary operator. If `cond` is true, return `then`, otherwise return `else_`
//     #[must_use]
//     fn ternary(cond: Condition, then: Self, else_: Self, context: &mut Context) -> Self {
//         Self {
//             real: context.ternary(cond, then.real, else_.real),
//             imaginary: context.ternary(cond, then.imaginary, else_.imaginary),
//         }
//     }

//     /// Multiply the complex by `i`. A separate function as it's a simple operation.
//     #[must_use]
//     fn mul_i(self, context: &mut Context) -> Self {
//         Self {
//             real: context.neg(self.imaginary),
//             imaginary: self.real,
//         }
//     }

//     /// Raise the number to a power.
//     #[must_use]
//     fn pow(&self, exp: f64, context: &mut Context) -> Self {
//         let c = context.constant(exp);

//         let a2 = context.mul(self.real, self.real);
//         let b2 = context.mul(self.imaginary, self.imaginary);
//         let a2_plus_b2 = context.add(a2, b2);
//         let a2_plus_b2_to_exp_by_2 = context.pow(a2_plus_b2, exp / 2.0);

//         let arg = context.atan2(self.imaginary, self.real);
//         let c_arg = context.mul(c, arg);
//         let cos_c_arg = context.cos(c_arg);
//         let sin_c_arg = context.sin(c_arg);

//         Self {
//             real: context.mul(a2_plus_b2_to_exp_by_2, cos_c_arg),
//             imaginary: context.mul(a2_plus_b2_to_exp_by_2, sin_c_arg),
//         }
//     }
// }

/// Get a single complex from an iterator over floats.
fn get_complex<I: Iterator<Item = f64>>(value: &mut I) -> Complex {
    Complex::new(value.next().unwrap(), value.next().unwrap())
}

/// Create a figure based on its IR, figure's inputs and
/// computed values for all figure's expressions.
fn get_figure(figure: &crate::script::figure::Figure, values: &[f64]) -> Generated {
    let mut value = values.iter().copied();

    // println!("{:#?}, {values:?}", figure.variables);

    let mut variables = Vec::new();
    for expr in &figure.variables {
        let v = match expr.ty {
            ExprType::Point | ExprType::Number => ValueEnum::Complex(get_complex(&mut value)),
            ExprType::Line => ValueEnum::Line(Line {
                origin: get_complex(&mut value),
                direction: get_complex(&mut value),
            }),
            ExprType::Circle => ValueEnum::Circle(Circle {
                center: get_complex(&mut value),
                radius: value.next().unwrap(),
            }),
        };
        variables.push(Expr {
            ty: expr.ty,
            kind: expr.kind.clone(),
            meta: v,
        });
    }

    let mut entities = Vec::new();
    for ent in &figure.entities {
        let v = match ent {
            EntityKind::PointOnCircle { .. }
            | EntityKind::PointOnLine { .. }
            | EntityKind::FreePoint => ValueEnum::Complex(get_complex(&mut value)),
            EntityKind::DistanceUnit | EntityKind::FreeReal => {
                ValueEnum::Complex(Complex::real(get_complex(&mut value).real))
            }
            EntityKind::Bind(_) => unreachable!(),
        };
        entities.push(Entity {
            kind: ent.clone(),
            meta: v,
        });
    }

    Generated {
        variables,
        entities,
        items: figure.items.clone(),
    }
}
