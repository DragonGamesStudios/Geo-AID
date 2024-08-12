use std::f64::consts::PI;
use num_traits::ToPrimitive;
use geo_aid_figure::VarIndex;
use geo_aid_math::{Comparison, ComparisonKind, Condition, Context, Expr as CompiledExpr};
use crate::geometry::{Circle, Complex, Line, ValueEnum};
use crate::script::figure::Generated;
use crate::script::math::{Entity, EntityKind, Expr, ExprKind, ExprType, Intermediate, Rule, RuleKind};

pub type FigureFn = Box<dyn for<'a> Fn(&'a [f64]) -> Generated>;

pub struct Compiled {
    pub figure_fn: FigureFn,
    pub errors: Vec<CompiledExpr>,
    pub context: Context,
    pub input_count: usize
}

pub fn compile(intermediate: &Intermediate) -> Compiled {
    let inputs = intermediate.adjusted.entities
        .iter()
        .map(|ent| match ent {
            EntityKind::FreePoint => 2,
            EntityKind::PointOnLine { .. }
            | EntityKind::PointOnCircle { .. }
            | EntityKind::FreeReal
            | EntityKind::DistanceUnit => 1,
            EntityKind::Bind(_) => unreachable!()
        })
        .sum();

    // for (i, var) in intermediate.figure.variables.iter().enumerate() {
    //     println!("[{i}] = {:?}", var.kind);
    // }

    let mut compiler = Compiler::new(inputs, &intermediate.adjusted.entities, &intermediate.figure.variables);

    let mut exprs = Vec::new();
    for value in &compiler.variables {
        match value {
            ValueExpr::This(this) => exprs.push(*this),
            ValueExpr::Line(line) => exprs.extend([
                line.origin.real,
                line.origin.imaginary,
                line.direction.real,
                line.direction.imaginary
            ]),
            ValueExpr::Complex(complex) => exprs.extend([
                complex.real,
                complex.imaginary,
            ]),
            ValueExpr::Circle(circle) => exprs.extend([
                circle.center.real,
                circle.center.imaginary,
                circle.radius
            ])
        }
    }

    let outs_len = exprs.len();
    let exprs = compiler.context.compute(exprs);
    let fig = intermediate.figure.clone();
    let figure_fn = Box::new(move |inputs: &[f64]| {
        let mut outputs = Vec::new();
        outputs.resize(outs_len, 0.0);
        exprs.call(inputs, outputs.as_mut_slice());

        get_figure(&fig, inputs, &outputs)
    });

    // Reset the compiler.
    compiler = Compiler::new(inputs, &intermediate.adjusted.entities, &intermediate.adjusted.variables);
    let rule_errors: Vec<_> = intermediate.adjusted.rules
        .iter()
        .map(|rule| (rule, compiler.compile_rule(rule)))
        .collect();

    let mut entity_errors = [Context::zero()].repeat(intermediate.adjusted.entities.len());
    for (rule, quality) in rule_errors {
        for ent in &rule.entities {
            entity_errors[ent.0] = compiler.context.add(entity_errors[ent.0], quality);
        }
    }

    // For now, this is how we calculate errors

    Compiled {
        figure_fn,
        errors: entity_errors,
        context: compiler.context,
        input_count: inputs
    }
}

struct Compiler<'r> {
    entities: &'r [EntityKind],
    context: Context,
    variables: Vec<ValueExpr>,
    adjustables: Vec<ValueExpr>
}

impl<'r> Compiler<'r> {
    #[must_use]
    pub fn new(inputs: usize, entities: &'r [EntityKind], variables: &[Expr<()>]) -> Self {
        let mut adjustables = Vec::new();
        let context = Context::new(inputs);

        let mut index = 0;
        for ent in entities {
            match ent {
                EntityKind::FreePoint => {
                    adjustables.push(ValueExpr::Complex(ComplexExpr {
                        real: context.input(index),
                        imaginary: context.input(index + 1)
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
                EntityKind::Bind(_) => unreachable!()
            }
        }

        let mut s = Self {
            entities,
            context: Context::new(inputs),
            variables: Vec::new(),
            adjustables
        };

        for var in variables {
            let expr = s.compile_value(var);
            s.variables.push(expr);
        }

        s
    }

    fn gt(&mut self, a: &VarIndex, b: &VarIndex) -> CompiledExpr {
        let a = self.variables[a.0].to_complex().real;
        let b = self.variables[b.0].to_complex().real;
        let abs_b = self.context.abs(b);
        let one_tenth = self.context.constant(0.1);
        let abs_b_plus_01 = self.context.add(abs_b, one_tenth);
        let offset = self.context.mul(abs_b_plus_01, one_tenth);
        let a_minus_b = self.context.sub(a, b);
        let pre_square = self.context.sub(
            a_minus_b,
            offset
        );
        self.context.mul(pre_square, pre_square)
    }

    fn compile_rule_kind(&mut self, kind: &RuleKind) -> CompiledExpr {
        match kind {
            RuleKind::PointEq(a, b)
            | RuleKind::NumberEq(a, b) => {
                // Weirdly, enough, these two are actually the same, right now
                let a = self.variables[a.0].to_complex();
                let b = self.variables[b.0].to_complex();
                let a_minus_b = a.sub(b, &mut self.context);
                let real2 = self.context.mul(a_minus_b.real, a_minus_b.real);
                let im2 = self.context.mul(a_minus_b.imaginary, a_minus_b.imaginary);
                let mag = self.context.add(real2, im2);
                let five = self.context.constant(5.0);
                self.context.mul(mag, five)
            }
            RuleKind::Lt(b, a)
            | RuleKind::Gt(a, b) => self.gt(a, b),
            RuleKind::Alternative(rules) => {
                // necessary because borrowing
                let qualities: Vec<_> = rules
                    .iter()
                    .map(|rule| self.compile_rule_kind(rule))
                    .collect();

                qualities
                    .into_iter()
                    .reduce(|a, b| self.context.min(a, b))
                    .unwrap()
            }
            RuleKind::Invert(q) => {
                let q = self.compile_rule_kind(q);
                self.context.div(Context::one(), q)
            }
            RuleKind::Bias => Context::zero() // Bias in this approach doesn't really do anything
        }
    }

    fn compile_rule(&mut self, rule: &Rule) -> CompiledExpr {
        let quality = self.compile_rule_kind(&rule.kind);
        let weight = self.context.constant(rule.weight.to_complex().real);
        self.context.mul(quality, weight)
    }

    fn compile_sum(&mut self, value: &[VarIndex]) -> ComplexExpr {
        value
            .iter()
            .map(|i| self.adjustables[i.0].to_complex())
            .reduce(|a, b| a.add(b, &mut self.context))
            .unwrap_or(ComplexExpr {
                real: Context::zero(),
                imaginary: Context::zero()
            })
    }

    // We'll assume all previous values are already handled.
    #[allow(clippy::too_many_lines)]
    fn compile_value(&mut self, value: &Expr<()>) -> ValueExpr {
        match &value.kind {
            ExprKind::Entity { id } => {
                let kind = self.entities[id.0].clone();
                match kind {
                    EntityKind::FreePoint => self.adjustables[id.0],
                    EntityKind::PointOnLine { line } => {
                        let line = self.variables[line.0].to_line();
                        let offset = self.adjustables[id.0].to_single();

                        let offset_times_dir = line.direction.mul_real(offset, &mut self.context);
                        line.origin.add(offset_times_dir, &mut self.context).into()
                    }
                    EntityKind::PointOnCircle { circle } => {
                        let circle = self.variables[circle.0].to_circle();
                        let theta = self.adjustables[id.0].to_single();
                        let two_pi = self.context.constant(2.0 * PI);
                        let theta = self.context.mul(theta, two_pi);

                        let point_rel = ComplexExpr {
                            real: self.context.cos(theta),
                            imaginary: self.context.sin(theta)
                        };
                        let point_rel = point_rel.mul_real(circle.radius, &mut self.context);

                        circle.center.add(point_rel, &mut self.context).into()
                    }
                    EntityKind::DistanceUnit | EntityKind::FreeReal => {
                        ComplexExpr::real(self.adjustables[id.0].to_single()).into()
                    }
                    EntityKind::Bind(_) => unreachable!()
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
                let a = k.origin;
                let b = k.direction;
                let c = l.origin;
                let d = l.direction;

                let b_by_d = b.div(d, &mut self.context);
                let a_sub_c = a.sub(c, &mut self.context);
                let a_sub_c_by_d = a_sub_c.div(d, &mut self.context);
                let quotient = self.context.div(a_sub_c_by_d.imaginary, b_by_d.imaginary);
                let b_times_quotient = b.mul_real(quotient, &mut self.context);

                a.sub(b_times_quotient, &mut self.context).into()
            }
            ExprKind::AveragePoint { items } => {
                let sum = self.compile_sum(items);

                let len = self.context.constant(items.len() as f64);
                sum.div_real(len, &mut self.context).into()
            }
            ExprKind::CircleCenter { circle } => self.variables[circle.0].to_circle().center.into(),
            ExprKind::Sum { plus, minus } => {
                let plus = self.compile_sum(plus);
                let minus = self.compile_sum(minus);

                plus.sub(minus, &mut self.context).into()
            }
            ExprKind::Product { times, by } => {
                let times = times
                    .iter()
                    .map(|i| self.adjustables[i.0].to_complex())
                    .reduce(|a, b| a.mul(b, &mut self.context))
                    .unwrap();

                let by = by
                    .iter()
                    .map(|i| self.adjustables[i.0].to_complex())
                    .reduce(|a, b| a.mul(b, &mut self.context))
                    .unwrap();

                times.div(by, &mut self.context).into()
            }
            ExprKind::Const { value } => {
                let value = value.to_complex();
                ComplexExpr {
                    real: self.context.constant(value.real),
                    imaginary: self.context.constant(value.imaginary)
                }.into()
            }
            ExprKind::PartialPower { value, exponent } => {
                let value = self.variables[value.0].to_complex();
                let exp = exponent.to_f64().unwrap();

                ComplexExpr {
                    real: self.context.pow(value.real, exp),
                    imaginary: self.context.pow(value.imaginary, exp),
                }.into()
            }
            ExprKind::PointPointDistance { p, q } => {
                let p = self.variables[p.0].to_complex();
                let q = self.variables[q.0].to_complex();

                let p_minus_q = p.sub(q, &mut self.context);
                ComplexExpr {
                    real: p_minus_q.modulus(&mut self.context),
                    imaginary: Context::zero()
                }.into()
            }
            ExprKind::PointLineDistance { point, line } => {
                // ((point - line.origin) / line.direction).imaginary.abs()
                let point = self.variables[point.0].to_complex();
                let line = self.variables[line.0].to_line();

                let point_minus_line_origin = point.sub(line.origin, &mut self.context);
                let that_by_direction = point_minus_line_origin.div(line.direction, &mut self.context);
                let real = self.context.abs(that_by_direction.imaginary);
                ComplexExpr::real(real).into()
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

                let arm1_vec = p.sub(q, &mut self.context);
                let arm2_vec = r.sub(q, &mut self.context);

                let dot_product_alpha = self.context.mul(arm1_vec.real, arm2_vec.real);
                let dot_product_beta = self.context.mul(arm1_vec.imaginary, arm2_vec.imaginary);
                let dot_product = self.context.add(
                    dot_product_alpha, dot_product_beta
                );
                let mag1 = arm1_vec.modulus(&mut self.context);
                let mag2 = arm2_vec.modulus(&mut self.context);
                let mag_product = self.context.mul(mag1, mag2);
                let quotient = self.context.div(dot_product, mag_product);
                ComplexExpr::real(self.context.acos(quotient)).into()
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

                let arm1_vec = p.sub(q, &mut self.context);
                let arm2_vec = r.sub(q, &mut self.context);

                let rotated = arm2_vec.div(arm1_vec, &mut self.context);
                ComplexExpr::real(self.context.atan2(rotated.imaginary, rotated.real)).into()
            }
            ExprKind::TwoLineAngle { k, l } => {
                // (k.direction / l.direction).arg().abs()
                let k = self.variables[k.0].to_line();
                let l = self.variables[l.0].to_line();
                let quotient = k.direction.div(l.direction, &mut self.context);
                let arg = self.context.atan2(quotient.imaginary, quotient.real);
                let abs = self.context.abs(arg);
                ComplexExpr::real(abs).into()
            }
            ExprKind::PointX { point } => {
                let point = self.variables[point.0].to_complex();
                ComplexExpr::real(point.real).into()
            }
            ExprKind::PointY { point } => {
                let point = self.variables[point.0].to_complex();
                ComplexExpr::real(point.imaginary).into()
            }
            ExprKind::PointPoint { p, q } => {
                let p = self.variables[p.0].to_complex();
                let q = self.variables[q.0].to_complex();
                let p_minus_q = p.sub(q, &mut self.context);
                let mag = p_minus_q.modulus(&mut self.context);
                let normalized = p_minus_q.div_real(mag, &mut self.context);
                LineExpr {
                    origin: p,
                    direction: normalized
                }.into()
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

                let a = arm1.sub(origin, &mut self.context);
                let b = arm2.sub(origin, &mut self.context);
                let ab = a.mul(b, &mut self.context);

                // sqrt_norm time
                let minus_ab = ab.neg(&mut self.context);

                let condition = Condition::Comparison(Comparison {
                    a: ab.real,
                    b: Context::zero(),
                    kind: ComparisonKind::Gt
                });
                let self_ = ComplexExpr::ternary(condition, ab, minus_ab, &mut self.context);

                let r = self_.modulus(&mut self.context);
                let self_plus_r = self_.add_real(r, &mut self.context);
                let mag = self_plus_r.modulus(&mut self.context);
                let normalized = self_plus_r.div_real(mag, &mut self.context);
                let normalized_mul_i = normalized.mul_i(&mut self.context);

                // Another ternary
                let direction = ComplexExpr::ternary(condition, normalized, normalized_mul_i, &mut self.context);

                LineExpr {
                    origin,
                    direction
                }.into()
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
                    direction: line.direction.mul_i(&mut self.context)
                }.into()
            }
            ExprKind::ConstructCircle { center, radius } => {
                let center = self.variables[center.0].to_complex();
                let radius = self.variables[radius.0].to_complex();

                CircleExpr {
                    center,
                    radius: radius.real
                }.into()
            }
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
enum ValueExpr {
    This(CompiledExpr),
    Line(LineExpr),
    Complex(ComplexExpr),
    Circle(CircleExpr)
}

impl ValueExpr {
    #[must_use]
    fn to_line(self) -> LineExpr {
        if let Self::Line(x) = self {
            x
        } else {
            panic!("self was not a line");
        }
    }

    #[must_use]
    fn to_complex(self) -> ComplexExpr {
        if let Self::Complex(x) = self {
            x
        } else {
            panic!("self was not a complex");
        }
    }

    #[must_use]
    fn to_circle(self) -> CircleExpr {
        if let Self::Circle(x) = self {
            x
        } else {
            panic!("self was not a circle");
        }
    }

    fn to_single(self) -> CompiledExpr {
        if let Self::This(x) = self {
            x
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

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
struct LineExpr {
    origin: ComplexExpr,
    direction: ComplexExpr
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
struct CircleExpr {
    center: ComplexExpr,
    radius: CompiledExpr
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
struct ComplexExpr {
    real: CompiledExpr,
    imaginary: CompiledExpr
}

impl ComplexExpr {
    #[must_use]
    fn real(real: CompiledExpr) -> Self {
        Self {
            real,
            imaginary: Context::zero()
        }
    }

    #[must_use]
    fn sub(self, other: Self, context: &mut Context) -> Self {
        Self {
            real: context.sub(self.real, other.real),
            imaginary: context.sub(self.imaginary, other.imaginary)
        }
    }

    #[must_use]
    fn add(self, other: Self, context: &mut Context) -> Self {
        Self {
            real: context.add(self.real, other.real),
            imaginary: context.add(self.imaginary, other.imaginary)
        }
    }

    #[must_use]
    fn add_real(self, other: CompiledExpr, context: &mut Context) -> Self {
        Self {
            real: context.add(self.real, other),
            ..self
        }
    }

    #[must_use]
    fn mul(self, other: Self, context: &mut Context) -> Self {
        // self = a + bi
        // other = c + di
        // quotient = (ac - bd) + (ad + bc)i
        let Self { real: a, imaginary: b } = self;
        let Self { real: c, imaginary: d } = other;

        let ac = context.mul(a, c);
        let bd = context.mul(b, d);
        let bc = context.mul(b, c);
        let ad = context.mul(a, d);

        let ac_sub_bd = context.sub(ac, bd);
        let bc_plus_ad = context.add(bc, ad);

        Self {
            real: ac_sub_bd,
            imaginary: bc_plus_ad
        }
    }

    #[must_use]
    fn div(self, other: Self, context: &mut Context) -> Self {
        // self = a + bi
        // other = c + di
        // quotient = ((ac + bd) + (bc - ad)i)/(c^2 + d^2)
        let Self { real: a, imaginary: b } = self;
        let Self { real: c, imaginary: d } = other;

        let ac = context.mul(a, c);
        let bd = context.mul(b, d);
        let bc = context.mul(b, c);
        let ad = context.mul(a, d);
        let c2 = context.mul(c, c);
        let d2 = context.mul(d, d);

        let ac_plus_bd = context.add(ac, bd);
        let bc_sub_ad = context.sub(bc, ad);
        let c2_plus_d2 = context.add(c2, d2);

        let real = context.div(ac_plus_bd, c2_plus_d2);
        let imaginary = context.div(bc_sub_ad, c2_plus_d2);

        Self {
            real,
            imaginary
        }
    }

    #[must_use]
    fn mul_real(self, other: CompiledExpr, context: &mut Context) -> Self {
        Self {
            real: context.mul(self.real, other),
            imaginary: context.mul(self.imaginary, other)
        }
    }

    #[must_use]
    fn div_real(self, other: CompiledExpr, context: &mut Context) -> Self {
        Self {
            real: context.div(self.real, other),
            imaginary: context.div(self.imaginary, other)
        }
    }

    fn modulus(self, context: &mut Context) -> CompiledExpr {
        // |a + bi| = (a^2 + b^2)^0.5
        let a2 = context.mul(self.real, self.real);
        let b2 = context.mul(self.imaginary, self.imaginary);
        let a2_plus_b2 = context.add(a2, b2);
        context.pow(a2_plus_b2, 0.5)
    }

    #[must_use]
    fn neg(self, context: &mut Context) -> Self {
        Self {
            real: context.neg(self.real),
            imaginary: context.neg(self.imaginary)
        }
    }

    #[must_use]
    fn ternary(cond: Condition, then: Self, else_: Self, context: &mut Context) -> Self {
        Self {
            real: context.ternary(cond, then.real, else_.real),
            imaginary: context.ternary(cond, then.imaginary, else_.imaginary)
        }
    }

    #[must_use]
    fn mul_i(self, context: &mut Context) -> Self {
        Self {
            real: context.neg(self.imaginary),
            imaginary: self.real
        }
    }
}

fn get_complex<I: Iterator<Item = f64>>(value: &mut I) -> Complex {
    Complex::new(
        value.next().unwrap(), value.next().unwrap()
    )
}

fn get_figure(figure: &crate::script::figure::Figure, inputs: &[f64], values: &[f64]) -> Generated {
    let mut value = values.iter().copied();

    // println!("{:#?}, {values:?}", figure.variables);

    let mut variables = Vec::new();
    for expr in &figure.variables {
        let v = match expr.ty {
            ExprType::Point | ExprType::Number => ValueEnum::Complex(get_complex(&mut value)),
            ExprType::Line => ValueEnum::Line(Line {
                origin: get_complex(&mut value),
                direction: get_complex(&mut value)
            }),
            ExprType::Circle => ValueEnum::Circle(Circle {
                center: get_complex(&mut value),
                radius: value.next().unwrap()
            }),
        };
        variables.push(Expr {
            ty: expr.ty,
            kind: expr.kind.clone(),
            meta: v,
        });
    }

    let mut input = inputs.iter().copied();

    let mut entities = Vec::new();
    for ent in &figure.entities {
        let v = match ent {
            EntityKind::FreePoint => ValueEnum::Complex(get_complex(&mut input)),
            EntityKind::PointOnCircle {..}
            | EntityKind::PointOnLine {..}
            | EntityKind::DistanceUnit
            | EntityKind::FreeReal => ValueEnum::Complex(Complex::real(input.next().unwrap())),
            EntityKind::Bind(_) => unreachable!()
        };
        entities.push(Entity { kind: ent.clone(), meta: v });
    }

    Generated {
        variables,
        entities,
        items: figure.items.clone(),
    }
}