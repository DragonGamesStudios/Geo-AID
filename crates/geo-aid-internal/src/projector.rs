//! Converts the generated figure to a ready-to-draw form - [`geo_aid_figure::Figure`].

use crate::geometry;
use crate::geometry::{Circle, Complex, Line, ValueEnum};
pub use geo_aid_figure as figure;
use geo_aid_figure::{
    CircleItem as RenderedCircle, Entity, Expression, Figure, Item as Rendered, Label,
    LineItem as RenderedLine, PointItem as RenderedPoint, Position,
    TwoPointItem as RenderedTwoPoint, VarIndex,
};
use std::f64::consts::PI;
use std::sync::Arc;

use crate::script::figure::{
    CircleItem, Generated, Item, LineItem, PointItem, RayItem, SegmentItem,
};
use crate::script::math::{EntityKind, Expr, ExprType, Flags};

/// Projector context.
struct Projector {
    /// Variables used by the figure
    pub variables: Vec<MathVariable>,
    /// Picture width
    pub width: f64,
    /// Picture height
    pub height: f64,
    /// Segments visible on the picture.
    pub segments: Vec<(Complex, Complex)>,
    /// Circles visible on the picture.
    pub circles: Vec<Circle>,
}

enum SegmentProximity {
    NearA,
    NearB,
    Between
}

impl Projector {
    /// Gets the intersection points of the line with the picture's frame.
    fn get_line_ends(&self, ln_c: Line) -> (Complex, Complex) {
        fn choose_intersection(i: usize, j: usize) -> impl Fn(f64, &[Complex]) -> Complex {
            move |width, intersections| {
                let x = intersections[i];

                if x.real > 0f64 && x.real < width {
                    x
                } else {
                    intersections[j]
                }
            }
        }

        // +--0--+
        // |     |
        // 1     2
        // |     |
        // +--3--+

        let intersections = [
            geometry::get_intersection(
                ln_c,
                geometry::get_line(
                    Complex::new(0.0, self.height),
                    Complex::new(1.0, self.height),
                ),
            ),
            geometry::get_intersection(
                ln_c,
                geometry::get_line(Complex::new(0.0, 0.0), Complex::new(0.0, 1.0)),
            ),
            geometry::get_intersection(
                ln_c,
                geometry::get_line(Complex::new(self.width, 0.0), Complex::new(self.width, 1.0)),
            ),
            geometry::get_intersection(
                ln_c,
                geometry::get_line(Complex::new(0.0, 0.0), Complex::new(1.0, 0.0)),
            ),
        ];

        // If the product of the real and imaginary is negative, line is "going down".
        let a = ln_c.direction.imaginary * ln_c.direction.real;

        #[allow(clippy::cast_precision_loss)]
        if a < 0f64 {
            // There must be one intersection with lines 0/1 and 2/3
            let i1 = choose_intersection(0, 1)(self.width, &intersections);

            let i2 = choose_intersection(3, 2)(self.width, &intersections);

            (i1, i2)
        } else {
            // There must be one intersection with lines 1/3 and 0/2
            let i1 = choose_intersection(3, 1)(self.width, &intersections);

            let i2 = choose_intersection(0, 2)(self.width, &intersections);

            (i1, i2)
        }
    }

    /// Figure out if a point lies on a segment
    #[must_use]
    fn get_segment_proximity((a, b): (Complex, Complex), p: Complex) -> Option<SegmentProximity> {
        // Identifying the "first" point by the real axis.
        let (a, b) = if a.real < b.real { (a, b) } else { (b, a) };
        let ln = geometry::get_line(a, b);
        let distance = geometry::distance_pt_ln(p, ln);

        if distance < 1e-2 {
            if geometry::distance_pt_pt(p, a) < 1e-2 {
                Some(SegmentProximity::NearA)
            } else if geometry::distance_pt_pt(p, b) < 1e-2 {
                Some(SegmentProximity::NearB)
            } else if a.real < p.real && p.real < b.real {
                Some(SegmentProximity::Between)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Find a good label position for a line.
    fn get_line_label_position(&self, (a, b): (Position, Position), min_size: f64) -> Position {
        let (a, b) = (a.into(), b.into());
        let ln = geometry::get_line(a, b);
        // Find all points and intersections on this line.
        // Get either the first, the last or the longest segment.
        // Place the label in the middle.
        let mut intersections = Vec::new();

        for &(p, q) in &self.segments {
            let ln2 = geometry::get_line(p, q);
            let r = geometry::get_intersection(ln2, ln);
            if Self::get_segment_proximity((p, q), r).is_some() {
                intersections.push(r);
            }
        }

        for &k in &self.circles {
            if let Some((a, b)) = geometry::get_lc_intersection(ln, k) {
                
            }
        }
    }

    /// Get the point's label position relative to the point.
    fn get_label_position_rel(&self, point: Complex, min_size: f64) -> Position {
        let mut vectors = Vec::new();

        // Checking the lines for proximity.
        for &(a, b) in &self.segments {
            // Check if the point lies on the line.
            // If so, we have 4 cases:
            // A - point lies close to point A. In that case, we only apply the AB vector.
            // B - point lies close to point B. In that case, we only apply the BA vector.
            // C - point lies on the segment AB. In that case, we apply both vectors.
            // D - point lies far from the segment AB. We do nothing.

            if let Some(proximity) = Self::get_segment_proximity((a, b), point) {
                match proximity {
                    SegmentProximity::NearA => {
                        vectors.push((b - a).normalize());
                    }
                    SegmentProximity::NearB => {
                        vectors.push((a - b).normalize());
                    }
                    SegmentProximity::Between => {
                        let v = (a - b).normalize();
                        vectors.extend([v, -v]);
                    }
                }
            }
        }

        // Checking the circles for associated vectors.
        for &Circle { center, radius } in &self.circles {
            if (geometry::distance_pt_pt(center, point) - radius).abs() < 1e-4 {
                let direction = (center - point).mul_i().normalize();

                vectors.push(direction);
                vectors.push(-direction);
            }
        }

        // Sorting by the complex number argument.
        vectors.sort_by(|a, b| a.arg().partial_cmp(&b.arg()).unwrap());

        let mut vec_iter = vectors.iter();
        vec_iter.next();

        let radius = 15.0;

        if vectors.is_empty() {
            // No vectors associated with the given point.
            Complex::polar(PI / 4.0, radius).into()
        } else if vectors.len() == 1 {
            // Only one vector which is associated with the given point.
            (-radius * vectors.first().copied().unwrap()).into()
        } else {
            let mut flip = false;
            let mut biggest_angle = 0.0;
            // Vectors between which the label should be located.
            let mut label_vectors = (Complex::default(), Complex::default());

            // If there is more than one associated vector.
            for vec in &vectors {
                if let Some(vec_next) = vec_iter.next() {
                    let angle = vec_next.arg() - vec.arg();
                    if angle > biggest_angle {
                        biggest_angle = angle;
                        label_vectors = (*vec, *vec_next);
                    }
                } else {
                    let first = vectors.first().unwrap();
                    let last = vectors.last().unwrap();
                    let angle = 2.0 * PI - (last.arg() - first.arg());
                    if angle > biggest_angle {
                        biggest_angle = angle;
                        label_vectors = (*first, *last);
                        flip = true; // The only case when the label offset will have to be flipped (scale -1)
                    }
                    break;
                }
            }

            // We get the bisector angle.
            let bisector_angle = (label_vectors.1.arg() + label_vectors.0.arg()) / 2.0;

            // This is just the standard complex number formula.
            let bisector_vec = Complex::polar(
                bisector_angle,
                (radius / (biggest_angle / 2.0).sin()).min(radius),
            ) * min_size
                / 500.0;

            // to do -> better scaling
            if flip {
                bisector_vec * -1.0
            } else {
                bisector_vec
            }
            .into()
        }
    }
}

/// Converts a [`VarIndex`] to its value.
trait UnVar<T> {
    /// Returns the actual variable value.
    fn un_var(&self, id: &VarIndex) -> Option<T>;
}

impl UnVar<Complex> for Projector {
    fn un_var(&self, id: &VarIndex) -> Option<Complex> {
        self.variables[id.0].meta.as_complex()
    }
}

impl UnVar<Line> for Projector {
    fn un_var(&self, id: &VarIndex) -> Option<Line> {
        self.variables[id.0].meta.as_line()
    }
}

impl UnVar<Circle> for Projector {
    fn un_var(&self, id: &VarIndex) -> Option<Circle> {
        self.variables[id.0].meta.as_circle()
    }
}

/// A helper trait for projecting (preparing) drawn items.
trait Project<T> {
    type Result;

    /// Prepare the given item for drawing.
    fn project(&mut self, item: T) -> Self::Result;
}

impl Project<Item> for Projector {
    type Result = Rendered;

    fn project(&mut self, item: Item) -> Self::Result {
        match item {
            Item::Point(v) => Rendered::Point(self.project(v)),
            Item::Circle(v) => Rendered::Circle(self.project(v)),
            Item::Line(v) => Rendered::Line(self.project(v)),
            Item::Ray(v) => Rendered::Ray(self.project(v)),
            Item::Segment(v) => Rendered::Segment(self.project(v)),
        }
    }
}

type MathVariable = Expr<ValueEnum>;

impl Project<PointItem> for Projector {
    type Result = RenderedPoint;

    fn project(&mut self, item: PointItem) -> Self::Result {
        RenderedPoint {
            position: <Projector as UnVar<Complex>>::un_var(self, &item.id)
                .unwrap()
                .into(),
            id: item.id,
            display_dot: item.display_dot,
            label: if item.label.is_empty() {
                None
            } else {
                Some(Label {
                    content: item.label,
                    position: Position { x: 0.0, y: 0.0 },
                })
            },
        }
    }
}

impl Project<LineItem> for Projector {
    type Result = RenderedLine;

    fn project(&mut self, item: LineItem) -> Self::Result {
        let ln_c: Line = self.un_var(&item.id).unwrap();
        let points = self.get_line_ends(ln_c);
        self.segments.push(points);

        RenderedLine {
            id: item.id,
            style: item.style,
            points: (points.0.into(), points.1.into()),
            label: if item.label.is_empty() {
                None
            } else {
                Some(Label {
                    content: item.label,
                    position: Position { x: 0.0, y: 0.0 },
                })
            },
        }
    }
}

impl Project<SegmentItem> for Projector {
    type Result = RenderedTwoPoint;

    fn project(&mut self, item: SegmentItem) -> Self::Result {
        let seg1 = self.un_var(&item.p_id).unwrap();
        let seg2 = self.un_var(&item.q_id).unwrap();
        self.segments.push((seg1, seg2));

        RenderedTwoPoint {
            points: (seg1.into(), seg2.into()),
            p_id: item.p_id,
            q_id: item.q_id,
            style: item.style,
            label: if item.label.is_empty() {
                None
            } else {
                Some(Label {
                    content: item.label,
                    position: Position { x: 0.0, y: 0.0 },
                })
            },
        }
    }
}

impl Project<RayItem> for Projector {
    type Result = RenderedTwoPoint;

    fn project(&mut self, item: RayItem) -> Self::Result {
        let ray_a = self.un_var(&item.p_id).unwrap();
        let ray_b = self.un_var(&item.q_id).unwrap();

        let line = geometry::get_line(ray_a, ray_b);
        let ends = self.get_line_ends(line);

        let vec1 = (ray_b - ray_a).normalize();
        let vec2 = (ends.1 - ray_a).normalize();
        let second_point;

        if vec1.real < 0.5 && vec1.real > -0.5 {
            if (vec1.imaginary - vec2.imaginary).abs() < 1e-4 {
                second_point = ends.1;
            } else {
                second_point = ends.0;
            }
        } else if (vec1.real - vec2.real).abs() < 1e-4 {
            second_point = ends.1;
        } else {
            second_point = ends.0;
        }
        self.segments.push((ray_a, second_point));

        RenderedTwoPoint {
            points: (ray_a.into(), second_point.into()),
            p_id: item.p_id,
            q_id: item.q_id,
            style: item.style,
            label: if item.label.is_empty() {
                None
            } else {
                Some(Label {
                    content: item.label,
                    position: Position { x: 0.0, y: 0.0 },
                })
            },
        }
    }
}

impl Project<CircleItem> for Projector {
    type Result = RenderedCircle;

    fn project(&mut self, item: CircleItem) -> Self::Result {
        let circle: Circle = self.un_var(&item.id).unwrap();
        let center = circle.center;
        let radius = circle.radius.abs();
        self.circles.push(circle);

        RenderedCircle {
            id: item.id,
            center: center.into(),
            radius,
            style: item.style,
            label: if item.label.is_empty() {
                None
            } else {
                Some(Label {
                    content: item.label,
                    position: Position { x: 0.0, y: 0.0 },
                })
            },
        }
    }
}

// /// Function getting the points defining the angle from the Expression defining it.
// ///
// /// # Panics
// /// If given invalid data.
// fn get_angle_points(
//     angle: &ExprKind,
//     variables: &[Expr<ValueEnum>],
// ) -> (Complex, Complex, Complex) {
//     match angle {
//         ExprKind::ThreePointAngle { p, q, r } => {
//             let arm1 = variables[p.0].meta.as_complex().unwrap();
//             let origin = variables[q.0].meta.as_complex().unwrap();
//             let arm2 = variables[r.0].meta.as_complex().unwrap();
//
//             (arm1, origin, arm2)
//         }
//         ExprKind::ThreePointAngleDir { p, q, r } => {
//             let arm1 = variables[p.0].meta.as_complex().unwrap();
//             let origin = variables[q.0].meta.as_complex().unwrap();
//             let arm2 = variables[r.0].meta.as_complex().unwrap();
//
//             (arm1, origin, arm2)
//         }
//         ExprKind::TwoLineAngle { k, l } => {
//             let ev_ln1 = variables[k.0].meta.as_line().unwrap();
//             let ev_ln2 = variables[l.0].meta.as_line().unwrap();
//
//             let origin = geometry::get_intersection(ev_ln1, ev_ln2);
//
//             (
//                 ev_ln1.origin + ev_ln1.direction,
//                 origin,
//                 ev_ln2.origin + ev_ln2.direction,
//             )
//         }
//         _ => unreachable!(),
//     }
// }

/// Represents the transform used by the projector to fit all
/// items on the canvas with a proper margin.
struct Transform {
    /// The offset to apply to all items
    offset: Complex,
    /// The scale to apply to all items.
    scale: f64,
    /// The margin - a translation to apply to all items.
    margin: Complex,
}

impl Transform {
    /// Translates generator coordinates to projector coordinates.
    fn transform_point(&self, pt: Complex) -> Complex {
        (pt + self.offset) * self.scale + self.margin
    }

    /// Translate a generator-space line to figure-space line
    fn transform_line(&self, ln: Line) -> Line {
        Line {
            origin: self.transform_point(ln.origin),
            ..ln
        }
    }

    /// Translate a generator-space circle to figure-space circle.
    fn transform_circle(&self, circle: Circle) -> Circle {
        Circle {
            center: self.transform_point(circle.center),
            radius: self.transform_dst(circle.radius),
        }
    }

    /// Translate a generator-space distance to figure-space distance
    fn transform_dst(&self, dst: f64) -> f64 {
        dst * self.scale
    }
}

// /// Function that outputs the vector containing the angles.
// ///
// /// # Panics
// /// It shouldn't panic.
// fn angles(
//     figure: &Figure,
//     offset: Complex,
//     scale: f64,
//     size: Complex,
//     args: &EvaluationArgs,
// ) -> Vec<RenderedAngle> {
//     let mut blueprint_angles = Vec::new();
//     for ang in &figure.angles {
//         let angle_points = get_angle_points(&ang.0, args);
//         blueprint_angles.push(RenderedAngle {
//             label: String::new(),
//             points: (
//                 transform(offset, scale, size, angle_points.0),
//                 transform(offset, scale, size, angle_points.1),
//                 transform(offset, scale, size, angle_points.2),
//             ),
//             no_arcs: ang.1,
//             expr: Arc::clone(&ang.0),
//             angle_value: ang.0.evaluate(args),
//             style: ang.2,
//         });
//     }
//     blueprint_angles
// }

/// Takes the figure and rendered adjustables and attempts to design a figure that can then be rendered in chosen format.
///
/// # Panics
/// Any panic is a bug.
#[allow(clippy::too_many_lines)]
pub fn project(figure: Generated, _flags: &Arc<Flags>, canvas_size: (f64, f64)) -> Figure {
    let mut entities: Vec<_> = figure.entities;
    let mut expressions: Vec<_> = figure.variables;
    let items = figure.items;

    let mut points = Vec::new();

    for item in &items {
        match item {
            Item::Point(pt) => points.push(expressions[pt.id.0].meta.as_complex().unwrap()),
            Item::Circle(c) => {
                let circle = expressions[c.id.0].meta.as_circle().unwrap();

                points.extend([
                    circle.center - circle.radius,
                    circle.center + circle.radius,
                    circle.center - circle.radius * Complex::i(),
                    circle.center + circle.radius * Complex::i(),
                ]);
            }
            _ => (),
        }
    }

    // Frame top left point.
    let top_left = Complex::new(
        points
            .iter()
            .map(|pt| pt.real)
            .reduce(f64::min)
            .unwrap_or_default(),
        points
            .iter()
            .map(|pt| pt.imaginary)
            .reduce(f64::min)
            .unwrap_or_default(),
    );

    let offset = -top_left;

    // Frame bottom right point.
    let furthest = Complex::new(
        points
            .iter()
            .map(|pt| pt.real)
            .reduce(f64::max)
            .unwrap_or_default(),
        points
            .iter()
            .map(|pt| pt.imaginary)
            .reduce(f64::max)
            .unwrap_or_default(),
    );

    // println!("{top_left}/{furthest}");
    let mut total_size = furthest + offset;
    total_size.real = f64::max(total_size.real, 0.1);
    total_size.imaginary = f64::max(total_size.imaginary, 0.1);

    #[allow(clippy::cast_precision_loss)]
    let size1 = Complex::new(canvas_size.0, canvas_size.1);
    let size09 = size1 * 0.9;
    let size005 = size1 * 0.05;
    let min_size = f64::min(canvas_size.0, canvas_size.1);

    // The scaled frame should be at most (and equal for at least one dimension) 90% of the size of the desired image (margins for rendering).
    let scale = f64::min(
        size09.real / total_size.real,
        size09.imaginary / total_size.imaginary,
    );

    let transform = Transform {
        offset,
        scale,
        margin: size005,
    };

    let ent_types: Vec<_> = entities
        .iter()
        .map(|t| t.get_type(&expressions, &entities))
        .collect();
    for (ent, ty) in entities.iter_mut().zip(ent_types) {
        match &mut ent.meta {
            ValueEnum::Circle(circle) => *circle = transform.transform_circle(*circle),
            ValueEnum::Line(line) => *line = transform.transform_line(*line),
            ValueEnum::Complex(complex) => match ty {
                ExprType::Point => *complex = transform.transform_point(*complex),
                ExprType::Number => {
                    if matches!(ent.kind, EntityKind::DistanceUnit) {
                        complex.real = transform.transform_dst(complex.real);
                    }
                }
                _ => unreachable!(),
            },
        }
    }

    let expr_types: Vec<_> = expressions
        .iter()
        .map(|t| t.get_type(&expressions, &entities))
        .collect();
    for (expr, ty) in expressions.iter_mut().zip(expr_types) {
        match &mut expr.meta {
            ValueEnum::Circle(circle) => *circle = transform.transform_circle(*circle),
            ValueEnum::Line(line) => *line = transform.transform_line(*line),
            ValueEnum::Complex(complex) => {
                if ExprType::Point == ty {
                    *complex = transform.transform_point(*complex);
                }
            }
        }
    }

    // println!("Scale: {scale}");
    // println!("Frame size: {total_size}");

    // let points: Vec<Complex> = points.into_iter().map(|x| x * scale + size005).collect();
    let mut projector = Projector {
        variables: expressions,
        width: size1.real,
        height: size1.imaginary,
        segments: Vec::new(),
        circles: Vec::new(),
    };

    let mut rendered: Vec<_> = items.into_iter().map(|v| projector.project(v)).collect();

    for point in rendered.iter_mut().filter_map(Rendered::as_point_mut) {
        let pos = point.position;
        if let Some(label) = &mut point.label {
            label.position = pos + projector.get_label_position_rel(pos.into(), min_size);
        }
    }

    for ln in rendered.iter_mut().filter_map(Rendered::as_line_mut) {
        if let Some(label) = &mut ln.label {
            label.position = projector.get_line_label_position(ln.points, min_size);
        }
    }

    Figure {
        width: canvas_size.0,
        height: canvas_size.1,
        expressions: projector
            .variables
            .into_iter()
            .map(|expr| Expression {
                hint: expr.meta.into(),
                kind: expr.kind.into(),
            })
            .collect(),
        entities: entities
            .into_iter()
            .map(|ent| Entity {
                hint: ent.meta.into(),
                kind: ent.kind.into(),
            })
            .collect(),
        items: rendered,
    }
}
