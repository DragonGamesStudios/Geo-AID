//! The `dst` function

use super::prelude::*;
use crate::{figure::SegmentItem, math::Build, unroll::Convert};
use geo_aid_figure::math_string::MathString;

/// `dst(point, point)` - distance between two points.
pub fn distance_function_pp(
    a: Expr<Point>,
    b: Expr<Point>,
    context: &CompileContext,
    mut display: Properties,
) -> Distance {
    let display_segment = display.get("display_segment").maybe_unset(true);
    let style = display.get("style").maybe_unset(Style::Solid);

    let mut expr = context.distance_pp_display(a, b, display);

    if let Some(node) = &mut expr.node {
        node.set_associated(Associated);
        node.insert_data("display_segment", display_segment);
        node.insert_data("style", style);
    }

    expr.into()
}

/// `dst(point, line)` - distance of a point from a line.
fn distance_function_pl(
    a: Expr<Point>,
    k: Expr<Line>,
    context: &CompileContext,
    mut display: Properties,
) -> Distance {
    let display_segment = display.get("display_segment").maybe_unset(true);
    let style = display.get("style").maybe_unset(Style::Dashed);

    let mut expr = context.distance_pl_display(a, k, display);

    if let Some(node) = &mut expr.node {
        node.set_associated(Associated);
        node.insert_data("display_segment", display_segment);
        node.insert_data("style", style);
    }

    expr.into()
}

/// Convert a point collection to a distance.
fn distance_convert_pc(mut pc: Pc<2>, context: &CompileContext, display: Properties) -> Distance {
    if let Some(node) = pc.node.as_mut() {
        node.root.props = Some(
            node.root
                .props
                .take()
                .unwrap_or_default()
                .merge_with(display),
        );
    }

    pc.0.convert(context).into()
}

/// ```
/// # use geo_aid_figure::Style;
/// struct Associated {
///     display_segment: bool,
///     style: Style
/// }
#[derive(Debug)]
pub struct Associated;

impl BuildAssociated<NumberNode> for Associated {
    fn build_associated(
        self: Box<Self>,
        build: &mut Build,
        associated: &mut HierarchyNode<NumberNode>,
    ) {
        let display_segment = associated
            .get_data("display_segment")
            .unwrap()
            .as_bool()
            .unwrap();
        let style = associated.get_data("style").unwrap().as_style().unwrap();

        if display_segment.unwrap() {
            match &associated.root.expr.data.data {
                NumberData::PointPointDistance(a, b) => {
                    let p_id = build.load(a);
                    let q_id = build.load(b);
                    build.add(SegmentItem {
                        p_id,
                        q_id,
                        label: MathString::new(),
                        style: style.unwrap(),
                    });
                }
                NumberData::PointLineDistance(a, k) => {
                    // Projection
                    let b = Expr::new_spanless(Point::LineLineIntersection(
                        Expr::new_spanless(Line::PerpendicularThrough(
                            k.clone_without_node(),
                            a.clone_without_node(),
                        )),
                        k.clone_without_node(),
                    ));

                    let p_id = build.load(a);
                    let q_id = build.load(&b);
                    build.add(SegmentItem {
                        p_id,
                        q_id,
                        label: MathString::new(),
                        style: style.unwrap(),
                    });
                }
                _ => unreachable!(),
            }
        }
    }
}

/// Register the function
pub fn register(library: &mut Library) {
    library.add(
        Function::new("dst")
            .alias("len")
            .alias_method(ty::collection(2), "dst")
            .alias_method(ty::collection(2), "len")
            .overload(distance_convert_pc)
            .overload(
                |v: Distance, context: &CompileContext, display: Properties| {
                    display.finish(context);
                    v
                },
            )
            .overload(|v: Unitless, context: &CompileContext, display| {
                Distance::from(context.set_unit_display(v.0, unit::DISTANCE, display))
            })
            .overload(distance_function_pp)
            .overload(distance_function_pl)
            .overload(
                |line: Expr<Line>, point: Expr<Point>, context: &CompileContext, display| {
                    distance_function_pl(point, line, context, display)
                },
            ),
    );
}
