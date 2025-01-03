/// The `angle` function
use crate::{
    figure::{LineItem, RayItem, SegmentItem},
    math::Build,
};

use super::prelude::*;
use geo_aid_figure::math_string::MathString;

/// angle(point, point, point) - angle delimited by 3 points.
fn angle_function_ppp(
    a: Expr<Point>,
    b: Expr<Point>,
    c: Expr<Point>,
    context: &CompileContext,
    mut display: Properties,
) -> Angle {
    let display_arms = display.get("display_arms").maybe_unset(true);
    let arms_style = display.get("arms_style").maybe_unset(Style::default());
    let arms_type = display.get("arms_type").maybe_unset(LineType::Segment);

    let mut expr = context.angle_ppp_display(a, b, c, display);

    if let Some(node) = &mut expr.node {
        node.insert_data("display_arms", display_arms);
        node.insert_data("arms_style", arms_style);
        node.insert_data("arms_type", arms_type);

        node.set_associated(Associated);
    }
    expr.into()
}

/// ```
/// # use geo_aid_figure::Style;
/// # use geo_aid_script::unroll::figure::LineType;
/// struct Associated {
///     display_arms: bool,
///     arms_style: Style,
///     amrs_type: LineType
/// }
/// ```
#[derive(Debug)]
pub struct Associated;

/// Helper function for adding the angle's arms to the figure
pub fn display_angle_arms(
    build: &mut Build,
    a_expr: &Expr<Point>,
    b_expr: &Expr<Point>,
    c_expr: &Expr<Point>,
    arms_type: LineType,
    arms_style: Style,
) {
    let a = build.load(a_expr);
    let b = build.load(b_expr);
    let c = build.load(c_expr);

    match arms_type {
        LineType::Line => {
            let line_a = Expr::new_spanless(Line::LineFromPoints(
                b_expr.clone_without_node(),
                a_expr.clone_without_node(),
            ));
            let line_c = Expr::new_spanless(Line::LineFromPoints(
                b_expr.clone_without_node(),
                c_expr.clone_without_node(),
            ));

            let id = build.load(&line_a);
            build.add(LineItem {
                id,
                label: MathString::new(),
                style: arms_style,
            });
            let id = build.load(&line_c);
            build.add(LineItem {
                id,
                label: MathString::new(),
                style: arms_style,
            });
        }
        LineType::Ray => {
            build.add(RayItem {
                p_id: b.clone(),
                q_id: a,
                label: MathString::new(),
                style: arms_style,
            });
            build.add(RayItem {
                p_id: b,
                q_id: c,
                label: MathString::new(),
                style: arms_style,
            });
        }
        LineType::Segment => {
            build.add(SegmentItem {
                p_id: b.clone(),
                q_id: a,
                label: MathString::new(),
                style: arms_style,
            });
            build.add(SegmentItem {
                p_id: b,
                q_id: c,
                label: MathString::new(),
                style: arms_style,
            });
        }
    }
}

impl BuildAssociated<NumberNode> for Associated {
    fn build_associated(
        self: Box<Self>,
        build: &mut Build,
        associated: &mut HierarchyNode<NumberNode>,
    ) {
        let display_arms = associated
            .get_data("display_arms")
            .unwrap()
            .as_bool()
            .unwrap()
            .unwrap();

        let arms_style = associated
            .get_data("arms_style")
            .unwrap()
            .as_style()
            .unwrap()
            .unwrap();

        let arms_type = associated
            .get_data("arms_type")
            .unwrap()
            .as_line_type()
            .unwrap()
            .unwrap();

        if display_arms {
            match &associated.root.expr.data.data {
                NumberData::ThreePointAngle(a_expr, b_expr, c_expr)
                | NumberData::ThreePointAngleDir(a_expr, b_expr, c_expr) => {
                    display_angle_arms(build, a_expr, b_expr, c_expr, arms_type, arms_style);
                }
                _ => unreachable!(),
            }
        }
    }
}

/// angle(line, line) - angle between two lines.
fn angle_function_ll(
    k: Expr<Line>,
    l: Expr<Line>,
    context: &CompileContext,
    display: Properties,
) -> Angle {
    context.angle_ll_display(k, l, display).into()
}

/// Register the function
pub fn register(library: &mut Library) {
    library.add(
        Function::new("angle")
            .overload(|mut col: Pc<3>, context: &CompileContext, display| {
                angle_function_ppp(
                    index!(node col,0),
                    index!(node col,1),
                    index!(node col,2),
                    context,
                    display,
                )
            })
            .overload(angle_function_ppp)
            .overload(angle_function_ll),
    );
}
