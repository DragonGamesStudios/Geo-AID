//! Functions directly related to circles.

use super::{bisector, prelude::*, ScalarUnit};

/// Circle constructor. Creates a circle based off of its center and radius.
fn circle_function(
    center: Expr<Point>,
    radius: Distance,
    context: &CompileContext,
    display: Properties,
) -> Expr<Circle> {
    context.circle_display(center, radius.0, display)
}

/// A circle circumscribed on three points.
fn circumcircle(
    a: Expr<Point>,
    b: Expr<Point>,
    c: Expr<Point>,
    context: &CompileContext,
    props: Properties,
) -> Expr<Circle> {
    let k = bisector::point_point(
        a.clone_without_node(),
        b.clone_without_node(),
        context,
        Properties::default(),
    );
    let l = bisector::point_point(b, c, context, Properties::default());

    let center = context.intersection(k, l);
    let radius = context.distance_pp(center.clone_without_node(), a);

    context.circle_display(center, radius, props)
}

/// A circle inscribed in three points.
fn incircle(
    a: Expr<Point>,
    b: Expr<Point>,
    c: Expr<Point>,
    context: &CompileContext,
    props: Properties,
) -> Expr<Circle> {
    let k = context.bisector_ppp(
        a.clone_without_node(),
        b.clone_without_node(),
        c.clone_without_node(),
    );
    let l = context.bisector_ppp(b.clone_without_node(), c, a.clone_without_node());
    let ab = context.line(a, b);

    let center = context.intersection(k, l);
    let radius = context.distance_pl(center.clone_without_node(), ab);

    context.circle_display(center, radius, props)
}

/// Register the function
pub fn register(library: &mut Library) {
    library
        .add(
            Function::new("circle")
                .overload(circle_function)
                .overload(
                    |radius: Distance, center: Expr<Point>, context: &CompileContext, display| {
                        circle_function(center, radius, context, display)
                    },
                )
                .overload(|context: &mut CompileContext, display| {
                    let mut center = context.free_point();
                    let mut radius = context.free_scalar();

                    center.take_node();
                    radius.take_node();

                    circle_function(
                        center,
                        ScalarUnit::from(context.set_unit(radius, unit::DISTANCE)),
                        context,
                        display,
                    )
                }),
        )
        .add(
            Function::new("circumcircle")
                .alias("[point collection (3)]::circumcircle")
                .overload(circumcircle)
                .overload(|mut col: Pc<3>, context: &CompileContext, props| {
                    circumcircle(
                        index!(node col, 0),
                        index!(node col, 1),
                        index!(node col, 2),
                        context,
                        props,
                    )
                }),
        )
        .add(
            Function::new("incircle")
                .alias("[point collection (3)]::incircle")
                .overload(incircle)
                .overload(|mut col: Pc<3>, context: &CompileContext, props| {
                    incircle(
                        index!(node col, 0),
                        index!(node col, 1),
                        index!(node col, 2),
                        context,
                        props,
                    )
                }),
        );
}
