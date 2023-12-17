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

use crate::script::{figure::Mode, unroll::{BuildAssociated, ScalarNode, ScalarData, CloneWithNode}, compile::Compile};
#[allow(unused_imports)]
use crate::script::{
    unit,
    unroll::{CompileContext, Expr, Function, Library, Line, Point, Properties, Scalar},
};
use geo_aid_derive::overload;

use super::macros::call;

pub fn distance_function_pp(
    a: Expr<Point>,
    b: Expr<Point>,
    context: &CompileContext,
    mut display: Properties
) -> Expr<Scalar> {
    let display_segment = display.get("display_segment").maybe_unset(true);
    let style = display.get("style").maybe_unset(Mode::Default);

    let mut expr = context.distance_pp_display(a, b, display);

    if let Some(node) = &mut expr.node {
        node.set_associated(Associated);
        node.insert_data("display_segment", display_segment);
        node.insert_data("style", style);
    }

    expr
}

fn distance_function_pl(
    a: Expr<Point>,
    k: Expr<Line>,
    context: &CompileContext,
    mut display: Properties
) -> Expr<Scalar> {
    let display_segment = display.get("display_segment").maybe_unset(true);
    let style = display.get("style").maybe_unset(Mode::Dashed);

    let mut expr = context.distance_pl_display(a, k, display);

    if let Some(node) = &mut expr.node {
        node.set_associated(Associated);
        node.insert_data("display_segment", display_segment);
        node.insert_data("style", style);
    }

    expr
}

/// ```
/// struct Associated {
///     display_segment: bool,
///     style: Style
/// }
#[derive(Debug)]
pub struct Associated;

impl BuildAssociated<ScalarNode> for Associated {
    fn build_associated(
            self: Box<Self>,
            compiler: &mut crate::script::compile::Compiler,
            figure: &mut crate::script::figure::Figure,
            associated: &mut crate::script::unroll::HierarchyNode<ScalarNode>,
        ) {
        let display_segment = associated.
            get_data("display_segment")
            .unwrap()
            .as_bool()
            .unwrap();
        let style = associated
            .get_data("style")
            .unwrap()
            .as_style()
            .unwrap();

        if display_segment.unwrap() {
            match &associated.root.expr.data.data {
                ScalarData::PointPointDistance(a, b) => {
                    figure.segments.push((
                        compiler.compile(a),
                        compiler.compile(b),
                        style.unwrap()
                    ))
                },
                ScalarData::PointLineDistance(a, k) => {
                    // Projection
                    let b = Expr::new_spanless(Point::LineLineIntersection(
                        Expr::new_spanless(Line::PerpendicularThrough(
                            k.clone_without_node(),
                            a.clone_without_node()
                        )),
                        k.clone_without_node() 
                    ));

                    figure.segments.push((
                        compiler.compile(a),
                        compiler.compile(&b),
                        style.unwrap()
                    ))
                }
                _ => unreachable!()
            }
        }
    }
}


pub fn register(library: &mut Library) {
    library.functions.insert(
        String::from("dst"),
        Function {
            name: String::from("dst"),
            overloads: vec![
                overload!((DISTANCE) -> DISTANCE {
                    |v: Expr<Scalar>, context: &CompileContext, display: Properties| {
                        display.finish(context);
                        v
                    }
                }),
                overload!((SCALAR) -> DISTANCE {
                    |v: Expr<Scalar>, context: &CompileContext, display: Properties| {
                        display.finish(context);
                        context.set_unit(v, unit::DISTANCE)
                    }
                }),
                overload!((POINT, POINT) -> DISTANCE : distance_function_pp),
                overload!((POINT, LINE) -> DISTANCE : distance_function_pl),
                overload!((LINE, POINT) -> DISTANCE {
                    |k: Expr<Line>, a: Expr<Point>, context: &CompileContext, display| call!(context:distance_function_pl(
                        a, k
                    ) with display)
                }),
            ],
        },
    );
}
