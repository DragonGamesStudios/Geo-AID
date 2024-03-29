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

use super::prelude::*;
use geo_aid_derive::overload;

pub fn function_point(
    args: Vec<Expr<Point>>,
    context: &CompileContext,
    display: Properties,
) -> Expr<Point> {
    context.average_p_display(args, display)
}

fn function_scalar(
    args: Vec<Expr<Scalar>>,
    context: &CompileContext,
    display: Properties,
) -> Expr<Scalar> {
    context.average_s_display(args, display)
}

pub fn register(library: &mut Library) {
    library.functions.insert(
        String::from("mid"),
        Function {
            overloads: vec![
                overload!((...ANGLE) -> ANGLE : function_scalar),
                overload!((...DISTANCE) -> DISTANCE : function_scalar),
                overload!((...POINT) -> POINT : function_point),
                overload!((...SCALAR) -> SCALAR : function_scalar),
            ],
        },
    );
}
