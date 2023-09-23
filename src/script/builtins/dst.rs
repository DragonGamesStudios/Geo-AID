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

use crate::script::unroll::{Function, Library};

use super::macros::{overload, set_unit, distance};

pub fn register(library: &mut Library) {
    library.functions.insert(
        String::from("dst"),
        Function {
            name: String::from("dst"),
            overloads: vec![
                overload!((DISTANCE) -> DISTANCE {
                    |args, _, _| args[0].clone()
                }),
                overload!((SCALAR) -> DISTANCE {
                    |args, _, _| set_unit!(args[0], %DISTANCE)
                }),
                overload!((POINT, POINT) -> DISTANCE {
                    |args, _, _| distance!(PP: args[0], args[1])
                }),
                overload!((POINT, LINE) -> DISTANCE {
                    |args, _, _| distance!(PL: args[0], args[1])
                }),
                overload!((POINT, POINT) -> DISTANCE {
                    |args, _, _| distance!(PL: args[1], args[0])
                }),
            ],
        },
    );
}
