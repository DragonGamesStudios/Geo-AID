use super::unroll::CompileContext;

pub mod angle;
pub mod bisector;
pub mod degrees;
pub mod dst;
pub mod intersection;
pub mod mid;
pub mod parallel;
pub mod perpendicular;
pub mod point;
pub mod radians;
pub mod circle;

/// Registers all builtins
pub fn register(context: &mut CompileContext) {
    point::register(context); // Point()
    dst::register(context); // dst()
    angle::register(context); // angle()
    degrees::register(context); // degrees()
    radians::register(context); // radians()
    mid::register(context); // mid()
    perpendicular::register(context); // perpendicular_through()
    parallel::register(context); // parallel_through()
    intersection::register(context); // intersection()
    bisector::register(context); // bisector()
    circle::register(context); // Circle()
}

macro_rules! ty {
    ($name:ident) => {$crate::script::ty::$name};
    ($count:literal-P) => {
        $crate::script::ty::collection($count)
    }
}

macro_rules! params {
    // ($($count:literal-)? $t:ident) => ($crate::script::builtins::ty!($($count-)? $t));
    ($($($count:literal-)? $t:ident),*) => {vec![$($crate::script::builtins::ty!($($count-)? $t)),*]}
}

macro_rules! group {
    () => (None);
    (...$($count:literal-)? $t:ident) => (Some($crate::script::builtins::ty!($($count-)? $t)))
}

macro_rules! overload {
    (($($($count:literal-)? $t:ident),* $(...$($gc:literal-)? $gt:ident)?) -> $($rcount:literal-)? $ret:ident {$content:expr}) => {
        $crate::script::unroll::FunctionOverload {
            returned_type: $crate::script::builtins::ty!($($rcount-)? $ret),
            definition_span: None,
            definition: $crate::script::unroll::FunctionDefinition(Box::new(
                $content
            )),
            params: $crate::script::builtins::params!($($($count-)? $t),*),
            param_group: $crate::script::builtins::group!()
        }
    };
    (($($($count:literal-)? $t:ident),* $(...$($gc:literal-)? $gt:ident)?) -> $($rcount:literal-)? $ret:ident : $func:ident) => {
        $crate::script::unroll::FunctionOverload {
            returned_type: $crate::script::builtins::ty!($($rcount-)? $ret),
            definition_span: None,
            definition: $crate::script::unroll::FunctionDefinition(Box::new($func)),
            params: $crate::script::builtins::params!($($($count-)? $t),*),
            param_group: $crate::script::builtins::group!($(...$($gc-)? $gt)?)
        }
    };
}

macro_rules! call {
    ($fig:ident : $func:ident($($arg:expr),*)) => {
        $func(&vec![$($arg),*], $fig, None)
    };
}

macro_rules! index {
    ($col:expr, $at:literal) => {
        $crate::script::unroll::UnrolledExpression {
            weight: 1.0,
            ty: $crate::script::ty::POINT,
            span: $crate::span!(0, 0, 0, 0),
            data: std::rc::Rc::new($crate::script::unroll::UnrolledExpressionData::IndexCollection(
                $col.clone(),
                $at
            ))
        }
    }
}

macro_rules! bisector_expr {
    ($a:expr, $b:expr, $c:expr) => {
        $crate::script::unroll::UnrolledExpression {
            weight: 1.0,
            ty: $crate::script::ty::LINE,
            span: $crate::span!(0, 0, 0, 0),
            data: std::rc::Rc::new($crate::script::unroll::UnrolledExpressionData::AngleBisector(
                $a.clone(), $b.clone(), $c.clone()
            ))
        }
    }
}

macro_rules! line_expr {
    ($a:expr, $b:expr) => {
        $crate::script::unroll::UnrolledExpression {
            weight: 1.0,
            ty: $crate::script::ty::LINE,
            span: $crate::span!(0, 0, 0, 0),
            data: std::rc::Rc::new($crate::script::unroll::UnrolledExpressionData::LineFromPoints(
                $a.clone(), $b.clone()
            ))
        }
    }
}

pub(crate) use {ty, overload, params, call, index, bisector_expr, line_expr, group};

// FunctionOverload {
//     returned_type: ty::LINE,
//     definition_span: None,
//     definition: pc3(),
//     params: vec![ty::collection(3)],
//     param_group: None,
// }