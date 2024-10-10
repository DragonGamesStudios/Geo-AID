//! Everything relating in any way to `GeoScript`. This is where the language gets parsed,
//! compiled and optimized. All errors are defined and reported here as well. The largest
//! module of Geo-AID

use std::{
    fmt::Display,
    ops::{Deref, DerefMut, Div, Mul},
};

use crate::cli::{AnnotationKind, Change, DiagnosticData, Fix};
use geo_aid_figure::math_string::SPECIAL_MATH;
use num_traits::{One, Zero};
use serde::Serialize;

use self::parser::Type;
use self::token::{number::CompExponent, NamedIdent, Span, Token};

pub mod cli;
pub mod figure;
pub mod geometry;
pub mod math;
pub mod parser;
pub mod token;
pub mod unroll;

/// A `GeoScript` error
#[derive(Debug)]
pub enum Error {
    /// Invalid token in the figure script.
    InvalidToken {
        /// The token that was encountered.
        token: Token,
    },
    /// Invalid (unsupported) character in the figure script.
    InvalidCharacter {
        /// The character that was encountered.
        character: char,
        /// Where it was encountered.
        error_span: Span,
    },
    /// A newline character was found in a string
    NewLineInString {
        /// Where the error happened.
        error_span: Span,
    },
    /// The given number is too large to be parsed.
    NumberTooLarge {
        /// Where the number is.
        error_span: Span,
    },
    /// Found an explicit iterator with a single variant.
    SingleVariantExplicitIterator {
        /// The location of the iterator.
        error_span: Span,
    },
    /// Unexpected end of script.
    EndOfInput,
    /// Found an undefined rule oprator.
    UndefinedRuleOperator {
        /// The operator
        operator: NamedIdent,
    },
    /// Iterators with non-matching lengths
    InconsistentIterators {
        /// The first iterator's span.
        first_span: Span,
        /// The first iterator's length
        first_length: usize,
        /// The second iterator's span
        occurred_span: Span,
        /// he second iterator's length
        occurred_length: usize,
        /// The specific error span.
        error_span: Span,
    },
    /// An iterator contains an iterator with the same id.
    IteratorWithSameIdIterator {
        /// Where exactly the error occurred
        error_span: Span,
        /// The parent iterator's span.
        parent_span: Span,
        /// The contained iterator's span.
        contained_span: Span,
    },
    /// Inconsistent types in a rule or a binary operation.
    InconsistentTypes {
        /// The expected type
        // boxes here to reduce size
        expected: (Type, Box<Span>),
        /// The recevied type.
        got: (Type, Box<Span>),
        /// Exactly where the error occurred.
        error_span: Box<Span>,
    },
    /// A variable with the same name already exists
    RedefinedVariable {
        /// The first definition span
        defined_at: Span,
        /// The second definition span
        error_span: Span,
        /// The variable name
        variable_name: String,
    },
    /// A variable of undefined type
    UndefinedTypeVariable {
        /// Where the variable is defined
        definition: Span,
    },
    /// An undefined variable was referenced
    UndefinedVariable {
        /// The reference span
        error_span: Span,
        /// The variable name
        variable_name: String,
        /// The potentially intended name.
        suggested: Option<String>,
    },
    /// An undefined function was referenced.
    UndefinedFunction {
        /// The reference span
        error_span: Span,
        /// The function name
        function_name: String,
        /// The potentially intended name.
        suggested: Option<&'static str>,
    },
    /// An undefined method was referenced.
    UndefinedMethod {
        /// The reference sapn
        error_span: Span,
        /// Teh method name
        function_name: String,
        /// The potentially intended name.
        suggested: Option<&'static str>,
        /// The type the method was searched on.
        on_type: Type,
    },
    /// An undeifned field was referenced
    UndefinedField {
        /// The reference span
        error_span: Span,
        /// The field name
        field: String,
        /// The type the field was searched on
        on_type: Type,
        /// The potentially intended name.
        suggested: Option<&'static str>,
    },
    /// A field was referenced on type with no fields.
    NoFieldsOnType {
        /// The reference span
        error_span: Span,
        /// The type the field was searched on.
        on_type: Type,
    },
    /// An attempt to use an unsupported language feature was made.
    FeatureNotSupported {
        /// The exact error span
        error_span: Span,
        /// The name of the feature.
        feature_name: &'static str,
    },
    /// Invalid argument count for a function
    InvalidArgumentCount {
        /// The call span
        error_span: Span,
        /// Expected possible numbers of arguments
        expected: &'static [u8],
        /// The count of arguments received.
        got: u8,
    },
    /// An overload for a function was not found
    OverloadNotFound {
        /// The call span
        error_span: Span,
        /// The call arguments
        params: Vec<Type>,
        /// The function name
        function_name: String,
    },
    /// Cannot unpack a type onto a point collection.
    CannotUnpack {
        /// The span of the unpack attempt
        error_span: Span,
        /// The type that cannot be unpacked.
        ty: Type,
    },
    /// There's no implicit conversion between two types.
    ImplicitConversionDoesNotExist {
        /// The conversion span
        error_span: Span,
        /// The type that is attempted to be converted
        from: Type,
        /// The target type
        to: Type,
    },
    /// Invalid type of an operand of a binary operation
    InvalidOperandType {
        /// The operation span
        error_span: Box<Span>,
        /// The received type
        got: (Type, Box<Span>),
        /// The operand
        op: String,
    },
    /// An unexpected iterator was found in a let statement.
    LetStatUnexpectedIterator {
        /// The variable span
        var_span: Span,
        /// The statement's span.
        error_span: Span,
    },
    /// More than one iterator was found in a let statement.
    LetStatMoreThanOneIterator {
        /// The statement span
        error_span: Span,
        /// First iterator's span
        first_span: Span,
        /// Second iterator's span
        second_span: Span,
    },
    /// There's a non-point value in a point collection
    NonPointInPointCollection {
        /// The point collection span
        error_span: Span,
        /// The non-point part of it.
        received: (Span, Type),
    },
    /// An undefined flag was referenced
    FlagDoesNotExist {
        /// The flag name
        flag_name: String,
        /// The flag's span
        flag_span: Span,
        /// The full span.
        error_span: Span,
        /// The potential intended name
        suggested: Option<String>,
    },
    /// A flag set expected as a flag value.
    FlagSetExpected {
        /// The exact error span
        error_span: Span,
    },
    /// A string was expected
    StringExpected { error_span: Span },
    /// A string or an identifier was expected.
    StringOrIdentExpected { error_span: Span },
    /// A non-raw string or an identifier was expected
    NonRawStringOrIdentExpected { error_span: Span },
    /// A bool value was expected.
    BooleanExpected { error_span: Span },
    /// A number value was expected
    NumberExpected { error_span: Span },
    /// The provided identifier cannot be converted into a math string.
    InvalidIdentMathString { error_span: Span },
    /// A flag's value was set more than once
    RedefinedFlag {
        /// The exact error span
        error_span: Span,
        /// The first definition's span
        first_defined: Span,
        /// Name of the flag
        flag_name: String,
    },
    /// Invalid value for an enumeration
    EnumInvalidValue {
        /// The value span
        error_span: Span,
        /// The possible enum values.
        available_values: &'static [&'static str],
        /// The received, invalid value.
        received_value: String,
    },
    /// A flag that must be set was not set.
    RequiredFlagNotSet {
        /// The flag's name
        flag_name: &'static str,
        /// The reason why it's required
        required_because: Span,
        /// The flag's definition span, if any
        definition_span: Option<Span>,
        /// The possible flag values.
        available_values: &'static [&'static str],
    },
    /// A comparison between two values of a type does not exist
    ComparisonDoesNotExist {
        error_span: Span,
        /// The problematic type
        ty: Type,
    },
    /// An empty lable was found
    EmptyLabel { error_span: Span },
    /// There's an unclosed special character in a math string
    UnclosedSpecial {
        error_span: Span,
        /// The longest parsed special character
        parsed_special: String,
    },
    /// An undefined special character was referenced
    SpecialNotRecognised {
        error_span: Span,
        /// The read code
        code: String,
        /// The potentially intended code.
        suggested: Option<String>,
    },
    /// There's an unclosed string
    UnclosedString { error_span: Span },
    /// An index was found inside another index, in a math string
    LabelIndexInsideIndex { error_span: Span },
    /// An unexpected property was found
    UnexpectedDisplayOption {
        error_span: Span,
        /// The unexpected property
        option: String,
        /// The potentially intended property
        suggested: Option<&'static str>,
    },
    /// A property was repeated
    RepeatedDisplayOption {
        /// The repeated property span
        error_span: Span,
        /// The first property span
        first_span: Span,
        /// The repeated option
        option: String,
    },
    /// An invalid Point collection
    InvalidPC { error_span: Span },
    /// A denominator of zero
    ZeroDenominator { error_span: Span },
    /// A function name was expected
    ExpectedFunction { error_span: Span },
}

impl Error {
    /// Match against `ImplicitConversonDoesNotExist`
    #[must_use]
    pub fn as_implicit_does_not_exist(&self) -> Option<(&Span, &Type, &Type)> {
        match self {
            Self::ImplicitConversionDoesNotExist {
                error_span,
                from,
                to,
            } => Some((error_span, from, to)),
            _ => None,
        }
    }

    /// Convert the error to a diagnostic
    #[must_use]
    #[allow(clippy::too_many_lines)]
    pub fn diagnostic(self) -> DiagnosticData {
        match self {
            Self::InvalidToken { token } => {
                DiagnosticData::new(&format!("invalid token: `{token}`")).add_span(token.get_span())
            }
            Self::InvalidCharacter {
                character,
                error_span,
            } => DiagnosticData::new(&format!("invalid character: `{character}`"))
                .add_span(error_span),
            Self::NewLineInString {
                error_span,
            } => DiagnosticData::new(&"newline in string")
                .add_span(error_span),
            Self::EndOfInput => DiagnosticData::new("unexpected end of input"),
            Self::UndefinedRuleOperator { operator } => {
                DiagnosticData::new(&format!("undefined rule operator: `{}`", operator.ident))
                    .add_span(operator.span)
            }
            Self::InconsistentIterators {
                first_span,
                first_length,
                occurred_span,
                occurred_length,
                error_span,
            } => DiagnosticData::new(&"inconsistent iterator lengths")
                .add_span(error_span)
                .add_annotation(
                    first_span,
                    AnnotationKind::Note,
                    &format!("First iterator with length {first_length} here."),
                )
                .add_annotation(
                    occurred_span,
                    AnnotationKind::Note,
                    &format!("Inconsistency (iterator with length {occurred_length}) here."),
                ),
            Self::InconsistentTypes {
                expected,
                got,
                error_span,
            } => DiagnosticData::new("inconsistent types")
                .add_span(*error_span)
                .add_annotation(
                    *expected.1,
                    AnnotationKind::Note,
                    &format!("This expression is of type {}", expected.0),
                )
                .add_annotation(
                    *got.1,
                    AnnotationKind::Note,
                    &format!("This expression is of type {}", got.0),
                ),
            Self::RedefinedVariable {
                defined_at,
                error_span,
                variable_name,
            } => DiagnosticData::new(&format!("redefined variable: `{variable_name}`"))
                .add_span(error_span)
                .add_annotation(defined_at, AnnotationKind::Note, "First defined here."),
            Self::UndefinedTypeVariable { definition } => {
                DiagnosticData::new("variable of undefined type")
                    .add_span(definition)
                    .add_annotation(definition, AnnotationKind::Note, "Defined here.")
            }
            Self::UndefinedVariable {
                error_span,
                variable_name,
                suggested
            } => {
                let message = suggested.map(|v| format!("did you mean: `{v}`?"));
                DiagnosticData::new(&format!("undefined variable: `{variable_name}`"))
                    .add_span(error_span)
                    .add_annotation_opt_msg(error_span, AnnotationKind::Help, message.as_ref())
            }
            Self::UndefinedFunction {
                error_span,
                function_name,
                suggested
            } => {
                let message = suggested.map(|v| format!("did you mean: `{v}`?"));
                DiagnosticData::new(&format!("function `{function_name}` not found"))
                    .add_span(error_span)
                    .add_annotation_opt_msg(error_span, AnnotationKind::Help, message.as_ref())
            }
            Self::UndefinedMethod {
                error_span,
                function_name,
                suggested,
                on_type
            } => {
                let message = suggested.map(|v| format!("did you mean: `{v}`?"));
                DiagnosticData::new(&format!("method `{function_name}` not found on type {on_type}"))
                    .add_span(error_span)
                    .add_annotation_opt_msg(error_span, AnnotationKind::Help, message.as_ref())
            }
            Self::UndefinedField {
                error_span,
                field,
                on_type,
                suggested
            } => {
                let message = suggested.map(|v| format!("did you mean: `{v}`?"));
                DiagnosticData::new(&format!("field `{field}` not found on type {on_type}"))
                    .add_span(error_span)
                    .add_annotation_opt_msg(error_span, AnnotationKind::Help, message.as_ref())
            }
            Self::NoFieldsOnType {
                error_span,
                on_type,
            } => {
                DiagnosticData::new(&format!("there are no fields on type {on_type}"))
                    .add_span(error_span)
            }
            Self::FeatureNotSupported {
                error_span,
                feature_name,
            } => {
                DiagnosticData::new(&format!("feature `{feature_name}` not supported"))
                    .add_span(error_span)
            }
            Self::InvalidArgumentCount {
                error_span,
                expected,
                got,
            } => {
                DiagnosticData::new(&format!("invalid argument count. Expected one of `{expected:?}`, got {got}"))
                    .add_span(error_span)
            }
            Self::OverloadNotFound {
                error_span,
                params,
                function_name,
            } => {
                DiagnosticData::new(&format!("overload for function `{function_name}` with params `({})` not found", params.into_iter().map(|x| format!("{x}")).collect::<Vec<String>>().join(", ")))
                    .add_span(error_span)
            },
            Self::CannotUnpack { error_span, ty } => {
                DiagnosticData::new(&format!("could not unpack `{ty}` onto a point collection"))
                    .add_span(error_span)
            }
            Self::ImplicitConversionDoesNotExist {
                error_span,
                from,
                to,
            } => {
                DiagnosticData::new(&format!("implicit conversion from `{from}` to `{to}` does not exist."))
                    .add_span(error_span)
            }
            Self::InvalidOperandType {
                error_span,
                got,
                op,
            } => {
                DiagnosticData::new(&format!("invalid operand type `{}` for operator `{op}`", got.0))
                    .add_span(*error_span)
                    .add_annotation(*got.1, AnnotationKind::Note, "this is of invalid type")
            }
            Self::LetStatUnexpectedIterator {
                var_span,
                error_span,
            } => {
                DiagnosticData::new(&"unexpected iterator in right-hand side of `let` statement")
                    .add_span(error_span)
                    .add_annotation(var_span, AnnotationKind::Note, "there was no iterator of left-hand side, so the same is expected for the right")
            }
            Self::IteratorWithSameIdIterator { error_span, parent_span, contained_span } => {
                DiagnosticData::new(&"an iterator with an id of `x` must not contain an iterator with an id of `x`")
                    .add_span(error_span)
                    .add_annotation(parent_span, AnnotationKind::Note, "parent iterator here")
                    .add_annotation(contained_span, AnnotationKind::Note, "child iterator here")
            }
            Self::LetStatMoreThanOneIterator { error_span, first_span, second_span } => {
                DiagnosticData::new(&"right hand side of a let statement must contain at most a single level of iteration")
                    .add_span(error_span)
                    .add_annotation(first_span, AnnotationKind::Note, "first iterator here")
                    .add_annotation(second_span, AnnotationKind::Note, "second iterator here")
            }
            Self::NumberTooLarge { error_span } => {
                DiagnosticData::new(&"number too large")
                    .add_span(error_span)
            }
            Self::SingleVariantExplicitIterator { error_span } => {
                DiagnosticData::new(&"explicit iterators must have at least two variants")
                    .add_span(error_span)
            }
            Self::NonPointInPointCollection { error_span, received } => {
                DiagnosticData::new(&"all values in a point collection constructor must be points")
                    .add_span(error_span)
                    .add_annotation(received.0, AnnotationKind::Note, &format!("value should be a point, received {}", received.1))
            }
            Self::FlagDoesNotExist { flag_name, flag_span, error_span, suggested } => {
                let message = suggested.map(|v| format!("Did you mean: `{v}`?"));
                DiagnosticData::new(&format!("compiler flag `{flag_name}` does not exist"))
                    .add_span(error_span)
                    .add_annotation(flag_span, AnnotationKind::Note, &"This does not exist.")
                    .add_annotation_opt_msg(flag_span, AnnotationKind::Help, message.as_ref())
            }
            Self::FlagSetExpected { error_span } => {
                DiagnosticData::new(&"expected a flag set ({...})")
                    .add_span(error_span)
            }
            Self::StringExpected { error_span } => {
                DiagnosticData::new(&"expected a string")
                    .add_span(error_span)
            }
            Self::StringOrIdentExpected { error_span } => {
                DiagnosticData::new(&"expected a string or an identifier")
                    .add_span(error_span)
            }
            Self::NonRawStringOrIdentExpected { error_span } => {
                DiagnosticData::new(&"expected a non-raw string or an identifier")
                    .add_span(error_span)
            }
            Self::BooleanExpected { error_span } => {
                DiagnosticData::new(&"expected a boolean value (enabled, disabled, on, off, true, false, 1 or 0)")
                    .add_span(error_span)
            }
            Self::NumberExpected { error_span } => {
                DiagnosticData::new(&"expected a number value")
                    .add_span(error_span)
            }
            Self::InvalidIdentMathString { error_span } => {
                DiagnosticData::new(&"invalid ident for a math string")
                    .add_span(error_span)
            }
            Self::RedefinedFlag {
                first_defined,
                error_span,
                flag_name,
            } => DiagnosticData::new(&format!("redefined flag: `{flag_name}`"))
                .add_span(error_span)
                .add_annotation(first_defined, AnnotationKind::Note, "first defined here"),
            Self::EnumInvalidValue { error_span, available_values, received_value } => {
                DiagnosticData::new(&format!("invalid value for an enum flag or property: `{received_value}`"))
                    .add_span(error_span)
                    .add_annotation(error_span, AnnotationKind::Help, &format!("supported values: {}", available_values.iter().map(
                        |v| format!("`{v}`")
                    ).collect::<Vec<String>>().join(", ")))
            }
            Self::RequiredFlagNotSet { flag_name, required_because, definition_span: flagdef_span, available_values } => {
                DiagnosticData::new(&format!("you must set a value for flag `{flag_name}`."))
                    .add_annotation(required_because, AnnotationKind::Note, &"Required because of this line.")
                    .add_annotation(required_because, AnnotationKind::Help, &format!("Possible values: {}", available_values.iter().map(
                        |v| format!("`{v}`")
                    ).collect::<Vec<String>>().join(", ")))
                    .add_annotation_opt_span(flagdef_span, AnnotationKind::Note, &"Flag defined here")
                    .add_fix(Fix {
                        message: String::from("Consider defining this flag at the top of the file."),
                        changes: vec![
                            Change {
                                span: span!(1, 1, 1, 1),
                                new_content: vec![
                                    format!("@{flag_name}: {};", available_values[0]),
                                    String::new()
                                ]
                            }
                        ]
                    })
            }
            Self::ComparisonDoesNotExist { error_span, ty } => {
                DiagnosticData::new(&format!("comparison between values of type {ty} does not exist."))
                    .add_span(error_span)
            }
            Self::EmptyLabel { error_span } => {
                DiagnosticData::new(&"labels cannot be empty.")
                    .add_span(error_span)
            }
            Self::UnclosedSpecial { error_span, parsed_special } => {
                // Try to figure out if any of the chars could show up here.
                let found = SPECIAL_MATH.iter().find(|x| parsed_special.starts_with(*x));

                let d = DiagnosticData::new(&"there's a missing ']' somewhere here. Braces denote special characters To escape a brace, use \\[.")
                    .add_span(error_span);

               if let Some(found) = found {
                    d.add_fix(Fix {
                        message: String::from("You may have forgotten to put a `]` here."),
                        changes: vec![
                            Change {
                                span: span!(
                                    error_span.start.line, error_span.start.column + found.len() + 1,
                                    error_span.start.line, error_span.start.column + found.len() + 1
                                ),
                                new_content: vec![
                                    String::from("]")
                                ]
                            }
                        ]
                    })
                } else {
                    d
                }
            }
            Self::SpecialNotRecognised {
                error_span,
                code,
                suggested
            } => {
                let message = suggested.map(|v| format!("Did you mean: `{v}`?"));
                DiagnosticData::new(&format!("special code not recognised: `{code}`"))
                    .add_span(error_span)
                    .add_annotation_opt_msg(error_span, AnnotationKind::Help, message.as_ref())
            }
            Self::UnclosedString { error_span } => {
                DiagnosticData::new(&"unclosed special tag")
                    .add_span(error_span)
            }
            Self::LabelIndexInsideIndex { error_span } => {
                DiagnosticData::new(&"lower index cannot be used inside another lower index")
                    .add_span(error_span)
            }
            Self::UnexpectedDisplayOption { error_span, option, suggested } => {
                let message = suggested.map(|v| format!("did you mean: `{v}`?"));
                DiagnosticData::new(&format!("unexpected display option: `{option}`"))
                    .add_span(error_span)
                    .add_annotation_opt_msg(error_span, AnnotationKind::Help, message.as_ref())
            }
            Self::RepeatedDisplayOption { error_span, first_span, option } => {
                DiagnosticData::new(&format!("repeated display option: `{option}`"))
                    .add_span(error_span)
                    .add_annotation(first_span, AnnotationKind::Help, &"first defined here")
            }
            Self::InvalidPC { error_span } => {
                DiagnosticData::new(&"point collections in this place are ambiguous and therefore not valid")
                    .add_span(error_span)
            }
            Self::ZeroDenominator { error_span } => {
                DiagnosticData::new(&"denominator in a fraction cannot be equal to zero")
                    .add_span(error_span)
            }
            Self::ExpectedFunction { error_span } => {
                DiagnosticData::new(&"expected function, found, value")
                    .add_span(error_span)
            }
        }
    }
}

/// Defines a simple unit.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SimpleUnit {
    Distance,
    Angle,
    Scalar,
}

impl Mul for SimpleUnit {
    type Output = ComplexUnit;

    fn mul(self, rhs: Self) -> Self::Output {
        let complex = ComplexUnit::new(self);

        complex * rhs
    }
}

/// How many different units are there, minus one for scalar
const fn unit_count() -> usize {
    SimpleUnit::Scalar as usize
}

/// Defines a complex unit: a product of simple units.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize, Default, Hash)]
pub struct ComplexUnit([CompExponent; unit_count()]);

/// Unit constants
pub mod unit {
    use super::{ComplexUnit, SimpleUnit};

    /// A distance
    pub const DISTANCE: ComplexUnit = ComplexUnit::new(SimpleUnit::Distance);
    /// An angle
    pub const ANGLE: ComplexUnit = ComplexUnit::new(SimpleUnit::Angle);
    /// A simple, unitless scalar.
    pub const SCALAR: ComplexUnit = ComplexUnit::new(SimpleUnit::Scalar);
}

/// Type constants
pub mod ty {
    use super::{parser::Type, ComplexUnit, SimpleUnit};

    /// The distance type
    pub const DISTANCE: Type = Type::Scalar(Some(ComplexUnit::new(SimpleUnit::Distance)));
    /// The point type
    pub const POINT: Type = Type::Point;
    /// The angle type
    pub const ANGLE: Type = Type::Scalar(Some(ComplexUnit::new(SimpleUnit::Angle)));
    /// The line type
    pub const LINE: Type = Type::Line;
    /// The circle type
    pub const CIRCLE: Type = Type::Circle;
    /// The unitless scalar type
    pub const SCALAR: Type = Type::Scalar(Some(ComplexUnit::new(SimpleUnit::Scalar)));
    /// The unknown-unit scalar type
    pub const SCALAR_UNKNOWN: Type = Type::Scalar(None);

    /// A point collection of given length. A length of 0 signifies a generic point collection
    #[must_use]
    pub const fn collection(length: usize) -> Type {
        Type::PointCollection(length)
    }

    /// A named bundle type.
    #[must_use]
    pub const fn bundle(t: &'static str) -> Type {
        Type::Bundle(t)
    }
}

impl ComplexUnit {
    /// Creates a new complex unit representing no unit.
    #[must_use]
    pub const fn new(simple: SimpleUnit) -> Self {
        let mut arr = [CompExponent::new_raw(0, 1); unit_count()];

        match simple {
            SimpleUnit::Scalar => (),
            _ => arr[simple as usize] = CompExponent::new_raw(1, 1),
        }

        Self(arr)
    }

    /// Raises the unit to a power
    #[must_use]
    pub fn pow(mut self, exp: CompExponent) -> Self {
        for v in &mut self.0 {
            *v *= exp;
        }

        self
    }
}

impl Display for ComplexUnit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();

        for i in 0..(SimpleUnit::Scalar as usize) {
            if !self.0[i].is_zero() {
                let name = match i {
                    0 => "Distance",
                    1 => "Point",
                    2 => "Angle",
                    3 => "Line",
                    _ => unreachable!(),
                };

                if self.0[i].is_one() {
                    s += name;
                } else {
                    s += &format!("{name}^{}", self.0[i]);
                };

                s += " * ";
            }
        }

        if s.is_empty() {
            write!(f, "no unit")
        } else {
            write!(
                f,
                "{}",
                String::from_utf8(s.as_bytes()[0..(s.len() - 3)].to_vec()).unwrap()
            )
        }
    }
}

impl Mul<SimpleUnit> for ComplexUnit {
    type Output = ComplexUnit;

    fn mul(mut self, rhs: SimpleUnit) -> Self::Output {
        match rhs {
            SimpleUnit::Scalar => (),
            // Clippy doesn't like exponentiation. Thanks, Clippy
            #[allow(clippy::suspicious_arithmetic_impl)]
            _ => self[rhs as usize] += 1,
        }
        self
    }
}

impl Mul<&ComplexUnit> for ComplexUnit {
    type Output = ComplexUnit;

    fn mul(mut self, rhs: &Self) -> Self::Output {
        self.iter_mut()
            .enumerate()
            .map(|(i, x)| *x += rhs[i])
            .for_each(drop);
        self
    }
}

impl Div<SimpleUnit> for ComplexUnit {
    type Output = ComplexUnit;

    fn div(mut self, rhs: SimpleUnit) -> Self::Output {
        match rhs {
            SimpleUnit::Scalar => (),
            // Oh, c'mon, Clippy
            #[allow(clippy::suspicious_arithmetic_impl)]
            _ => self[rhs as usize] -= 1,
        }
        self
    }
}

impl Div<&ComplexUnit> for ComplexUnit {
    type Output = ComplexUnit;

    fn div(mut self, rhs: &Self) -> Self::Output {
        self.iter_mut()
            .enumerate()
            .map(|(i, x)| *x -= rhs[i])
            .for_each(drop);
        self
    }
}

impl Deref for ComplexUnit {
    type Target = [CompExponent; unit_count()];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for ComplexUnit {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
