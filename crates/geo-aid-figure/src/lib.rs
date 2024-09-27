#![warn(
    clippy::pedantic,
    missing_docs,
    missing_copy_implementations,
    missing_debug_implementations
)]

//! This crate contains type definitions for Geo-AID's JSON format.

use crate::math_string::MathString;
use num_rational::Rational64;
use serde::{Deserialize, Serialize};
use std::fmt::{Display, Formatter};
use std::num::NonZeroI64;
use std::ops::{Add, Deref, DerefMut, Mul};

/// Math strings are Geo-AID's way of handling text involving math-specific notation.
pub mod math_string;

/// Index of an expression.
/// Isn't `Copy` for easier differentiation between moving and cloning the value.
#[allow(missing_copy_implementations)]
#[derive(Debug, Clone, Hash, Ord, PartialOrd, Eq, PartialEq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct VarIndex(pub usize);

impl Display for VarIndex {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)
    }
}

impl Deref for VarIndex {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for VarIndex {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Index of an expression or an entity
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct EntityIndex(pub usize);

impl Deref for EntityIndex {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for EntityIndex {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// A complex number real + i*imaginary
#[derive(Debug, Clone, Copy, Serialize, Deserialize, Default)]
pub struct Complex {
    /// The real component
    #[serde(default)]
    pub real: f64,
    /// The imaginary component
    #[serde(default)]
    pub imaginary: f64,
}

/// A rational number
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Ratio {
    /// The nominator of the ratio
    pub num: i64,
    /// The denominator of the ratio
    #[serde(default = "one_i64")]
    pub denom: NonZeroI64,
}

impl From<Rational64> for Ratio {
    fn from(value: Rational64) -> Self {
        Self {
            num: *value.numer(),
            denom: (*value.denom()).try_into().unwrap(),
        }
    }
}

fn one_i64() -> NonZeroI64 {
    NonZeroI64::new(1).unwrap()
}

impl Default for Ratio {
    fn default() -> Self {
        Self {
            num: 0,
            denom: one_i64(),
        }
    }
}

/// A line
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Line {
    /// The origin point of the line
    pub origin: Complex,
    /// The direction vector of the line
    pub direction: Complex,
}

/// A circle
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Circle {
    /// The center of the circle
    pub center: Complex,
    /// The radius of the circle. Must be positive
    pub radius: f64,
}

/// A value of an expression or an entity
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "kebab-case")]
pub enum Value {
    /// A complex number
    Complex(Complex),
    /// A line
    Line(Line),
    /// A circle
    Circle(Circle),
}

/// Defines how a line should be drawn
#[derive(Debug, Clone, Copy, Serialize, Deserialize, Default)]
#[serde(rename_all = "kebab-case")]
pub enum Style {
    /// A standard, solid line
    #[default]
    Solid,
    /// A line made with dots
    Dotted,
    /// A line made with dashes (`-`)
    Dashed,
    /// A slightly thicker line
    Bold,
}

/// Label-related information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Label {
    /// Where the label should be drawn (figure space)
    pub position: Position,
    /// The label contents
    pub content: MathString,
}

/// A figure-space position
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Position {
    /// X coordinate
    pub x: f64,
    /// Y coordinate
    pub y: f64,
}

impl Mul<f64> for Position {
    type Output = Self;

    fn mul(self, rhs: f64) -> Self::Output {
        Self {
            x: self.x * rhs,
            y: self.y * rhs,
        }
    }
}

impl Add for Position {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
}

/// A figure generated by Geo-AID
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Figure {
    /// The width of the image
    pub width: f64,
    /// The height of the image
    pub height: f64,
    /// Expressions used by the image
    pub expressions: Vec<Expression>,
    /// Entities in the image
    pub entities: Vec<Entity>,
    /// Items drawn on the image
    pub items: Vec<Item>,
}

/// A single expression
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Expression {
    /// The calculated value of this expression
    pub hint: Value,
    /// The kind of an expression this is
    pub kind: ExpressionKind,
}

/// The kind of an expression
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "kebab-case")]
pub enum ExpressionKind {
    /// An entity
    Entity {
        /// The index in the `entities` vector
        id: EntityIndex,
    },
    /// Intersection of k and l
    LineLineIntersection {
        /// Line 1
        k: VarIndex,
        /// Line 2
        l: VarIndex,
    },
    /// The arithmetic average of points as complex numbers
    AveragePoint {
        /// The elements of the average
        items: Vec<VarIndex>,
    },
    /// The center of a circle
    CircleCenter {
        /// Circle to query
        circle: VarIndex,
    },
    /// Summation of numbers
    Sum {
        /// All the added ones
        plus: Vec<VarIndex>,
        /// All the subtracted ones
        minus: Vec<VarIndex>,
    },
    /// Product of numbers
    Product {
        /// Multiply by them
        times: Vec<VarIndex>,
        /// Divide by them
        by: Vec<VarIndex>,
    },
    /// A constant number value
    Const {
        /// The value
        value: Complex,
    },
    /// Raising a value to a rational power
    Power {
        /// The base
        value: VarIndex,
        /// The exponent
        exponent: Ratio,
    },
    /// Distance between `p` and `q`
    PointPointDistance {
        /// Point 1
        p: VarIndex,
        /// Point 2
        q: VarIndex,
    },
    /// Distance between `point` and `line`
    PointLineDistance {
        /// The point
        point: VarIndex,
        /// The line
        line: VarIndex,
    },
    /// Angle `abc`
    ThreePointAngle {
        /// Arm 1
        a: VarIndex,
        /// Vertex
        b: VarIndex,
        /// Arm 2
        c: VarIndex,
    },
    /// Directed angle `abc`
    ThreePointAngleDir {
        /// Arm 1
        a: VarIndex,
        /// Vertex
        b: VarIndex,
        /// Arm 2
        c: VarIndex,
    },
    /// Angle between `k` and `l`
    TwoLineAngle {
        /// Line 1
        k: VarIndex,
        /// Line 2
        l: VarIndex,
    },
    /// X coordinate of a point
    PointX {
        /// The point
        point: VarIndex,
    },
    /// Y coordinate of a point
    PointY {
        /// The point
        point: VarIndex,
    },
    /// Line `pq`
    PointPoint {
        /// Point 1
        p: VarIndex,
        /// Point 2
        q: VarIndex,
    },
    /// Bisector of angle `abc`
    AngleBisector {
        /// Arm 1
        p: VarIndex,
        /// Vertex
        q: VarIndex,
        /// Arm 2
        r: VarIndex,
    },
    /// Perpendicular line going through `point`
    PerpendicularThrough {
        /// The guiding point
        point: VarIndex,
        /// The reference line
        line: VarIndex,
    },
    /// Parallel line going through `point`
    ParallelThrough {
        /// The guiding point
        point: VarIndex,
        /// The reference line
        line: VarIndex,
    },
    /// A circle with center and radius
    ConstructCircle {
        /// The circle's center
        center: VarIndex,
        /// The circle's radius. Must be positive
        radius: VarIndex,
    },
}

/// A single entity
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Entity {
    /// The calculated value of this expression
    pub hint: Value,
    /// The kind of an entity this is
    pub kind: EntityKind,
}

/// The kind of an entity
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "kebab-case")]
pub enum EntityKind {
    /// A free point
    FreePoint,
    /// Point on a line
    PointOnLine {
        /// The reference line
        line: VarIndex,
    },
    /// Point on a circle
    PointOnCircle {
        /// The reference circle
        circle: VarIndex,
    },
    /// A free real
    FreeReal,
    /// A distance unit
    DistanceUnit,
}

/// An item drawn on the image
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "kebab-case")]
pub enum Item {
    /// A point
    Point(PointItem),
    /// A line
    Line(LineItem),
    /// A ray (half-line)
    #[doc(alias = "HalfLine")]
    Ray(TwoPointItem),
    /// A segment
    Segment(TwoPointItem),
    /// A circle
    Circle(CircleItem),
}

impl Item {
    /// If it's a point, returns a mutable reference to it
    #[must_use]
    pub fn as_point_mut(&mut self) -> Option<&mut PointItem> {
        match self {
            Self::Point(p) => Some(p),
            _ => None,
        }
    }
}

/// A point item. Usually depicted by a dot.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PointItem {
    /// The point's position on the image
    pub position: Position,
    /// The defining expression index
    pub id: VarIndex,
    /// Whether to display the dot (circle)
    #[serde(default)]
    pub display_dot: bool,
    /// The point's label
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub label: Option<Label>,
}

/// A line item. Usually depicted by a line.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LineItem {
    /// Delimiting points of the drawn line segment
    pub points: (Position, Position),
    /// The defining expression index
    pub id: VarIndex,
    /// How the line should be drawn
    #[serde(default)]
    pub style: Style,
    /// The line's label
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub label: Option<Label>,
}

/// A segment or a ray. Usually depicted by a line.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TwoPointItem {
    /// Delimiting points of the drawn line segment
    pub points: (Position, Position),
    /// The first point's expression index (origin if ray)
    pub p_id: VarIndex,
    /// The second point's expression index
    pub q_id: VarIndex,
    /// How the line should be drawn
    #[serde(default)]
    pub style: Style,
    /// The item's label
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub label: Option<Label>,
}

/// A circle item. Usually depicted by a circle.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircleItem {
    /// The center of the drawn circle
    pub center: Position,
    /// The radius of the drawn circle
    pub radius: f64,
    /// The defining expression index
    pub id: VarIndex,
    /// How the line should be drawn
    #[serde(default)]
    pub style: Style,
    /// The circle's label
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub label: Option<Label>,
}
