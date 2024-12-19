//! Utility crate providing functions for geometry computations.

use std::{
    fmt::Display,
    iter::{Product, Sum},
    ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign},
};

use geo_aid_figure::Position;
use serde::Serialize;

/// Represents a complex number
#[derive(Debug, Clone, Copy, Serialize)]
pub struct Complex {
    /// The real part
    pub real: f64,
    /// The imaginary part.
    pub imaginary: f64,
}

impl Complex {
    /// Create a new complex from its real and imaginary parts.
    #[must_use]
    #[inline]
    pub const fn new(real: f64, imaginary: f64) -> Self {
        Self { real, imaginary }
    }

    /// Convert a real to a complex.
    #[must_use]
    pub const fn real(real: f64) -> Self {
        Self::new(real, 0.0)
    }

    /// Create a new complex from its polar representation.
    #[must_use]
    pub fn polar(theta: f64, radius: f64) -> Self {
        Self::new(theta.cos(), theta.sin()) * radius
    }

    /// Complex zero.
    #[must_use]
    #[inline]
    pub const fn zero() -> Self {
        Self::new(0.0, 0.0)
    }

    /// Complex one.
    #[must_use]
    #[inline]
    pub const fn one() -> Self {
        Self::new(1.0, 0.0)
    }

    /// The imaginary unit.
    #[must_use]
    pub const fn i() -> Self {
        Self::new(0.0, 1.0)
    }

    /// Optimized multiplication by the complex unit (i).
    #[must_use]
    pub fn mul_i(self) -> Complex {
        Complex::new(-self.imaginary, self.real)
    }

    /// The magnitude of the complex, also called its modulus.
    #[must_use]
    pub fn magnitude(self) -> f64 {
        f64::sqrt(self.real.powi(2) + self.imaginary.powi(2))
    }

    /// The complex's conjugate (a - bi)
    #[must_use]
    pub fn conjugate(self) -> Complex {
        Complex::new(self.real, -self.imaginary)
    }

    /// Multiply the complex's parts by other complex's parts (ab + cdi)
    #[must_use]
    pub fn partial_mul(self, other: Complex) -> Complex {
        Complex::new(self.real * other.real, self.imaginary * other.imaginary)
    }

    /// Divide the complex's parts by other complex's parts (a/b + (c/d)i)
    #[must_use]
    pub fn partial_div(self, other: Complex) -> Complex {
        Complex::new(self.real / other.real, self.imaginary / other.imaginary)
    }

    /// Compute the complex's argument
    #[must_use]
    pub fn arg(self) -> f64 {
        f64::atan2(self.imaginary, self.real)
    }

    /// Normalize the complex by dividing it by its own magnitude.
    #[must_use]
    pub fn normalize(self) -> Complex {
        self / self.magnitude()
    }

    /// Number-theoretical norm. Simply a^2 + b^2 with self = a + bi
    #[must_use]
    pub fn len_squared(self) -> f64 {
        self.real * self.real + self.imaginary * self.imaginary
    }

    /// A square root. Chooses the one with non-negative imaginary part.
    #[must_use]
    pub fn sqrt(self) -> Complex {
        // The formula used here doesn't work for negative reals. We can use a trick here to bypass that restriction.
        // If the real part is negative, we simply negate it to get a positive part and then multiply the result by `i`.
        if self.real > 0.0 {
            // Use the generic formula (https://math.stackexchange.com/questions/44406/how-do-i-get-the-square-root-of-a-complex-number)
            let r = self.magnitude();

            r.sqrt() * (self + r).normalize()
        } else {
            (-self).sqrt().mul_i()
        }
    }

    /// Same as sqrt, but returns a normalized result.
    #[must_use]
    pub fn sqrt_norm(self) -> Complex {
        // The formula used here doesn't work for negative reals. We can use a trick here to bypass that restriction.
        // If the real part is negative, we simply negate it to get a positive part and then multiply the result by `i`.
        if self.real > 0.0 {
            // Use the generic formula (https://math.stackexchange.com/questions/44406/how-do-i-get-the-square-root-of-a-complex-number)
            let r = self.magnitude();

            // We simply don't multiply by the square root of r.
            (self + r).normalize()
        } else {
            (-self).sqrt_norm().mul_i() // Normalization isn't lost here.
        }
    }

    /// Inverse of the number.
    #[must_use]
    pub fn inverse(self) -> Self {
        self.conjugate() / self.len_squared()
    }
}

impl From<Complex> for Position {
    fn from(value: Complex) -> Self {
        Self {
            x: value.real,
            y: value.imaginary,
        }
    }
}

impl From<Complex> for geo_aid_figure::Complex {
    fn from(value: Complex) -> Self {
        Self {
            real: value.real,
            imaginary: value.imaginary,
        }
    }
}

impl From<Position> for Complex {
    fn from(value: Position) -> Self {
        Self::new(value.x, value.y)
    }
}

impl Mul for Complex {
    type Output = Complex;

    fn mul(self, rhs: Complex) -> Self::Output {
        Complex::new(
            self.real * rhs.real - self.imaginary * rhs.imaginary,
            self.real * rhs.imaginary + rhs.real * self.imaginary,
        )
    }
}

impl Mul<Complex> for f64 {
    type Output = Complex;

    fn mul(self, rhs: Complex) -> Self::Output {
        Complex::new(self * rhs.real, self * rhs.imaginary)
    }
}

impl Mul<f64> for Complex {
    type Output = Complex;

    fn mul(self, rhs: f64) -> Self::Output {
        Complex::new(self.real * rhs, self.imaginary * rhs)
    }
}

impl MulAssign<f64> for Complex {
    fn mul_assign(&mut self, rhs: f64) {
        self.real *= rhs;
        self.imaginary *= rhs;
    }
}

impl Add<f64> for Complex {
    type Output = Complex;

    fn add(self, rhs: f64) -> Self::Output {
        Complex::new(self.real + rhs, self.imaginary)
    }
}

impl Add for Complex {
    type Output = Complex;

    fn add(self, rhs: Self) -> Self::Output {
        Complex::new(self.real + rhs.real, self.imaginary + rhs.imaginary)
    }
}

impl Div<f64> for Complex {
    type Output = Complex;

    fn div(self, rhs: f64) -> Self::Output {
        Complex::new(self.real / rhs, self.imaginary / rhs)
    }
}

impl Div for Complex {
    type Output = Complex;

    fn div(self, rhs: Complex) -> Self::Output {
        (self * rhs.conjugate()) / (rhs.real * rhs.real + rhs.imaginary * rhs.imaginary)
    }
}

impl Sub<f64> for Complex {
    type Output = Complex;

    fn sub(self, rhs: f64) -> Self::Output {
        Complex::new(self.real - rhs, self.imaginary)
    }
}

impl Sub for Complex {
    type Output = Complex;

    fn sub(self, rhs: Self) -> Self::Output {
        Complex::new(self.real - rhs.real, self.imaginary - rhs.imaginary)
    }
}

impl SubAssign for Complex {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl AddAssign for Complex {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl MulAssign for Complex {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Display for Complex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(precision) = f.precision() {
            write!(
                f,
                "{2:.*} + {3:.*}i",
                precision, precision, self.real, self.imaginary
            )
        } else {
            write!(f, "{} + {}i", self.real, self.imaginary)
        }
    }
}

impl Neg for Complex {
    type Output = Complex;

    fn neg(self) -> Self::Output {
        Complex::new(-self.real, -self.imaginary)
    }
}

impl Default for Complex {
    fn default() -> Self {
        Self {
            real: 0.0,
            imaginary: 0.0,
        }
    }
}

impl Sum for Complex {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        let mut v = Complex::zero();

        for x in iter {
            v += x;
        }

        v
    }
}

impl Product for Complex {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        let mut v = Complex::zero();

        for x in iter {
            v *= x;
        }

        v
    }
}

/// Represents a line in a 2D Euclidean space.
#[derive(Debug, Clone, Copy, Serialize)]
pub struct Line {
    /// Line's origin as a complex number.
    pub origin: Complex,
    /// A normalized direction vector.
    pub direction: Complex,
}

impl Line {
    /// Creates a new line from its origin and a direction vector
    #[must_use]
    pub fn new(origin: Complex, direction: Complex) -> Self {
        Self {
            origin,
            direction: direction.normalize(),
        }
    }
}

impl From<Line> for geo_aid_figure::Line {
    fn from(value: Line) -> Self {
        Self {
            origin: value.origin.into(),
            direction: value.direction.into(),
        }
    }
}

/// Represents a circle in a 2D euclidean space.
#[derive(Debug, Clone, Copy, Serialize)]
pub struct Circle {
    /// Circle's center.
    pub center: Complex,
    /// Its radius
    pub radius: f64,
}

impl From<Circle> for geo_aid_figure::Circle {
    fn from(value: Circle) -> Self {
        Self {
            center: value.center.into(),
            radius: value.radius,
        }
    }
}

/// Enumerated value type for serialization.
#[derive(Debug, Clone, Copy, Serialize)]
pub enum ValueEnum {
    Complex(Complex),
    Line(Line),
    Circle(Circle),
}

impl ValueEnum {
    #[must_use]
    pub fn as_complex(self) -> Option<Complex> {
        match self {
            Self::Complex(c) => Some(c),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_line(self) -> Option<Line> {
        match self {
            Self::Line(l) => Some(l),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_circle(self) -> Option<Circle> {
        match self {
            Self::Circle(l) => Some(l),
            _ => None,
        }
    }
}

impl From<ValueEnum> for geo_aid_figure::Value {
    fn from(value: ValueEnum) -> Self {
        match value {
            ValueEnum::Complex(c) => Self::Complex(c.into()),
            ValueEnum::Line(ln) => Self::Line(ln.into()),
            ValueEnum::Circle(c) => Self::Circle(c.into()),
        }
    }
}

/// Get the line going through `p1` and `p2`
#[must_use]
pub fn get_line(p1: Complex, p2: Complex) -> Line {
    Line {
        origin: p1,
        direction: (p2 - p1).normalize(),
    }
}

/// Gets the intersection point of two lines.
#[must_use]
pub fn get_intersection(k_ln: Line, l_ln: Line) -> Complex {
    let Line {
        origin: a,
        direction: b,
    } = k_ln;
    let Line {
        origin: c,
        direction: d,
    } = l_ln;

    a - b * ((a - c) / d).imaginary / (b / d).imaginary
}

/// Gets the intersections of a line and a circle
#[must_use]
pub fn get_lc_intersections(k: Line, omega: Circle) -> Option<(Complex, Complex)> {
    let center = (omega.center - k.origin) / k.direction;
    let d = center.imaginary.abs();

    if d > omega.radius {
        return None;
    }

    let diff = (omega.radius * omega.radius - d * d).sqrt();

    let (a, b) = (center.real - diff, center.real + diff);
    Some((
        a * k.direction + k.origin,
        b * k.direction + k.origin
    ))
}

/// Gets the angle between two arms and the origin
#[must_use]
pub fn get_angle(arm1: Complex, origin: Complex, arm2: Complex) -> f64 {
    // Get the vectors to calculate the angle between them.
    let arm1_vec = arm1 - origin;
    let arm2_vec = arm2 - origin;

    // Get the dot product
    let dot_product = arm1_vec.real * arm2_vec.real + arm1_vec.imaginary * arm2_vec.imaginary;

    // Get the argument
    f64::acos(dot_product / (arm1_vec.magnitude() * arm2_vec.magnitude()))
}

/// Gets the directed angle between two arms and the origin
#[must_use]
pub fn get_angle_directed(arm1: Complex, origin: Complex, arm2: Complex) -> f64 {
    // Get the vectors to calculate the angle between them.
    let arm1_vec = arm1 - origin;
    let arm2_vec = arm2 - origin;

    // decrease p2's angle by p1's angle:
    let p2_rotated = arm2_vec / arm1_vec;

    // Get the argument
    p2_rotated.arg()
}

// Rotates p around origin by angle.
#[must_use]
pub fn rotate_around(p: Complex, origin: Complex, angle: f64) -> Complex {
    (p - origin) * Complex::new(angle.cos(), angle.sin()) + origin
}

// Computes Point-Line distance.
#[must_use]
pub fn distance_pt_ln(point: Complex, line: Line) -> f64 {
    // Make the point coordinates relative to the origin and rotate.
    let point_rot = (point - line.origin) / line.direction;

    // Now we can just get the imaginary part. We have to take the absolute value here.
    point_rot.imaginary.abs()
}

// Computes Point-Point distance.
#[must_use]
pub fn distance_pt_pt(p1: Complex, p2: Complex) -> f64 {
    ((p1.real - p2.real) * (p1.real - p2.real)
        + (p1.imaginary - p2.imaginary) * (p1.imaginary - p2.imaginary))
        .sqrt()
}
