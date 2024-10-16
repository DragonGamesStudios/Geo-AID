# Functions

Here are listed all of GeoScript's functions. Note that, the names are case-insensitive.
Overloads are listed in the order they are checked.

## `angle`

* `angle(ABC: 3-P)`
* `angle(A: Point, B: Point, C: Point)`

**Return type**: [Scalar (angle)](./types.md#scalar)

**Returns**: measurement of the angle `ABC`

**Displays**: the angle's arms.

The function accepts additional properties in the form of:

```rust
struct Angle {
    display_arms: bool, // Default: true,
    arms_type: LineType, // Default: SEGMENT
}
```

`display_arms` decides whether the arms should be displayed and `arms_type` decides whether they should be segments, rays or lines. The assumed order for rays is `B -> A` and `B -> C`;

* `angle(k: Line, l: Line)`

**Return type**: [Scalar (angle)](./types.md#scalar)

**Returns**: measurement of the angle between `k` and `l`. Which angle, depends on the order of the lines. For predictable outcome, the point versions are strongly recommended.

## `bisector`

* `bisector(AB: 2-P)`
* `bisector(A: Point, B: Point)`

**Return type**: [Line](./types.md#Line)

**Returns**: a bisector of the segment `AB` - a perpendicular line passing through its center.

* `bisector(ABC: 3-P)`
* `bisector(A: Point, B: Point, C: Point)`

**Return type**: [Line](./types.md#Line)

**Returns**: a bisector of the angle `ABC` - a line between lines `AB` and `BC`, where each point is in the same distance from both of these lines.

**Displays**: the angle's arms.

The function accepts additional properties in the form of:

```rust
struct Bisector {
    display_arms: bool, // Default: true,
    arms_type: LineType, // Default: SEGMENT
}
```

`display_arms` decides whether the arms should be displayed and `arms_type` decides whether they should be segments, rays or lines. The assumed order for rays is `B -> A` and `B -> C`;

* `angle(k: Line, l: Line)`

## `center`

* `center(circle: Circle)`

**Return type: [Point](./types.md#Point)

## `circle`

* `circle(center: Point, radius: Scalar (distance))`
* `circle(radius: Scalar (distance), center: Point)`

**Return type**: [Circle](./types.md#Circle)

**Returns**: a circle with the given `center` and `radius`.

* `circle()`

**Return type**: [Circle](./types.md#Circle)

**Returns**: a circle with an adjusted (free point) `center` and an adjusted (free scalar) `radius`.

## `circumcircle`

* `circumcircle(a: Point, b: Point, c: Point)`
* `circumcircle(abc: 3-P)`

**Return type**: [Circle](./types.md#Circle)

**Returns**: a circle circumscribed on the three points given.

## `degrees` (alias `deg`)

* `degrees(value: Scalar (no unit))`

**Return type**: [Scalar (angle)](./types.md#Scalar)

**Returns**: an angle with the given measurement in degrees. Related: [radians](#radians)

* `degrees(value: Scalar (angle))`

**Return type**: [Scalar (scalar)](./types.md#Scalar)

**Returns**: the angle value in degrees. Related: [radians](#radians)

## `dst` (alias `len`)

* `dst(AB: 2-P)`
* `dst(A: Point, B: Point)`

**Return type**: [Scalar (distance)](./types.md#Scalar)

**Returns**: the distance between points `A` and `B`.

**Displays**: the segment `AB`.

The function accepts additional properties in the form of:

```rust
struct Dst {
    display_segment: bool, // Default: true,
    style: Style, // Default: SOLID
}
```

`display_segment` decides whether the segment should be displayed and `style` decides how it should be displayed.

* `dst(P: Point, k: Line)`
* `dst(k: Line, P: Point)`

**Return type**: [Scalar (distance)](./types.md#Scalar)

**Returns**: the distance between point `P` and line `k`.

**Displays**: the segment between `P` and its perpendicular projection onto `k`.

The function accepts additional properties in the form of:

```rust
struct Dst {
    display_segment: bool, // Default: true,
    style: Style, // Default: DASHED
}
```

`display_segment` decides whether the segment should be displayed and `style` decides how it should be displayed.

* `dst(value: Scalar (no unit / distance))`

**Return type**: [Scalar (angle)](./types.md#Scalar)

**Returns**: the value with a distance unit.

## `incircle`

* `incircle(a: Point, b: Point, c: Point)`
* `incircle(abc: 3-P)`

**Return type**: [Circle](./types.md#Circle)

**Returns**: a circle inscribed in the three points given.

## `intersection`

All overloads by default don't display the point dot. This can be changed with properties.

* `intersection(k: Line, l: Line)`

**Return type**: [Point](./types.md#point)

**Returns**: intersection of lines `k` and `l`.

* `intersection(k: Line, circle: Circle)`
* `intersection(circle: Circle, k: Line)`

**Return type**: [Point](./types.md#point)

**Returns**: intersection of line `k` and circle `circle`.

* `intersection(o1: Circle, o2: Circle)`

**Return type**: [Point](./types.md#point)

**Returns**: intersection of circles `o1` and `o2`.

**Note**: `display_dot` property is not currently supported.

## `line`

* `line(col: 2-PC)`
* `line(P: Point, Q: Point)`

**Return type**: [Line](./types.md#Line)

**Returns**: a line through two given points.

**Displays**: The created line.

## `mid`

* `mid(col: 0-P)`

**Return Type**: [Point](.types.md#Point)

**Returns**: The middle point of all points in the collection.

**Note**: The following functions allow any positive numbers of arguments.

* `mid(v_1: Scalar (any unit u), v_2 Scalar (the same unit u), ..., v_n: Scalar (the same unit u))`

**Return type**: [Scalar (the same unit u)](./types.md#Scalar)

**Returns**: The average value of `v_1`, `v_2`, ... `v_n`.

* `mid(P_1: Point, P_2: Point, ..., P_n: Point)`

**Return type**: [Point](./types.md#Point)

**Returns**: The middle point of `P_1`, `P_2`, ... `P_n`. Special cases: when `n=2`, the middle of a segment; When `n=3`, the centroid of a triangle.

## `parallel_through` (alias `parallel`)

* `parallel_through(P: Point, k: Line)`
* `parallel_through(k: Line, P: Point)`

**Return type**: [Line](./types.md#Line)

**Returns**: a line parallel to `k`, passing through `P`.

## `perpendicular_through` (alias `perpendicular`)

* `perpendicular_through(P: Point, k: Line)`
* `perpendicular_through(k: Line, P: Point)`

**Return type**: [Line](./types.md#Line)

**Returns**: a line perpendicular to `k`, passing through `P`.

## `point`

* `point()`

**Return type**: [Point](./types.md#Circle)

**Returns**: an adjusted (free) point.

## `radians` (alias `rad`)

* `radians(value: Scalar (no unit))`

**Return type**: [Scalar (angle)](./types.md#Scalar)

**Returns**: an angle with the given measurement in radians. Related: [degrees](#degrees)

* `radians(value: Scalar (angle))`

**Return type**: [Scalar (no unit)](./types.md#Scalar)

**Returns**: the value of the angle in radians. Related: [degrees](#degrees)

## `radius`

* `radius(circle: Circle)`

**Return type**: [Scalar (distance)](./types.md#Scalar)

**Returns**: the radius of the given circle.

## `segment`

* `segment(AB: 2-P)`
* `segment(A: Point, B: Point)`

**Return type**: [Segment](./types.md#segment)

**Returns**: the segment `AB`.

**Displays**: the segment `AB`.

The function accepts additional properties in the form of:

```rust
struct Segment {
    display_segment: bool, // Default: true,
    style: Style, // Default: SOLID
}
```

`display_segment` decides whether the segment should be displayed and `style` decides how it should be displayed.

## `x`

* `x(P: Point)`

**Return type**: [Scalar (distance)](.types.md#Scalar)

**Returns**: The `x` coordinate of the point.

## `y`

* `y(P: Point)`

**Return type**: [Scalar (distance)](.types.md#Scalar)

**Returns**: The `y` coordinate of the point.
