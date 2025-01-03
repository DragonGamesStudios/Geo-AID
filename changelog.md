## Version 0.7.1

- **GeoScript**: More functions for triangles and circles.

## Version 0.7.0

- **GeoScript**: Function, rule, and property names now ignore casing of letters and underscores.
- **GeoScript**: Trigonometry functions were added.
- **GeoScript**: Complex numbers are now supported.
- **GeoScript**: Isometric and similar transforms were added (homothety, rotation, reflection, translation and composition of these)
- **GeoScript**: Area functions are now supported, both absolute and signed.
- **GeoScript**: Shorthands for polygons and convex polygons were added.
- **GeoScript**: Let statements now support display properties.
- **GeoScript**: Let statements now only support one rule. Decision was made to avoid conflicts with:
- **GeoScript**: Rule chains were added to the language (e.g. `a < b < c`).
- **GeoScript**: Field syntax was removed from the language in favor of methods, all for the sake of consistency.
- **GeoScript**: Function and method aliases are now supported.
- **GeoScript**: More, various functions were added.
- **GeoScript**: Added a "point collection lies on line" rule, ensures the order of points.
- **GeoScript**: Fixed a critical bug, that caused decimal numbers to be read incorrectly.
- **GeoScript**: `mid` for a point collection with 2 points now returns the midpoint, rather than the distance.
- **GeoScript**: Multiple functions are now generic over point collection length.
- Fixed various other bugs.
- Multiple improvements for further development.

## Version 0.6.0

- **Interface**: The command line interface changed to support generating output in multiple formats.
- **Interface**: Fixed figure sizing.
- **Geogebra Format**: Support for Geogebra format introced.
- **GeoScript**: `mid`, when given a single point collection of length 2, now returns the midpoint of the segment.
- **GeoScript**: Fixed various conversion false positive diagnostics.
- **Projector**: When creating circle items, the radius will now always be non-negative.

## Version 0.5.1

- **Glide**: Fixed that Glide wouldn't actually try to optimize the figure (a typo).
- **Compiler**: Fixed that zero-distance optimisation would return false negatives when
  it should be applied and lead to stack overflow when it shouldn't.
- **Debugger**: The debugger is now a part of the monorepo and has a different function.
- **GeoScript**: Removed the `identical_expressions` flag as it no longer had any effect.
- **GeoScript**: Replaced `point_bounds` with `point_inequalities`. The former was not functional
  or useful. The latter is enabled by default and disabling it might be desirable.

## Version 0.5.0

- **Rage**: Added *strictness* parameter controlling how strict the rules are to be treated.
- **GeoScript**: Fixed bugs
    - Errors regarding unexpected or repeated display options now show squiggles in the right place
    - Accessing fields on single-point point collections no longer yields errors
    - Single-point point collections on the right hand side of a let statement are no longer considered ambiguous
    - Using display options on a rule is now parsed correctly, rather than throwing a syntax error
    - Using name identifiers on the left side on a single-point point collection assigning let statement no longer
      yields errors.
- **Glide**: Added a new gradient descent based engine that should generally perform better than Rage and made it a new
  default.
- **Book**: Updated the book.

## Version 0.4.2 (2024.07.30)

- **All**: Full reorganization of the repository.
- **Rage**: Modified the public API.

## Version 0.4.1 (2024.07.10)

- **All**: Generated figure format (datatype) is now in its own library, including math strings. Drawers now use that,
  rather than a private type.
- **All**: The organization of the repo changed. Everything is now in a single repository.
- **All**: Versioning is modified for `geo_aid_derive` to match Geo-AID's.
- **All**: Licensing is less aggressive now (license did not change, placement did).
- **JSON**: A schema is now available at the repository root.
- **Other**: The `test` directory is now licensed under CC0.
- **Other**: Fixed the ordering of the change log

## Version 0.4.0

- Completely changed how figures are generated, a new design around generation engines, additional processing stage.
- Removed the current weight system, as it was hurting the generation.
- Figures now generate way, way faster.

## Version 0.3.1

- **GeoScript**: Added custom weighing
- **GeoScript**: Added exponentiation support and rational unit powers
- **GeoScript**: Added fields and methods to the language
- **GeoScript**: Modified the syntax of negation and exponentiation
- **Drawers**: Refactored drawers for better maintenance capability

## Version 0.3.0

- Rewrote the entire display system (deciding what is displayed and what is not, based on the script)
- Added smart label positioning
- Point collection variables are no longer valid.

## Version 0.2.6

- Added drawing modes for lines, segments, rays, angles and circles (dashed, dotted, bolded, default)
- Fixed that any file involving the `lies_on` rule would inevitably crash because of point equality prevention rules.
- Fixed that negating some normal rules would not actually negate them.
- Fixed that negating `lies_on` would not actually negate it (no effect would be achieved).
- The `svg` drawing option is now default.
- Updated README to contain information about the book.

## Version 0.2.5

- Huge compiler & generator refactor
- A point laying on two lines is now defined as an intersection of them.
- Added proper documentation.

## Version 0.2.4

- Added the circle clip and the line clip
- Added basic bundle type support
- Added the `Segment` function
- Added the `lies_on` operator for points on circles, lines and segments.

## Version 0.2.3

- Added ray support.
- Added circle primitive and function.
- Added circle support and improved latex drawer.
- Heavily changed the display system.

## Version 0.2.2

- An overhaul of expressions with proper value caching and precomputed weights.
- Improved angle support.
- Added segment support.

## Version 0.2.1

- Added testing environment for the projector and drawers
- Added testing environment for Geo-AID in general.
- Added support for multiple iteration levels in iterators
- Changed implicit iterators from being separated with `|` to being separated with `,`.
- Fixed faulty display of multiline error messages.
- Added command line options for JSON and raw drawers.
- Added builtin functions: bisector, mid (average), parallel, perpendicular, intersection
- Added point collection constructors.
- Added parser support for compiler flags.
- Added identical_expressions optimization flag, allowing to optimise for calculating identical expressions.
- Improved generator-projector pipeline.
- Distance literals now work properly.
- Error messages now can suggest code changes.

## Version 0.2.0

- Refactored svg.rs to optimize the rendering
- Created the latex drawer
- Completed the documentation as of now.
- Added a Command Line Interface
- Pretty error printing
- Added the JSON drawer
- Added the raw drawer
- Added angle support
- Fixed draw signatures
- Added benchmarking for generation

## Version 0.1.0

- Primitive GeoScript
- Primitive figure rendering
- Basic generation
