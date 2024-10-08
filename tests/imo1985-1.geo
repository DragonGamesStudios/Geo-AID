# A circle has center on the side AB of the cyclic quadrilateral ABCD. The other three sides are tangent to the circle.
# Prove that AD + BC = AB.

let A, B, C, D = Point();
ABCD lies_on Circle();

let X [display = false] = intersection(bisector(BCD), bisector(CDA)) lies_on Segment(AB);
let omega = Circle(X, dst(X, DC [display = false]));

?Segment((BC, CD, DA));