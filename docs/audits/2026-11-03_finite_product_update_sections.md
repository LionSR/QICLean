# Uniform update sections at an arbitrary finite coordinate

`MeasureTheory.Measure.pi_le_of_update_sections` applies to a family of
probability measures indexed by any finite type. For a measurable event,
a uniform bound on every section obtained by changing one coordinate of a
whole tuple bounds the measure of that event by the same number.
In particular the index may be the pair of chain endpoints; it need not
already be an initial interval of the natural numbers.

The proof uses a measure-preserving finite enumeration and the existing
`pi_le_of_coordinate_sections` theorem, which remains unchanged and is an
active dependency. A coordinate value needed to fill a remaining-coordinate
tuple is derived from its probability law. There is no additional
nonemptiness hypothesis and no second probability measure construction.
Dependent coordinate spaces are retained throughout. The event itself must
be measurable; the statement does not assume the desired bound on its
measure.

This is a measure-theoretic auxiliary supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817. It does not by
itself construct an adaptive process or establish its success probability.
