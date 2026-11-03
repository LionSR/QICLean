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

The actual-name strict check passed in 3.612 seconds against the immutable
TNLean `435cbe7fe53e5d3a04c1b8eb2382753749f21a64` provider and its own
QICLean `b2ea12a0139820758e161514968ed9ead661c5a7` package, with the frozen
finite-coordinate section theorem as an explicit source/object override.
The check guarded both selected QIC dependencies and all build inputs.
Default elaboration options were retained. The imported foundation inspection passed in 3.449 seconds, using only
`propext`, `Classical.choice`, and `Quot.sound`; its temporary source was
deleted. Source/blueprint synchronization, reader prose, generated imports,
proof-integrity, whitespace and pattern checks passed. A one-page reader
rendering was inspected. Exact hashes and check records are in the
verification manifest. No provider,
cache, dependency pin, or Mathlib source was changed or built. Ordinary
combined compilation and compiled blueprint declarations remain integration
checks.
