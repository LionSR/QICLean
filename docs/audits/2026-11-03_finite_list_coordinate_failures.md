# A finite list of coordinate failures

The new theorem `MeasureTheory.Measure.pi_biUnion_list_le_of_update_sections`
bounds the union of a finite list of measurable events by the list length
times a common bound on their true one-coordinate update sections. The
coordinate index is finite; labels may have any type. Only listed labels
must have measurable events and satisfy the section bound. Repeated labels
are allowed and counted by their occurrences. Empty lists and empty label
types require no separate hypothesis.

The proof applies the existing arbitrary-finite-index update theorem to each
event and binary union subadditivity in a list induction. The previously
frozen update and finite-ordinal section theorems remain unchanged active
dependencies. This auxiliary supports ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817; it does not assume or construct an
adaptive process.

The actual-name strict check passed in 3.585 seconds against immutable
TNLean `435cbe7fe53e5d3a04c1b8eb2382753749f21a64` and its own
QICLean `b2ea12a0139820758e161514968ed9ead661c5a7` package, with the frozen
section theorems as explicit source/object overrides. Three selected QIC
dependency pairs and all build inputs were guarded. Default elaboration
options were retained. The imported foundation inspection uses only `propext`,
`Classical.choice`, and `Quot.sound`; its temporary source was deleted.
Source/blueprint synchronization, reader prose, generated imports, proof
integrity, whitespace and pattern checks passed. The new mathematical entry
was rendered and inspected. Exact hashes, timing and check records are in
the verification manifest. No provider, cache, dependency pin,
or Mathlib source was changed or built. Ordinary combined compilation and
compiled blueprint declarations remain integration checks.
