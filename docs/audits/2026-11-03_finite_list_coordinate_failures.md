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
