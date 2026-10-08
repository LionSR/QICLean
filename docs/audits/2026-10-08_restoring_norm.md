# Singular restoring operator norm bounds

The new `QICLean.Entropy.RestoringNorm` module proves the first estimate in
`09-amplification.tex:374–397`, pinned at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The actual weighted block sum obeys

`restoringGram E p Q T ≤ (cX * cQ * cY) • 1`

from the selected inverse-probability bound, `Q ≤ cQ • ρ`, and
`T * partialTraceLeft ρ * T ≤ cY • T`. Its proof first bounds selected
positive blocks by the full partial trace and then applies positive
compression. `Q` and `T` are orthogonal projections; the constants are
nonnegative. The Gram-order theorem is stronger than needed: positivity of
selected probabilities is needed only in the operator Gram identities and
norm results, not in this order comparison.

The checked Gram identities now yield actual Euclidean operator norm bounds
for `restoringOperator` and `columnOperator`. Unit blank vectors give
outer-product projections below the identity. Positivity of tensor products
bounds each actual Gram matrix, and the C*-norm-square identity gives
`sqrt (cX * cQ * cY)`. A general Kronecker norm equality is unnecessary.

The source specialization uses exactly
`cX = exp (SX + w)`, `cQ = exp (SXY + w)`, and
`cY = exp (-SY + w)`. With `I = SX + SXY - SY`, both bounds become
`exp ((I + 3 * w) / 2)`, with no extra factor.

No full-rank, unselected-probability positivity, projector-commutation,
assumed Gram-bound, assumed norm-bound, or `Nonempty` hypothesis is added.
The unit blanks use their Euclidean norm directly. The column definition
continues to sum over the full ancillary basis.

## Validation

The exact commands, exit codes, and source checksums are in
[`2026-10-08_restoring_norm.json`](2026-10-08_restoring_norm.json).

- Strict warning-as-error compilation of the implementation passed.
- The targeted Lake build passed: 3098/3098 jobs, with only the new module built.
- Six finite consumers passed strict compilation: a zero-probability physical
  coordinate, the actual weighted Gram attaining one, both exponential norm
  bounds with complex blank phases, an empty physical system, explicitly
  noncommuting spectral projectors, and a sharper `sqrt (1/2)` norm bound for
  those projectors.
- Guarded and independent raw axiom reports for every public declaration list
  only `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff --check` passed.

This is targeted validation, not a full project rebuild. Import-router and CI
registration belong to the integrating task. Dependency/toolchain pins,
shared modules, and external repositories were unchanged.
