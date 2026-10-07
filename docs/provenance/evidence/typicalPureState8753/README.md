# Typical Schmidt truncation of a bipartite pure state

The mathematical source is OpenAI, *A two-dimensional area law from a global
spectral gap* (September 24, 2026), at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, `07-comparators.tex`, lines 240–247
and equation `comparator:post-marginal`. The production source revision is
`42f0b20238cc164e912f7d73ce6a33239a581e52`.

For an actual bipartite pure vector, its first marginal supplies the spectral
projection and selected mass. Acting with the projection on the first tensor
factor and dividing by the square root of the mass gives the actual selected
vector. Its first marginal is the existing normalized spectral restriction.
Its complementary marginal satisfies the exact selected/discarded decomposition,
the positive-semidefinite upper bound, and the entropy bound from the source.
The vector overlap and squared error are also computed exactly.

The normalization and marginal identities only require positive selected mass;
the squared-error estimate and complementary entropy estimate additionally
require an original unit vector. No full rank, ordering of dimensions, assumed
Schmidt coordinates, or supplied entropy conclusion occurs. The complementary
remainder stays unnormalized, so selected mass one introduces no extra case
hypothesis. The independently formalized adjusted entropy of every positive
remainder is nonnegative, including a zero remainder.

`build.log` records the Lake target. `strict-source.log` records a direct source
check with warnings as errors, the standard Mathlib linters, and strict implicit
arguments. Both passed. `axioms.log` contains all 13 exact public declarations,
including the two definitions; every record contains only `propext`,
`Classical.choice`, and `Quot.sound`. The audit file disables only the linter
against diagnostic hash commands, since these commands are its purpose.
`regressions.log` records full selection on a two-dimensional factor with a
one-dimensional complement (so the first marginal is singular), and empty
selection. Both passed under the same strict options.

The new blueprint fragment is `ch12_entropy_typical_pure_state.tex`. Its inclusion,
root imports, full-library build, and global blueprint checks belong to the
combined integration branch. The source does not assert the full norm-comparison
proposition, nor the relabeling or Schur-sector arguments that follow the selected
Schmidt-vector construction.

Codex (GPT-6) assisted this independently written formalization. No upstream Lean
proof text was copied or adapted. The per-declaration original-source notices and
hashed evidence are recorded in `typicalPureState8753.json`.
