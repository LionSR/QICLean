# The selected Schmidt coordinate space

The source is OpenAI, *A two-dimensional area law from a global spectral gap*
(September 24, 2026), `07-comparators.tex`, lines 240–247 and
`comparator:post-marginal`, at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
`source-comparison.json` records the immutable manuscript blob and confirms
that its bytes agree with the local mathematical source.

The complete production source revision is
`7076296aad42492bccb9b3bb321ca12b5565d0e9`, based on the published parent
`3446fccdbe72e932aa9479c146c7f3d1b4faee88`.
For the actual left marginal of a bipartite vector, the selected columns of
its spectral unitary define an isometry from the coordinate space indexed by
the selected set. Its range projection is the existing spectral selection.
The coefficient matrix of the compressed vector is the original coefficient
matrix multiplied on the left by the adjoint of this isometry and divided by
the square root of the selected mass.

Embedding this vector recovers the actual typical truncation. The selected
marginal is the diagonal matrix of selected eigenvalues divided by their
total mass. The whole complementary marginal is unchanged, so every further
partial trace on the complement is unchanged as well. Positive selected mass
gives norm one. These conclusions require no supplied Schmidt decomposition,
full-rank assumption or normalization of the original vector. The selected
coordinate space has dimension equal to the cardinality of the selected set;
positivity of each selected eigenvalue is not required here.

`verification.json` binds the entire production file, including both private
auxiliary proofs, and the unique mathematical blueprint fragment by SHA256.
`build.log` records the successful package target, with 3,273 jobs and 3.9 seconds
for the new module. `strict-source.log` records successful elaboration with
warnings as errors, strict implicit arguments and the standard Mathlib
linter set. `axioms.log` records all eight public declarations, including both
definitions; every report contains only `propext`, `Classical.choice` and
`Quot.sound`. The diagnostic source disables only the linter against hash
commands. `provenance.log` records validation of all eight declaration entries,
their committed source bytes, independence notices and hashed verification logs.

All proofs were independently written from the manuscript; no upstream Lean
proof text was reused. Codex (GPT-6) assisted the formalization. The selected
space construction has no dependence on the Schur-label development, regional
selection additions or commutation additions. This result supplies only the
selected-space relabeling used by the comparator argument. Bell contraction,
tensor powers, sector estimates and the full area law remain separate results.

The blueprint fragment is `blueprint/src/fragment/typical_pure_compression.tex`.
Root import and chapter inclusion, a combined full-library build, and complete
blueprint PDF, web and declaration checks remain for integration. No complete
build or publication check is claimed by this evidence.
