# AKLV polynomial coefficients and ground-state filters

This change supplies the finite-dimensional algebra used in AKLV,
arXiv:1301.1162v1, Section 4, Lemmas 4.1 and 4.2 (`l:agsp`), source
`1dfrustrated34.tex`, lines 530–663. It was extracted from the completed
area-law development and checked against the current public library.

For a distinguished interaction occurring k times and ordinary interactions
with total frequency m, the weighted coefficient sum has operator Schmidt
rank at most the number of ordinary frequency vectors times
`choose (m + 2*k + 1) (2*k + 1) * r^k`. The corrected count is documented in
`docs/paper-gaps/aklv13_interpolation_and_word_count.tex`. Arbitrary scalar
weights and dependent coefficient matrices are allowed.

The change also identifies these coefficients with full-frequency word sums,
partitions a Hamiltonian power by a minimum-frequency interaction, and proves
the numerical bounds used to shorten a window. For a Hermitian matrix with a
unit ground vector, positive projector gap, and spectral upper bound, the
constructed Chebyshev polynomial fixes the ground vector and suppresses its
orthogonal complement. Chain geometry and the final physical rank estimate
are developed in TNLean.

The former private `rank_weighted_sum_of_injective_monomials` proof is moved
to `Matrix.operatorSchmidtRank_sum_smul_le_of_injective_monomial_evaluations`;
both the one- and two-distinguished-interaction estimates use it. No public
declaration is removed.

## Verification

- Targeted Lake builds cover the coefficient, counting, ground-filter, and
  refactored two-interaction modules.
- Changed mathematical modules are checked with strict implicit arguments,
  Mathlib standard linters, warnings as errors, and synthesis depth three.
- The six principal coefficient, partition, counting, and filter results have
  only `propext`, `Classical.choice`, and `Quot.sound` as kernel axioms.
- Blueprint/source synchronization and generated import checks pass.
- Changed source contains no proof placeholders or additional axioms.

The finite-dimensional results do not assert an entropy bound, an MPS
approximation theorem, or an algorithmic running time.
