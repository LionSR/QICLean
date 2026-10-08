# Tactic pattern ledger

Record repeated proof patterns before introducing a new tactic. Prefer an
existing theorem, then a reusable lemma or simp set; promote a new abstraction
only after at least three genuine occurrences across two files. Occurrences
in a regression file are not additional mathematical consumers.

## Promoted

No new tactic or automation is introduced for shifted spectral truncation.
The proofs reuse existing functional-calculus identities, projection
rank/trace comparison, range-of-composition, and scalar real-power bounds.

### Unit-blank contraction in restoration — promoted lemmas (2026-10-08)

- **Pattern:** Expand restoring matrix entries and contract unit ancillary
  blanks through `∑ i, star (b i) * b i = 1`.
- **Seen:** The copied-vector identity in `RestoringVectors.lean` and the actual
  ground-component coefficient proof in `RestoringGroundComponent.lean`.
- **Abstraction:** Promote the already proved blank normalization and restoring
  entry formula as `restoringBlank_sum_eq_one` and
  `restoringOperatorWithAncilla_apply`, preserving their existing proof bodies.
  The new coefficient proof reuses both instead of duplicating those expansions.
- **Caveats:** Blank norms are Euclidean. The copied ancillary coordinate runs
  over the whole basis, including coordinates with zero assigned probability.

## Candidates

### Commutation with a matrix inverse — candidate (2026-10-07)

- **Pattern:** Give a positive definite matrix its existing `Invertible`
  instance, use `Commute.invOf_right` or `commute_invOf`, and rewrite
  `Matrix.invOf_eq_nonsing_inv`.
- **Seen:** Three inverse-commutation steps in
  `QICLean/Analysis/PatchRegulator.lean`; one file.
- **Abstraction:** The existing Mathlib commutation lemmas suffice. Retain
  this record until independent occurrences in another file justify a
  matrix-specific lemma; no new tactic is introduced.

### Finite-spectrum functional-calculus scalar reduction — candidate (2026-10-07)

- **Pattern:** Rewrite matrices as Hermitian functional calculi, combine
  products with `← hA.cfc_mul`, and reduce the equality to a pointwise
  threshold split followed by scalar simplification.
- **Seen:** In `QICLean/Analysis/ShiftedDensityTruncation.lean`,
  `IsHermitian.isStarProjection_spectralProjectionGE`,
  `PosSemidef.commute_add_smul_one_rpow_spectralProjectionGE`,
  `PosSemidef.shiftedPowerHead_eq_cfc`, and
  `PosSemidef.shiftedPowerHead_mul_shiftedPowerTail` are representative
  occurrences. Their scalar conclusions differ.
- **Abstraction:** Continue using the existing `Matrix.IsHermitian.cfc_mul`
  and `cfc_congr` results. A specialized automation rule is not justified
  by repetition in this single module.
- **Caveats:** Continuity is required only on the finite spectrum. Do not
  claim global continuity of a threshold indicator. Nonnegativity and
  norm estimates still require the correct PSD and exponent hypotheses.

### Reverse range inclusion from a commuting inverse — candidate (2026-10-07)

- **Pattern:** Prove both range inclusions from H = ΠF and Π = HF⁻¹, using
  `LinearMap.range_comp_le_range` after translating matrix products.
- **Seen:** The two inclusions in
  `Matrix.PosSemidef.range_shiftedPowerHead`; one mathematical consumer
  in one file.
- **Abstraction:** Keep the existing range-of-composition theorem. The
  public range equality is the reusable mathematical result; introducing
  another tactic would not remove independent repeated work.
- **Caveats:** Commutation and the actual inverse identity are proved before
  use. Neither an abstract range certificate nor invertibility of the
  unshifted PSD matrix is assumed.

### Sector mass from a finite resolution — candidate (2026-10-07)

- **Pattern:** Restrict trace masses to the nonzero projections, use positivity
  and completeness to obtain a nonempty set of total mass one, and apply
  `Finset.exists_le_of_sum_le` with a bound on the number of projections.
- **Seen:** `TensorPower.exists_labelProj_trace_mass_ge` in
  `QICLean/Representation/SchurSectorMass.lean`; one mathematical consumer.
- **Abstraction:** Reuse the existing finite-sum comparison theorem. The
  projected-vector result applies this trace result to the actual reduced
  state and uses the trace-pairing and Hermitian-idempotent norm identities.
  No new tactic is needed.
- **Caveats:** The sector count gives a mass bound only; an entropy window
  requires a separate concentration estimate and a restricted selection.
### Contraction of the repeated uniform pair — candidate (2026-10-07)

- **Pattern:** Expand a Kronecker action against the actual repeated uniform
  pair, rewrite its coordinates as a scalar times the equality indicator,
  and contract one coordinate sum.
- **Seen:** The two private coordinate identities in
  `QICLean/Representation/UniformBellLabel.lean`; two occurrences in one file.
- **Abstraction:** The public projected-norm and nonzero-occurrence theorems
  supply the mathematical consequences. A separate tactic is not warranted
  by two coordinate contractions.
- **Caveats:** The normalization depends on the actual one-copy dimension;
  nonzero occurrence requires that dimension to be positive. The central
  Schur label equality additionally uses inversion-invariant coefficients.
