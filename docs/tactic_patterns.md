# Tactic pattern ledger

Record repeated proof patterns before introducing a new tactic. Prefer an
existing theorem, then a reusable lemma or simp set; promote a new abstraction
only after at least three genuine occurrences across two files. Occurrences
in a regression file are not additional mathematical consumers.

## Promoted

No new tactic or automation is introduced for shifted spectral truncation.
The proofs reuse existing functional-calculus identities, projection
rank/trace comparison, range-of-composition, and scalar real-power bounds.

### Operator norm in orthonormal coordinates — promoted (2026-10-08)

- **Pattern:** Identify the matrix of a continuous linear map in finite
  orthonormal input and output bases, then transfer its operator-norm bound.
- **Result:** `ContinuousLinearMap.norm_toMatrix_orthonormal` in
  `QICLean/Analysis/OrthonormalMatrixNorm.lean` gives equality of norms.
  It reuses Mathlib's Euclidean matrix norm and invariance under composition
  with linear isometric equivalences. Rectangular matrices and empty bases
  require no separate cases.
- **Consumers:** TNLean's `Word.norm_preparedMatrix_le_one`,
  `Word.norm_freeSourceMatrix_le_one`, and the new
  `Word.norm_physicalOutputMatrix_le_one` in `ExteriorSourceContraction`.
- **Decision:** The third application justifies one general equality. The
  prepared TNLean refactor removes the two older coordinate-vector proofs;
  it will be applied together with the dependency update. No custom tactic
  or duplicate coordinate-norm theorem is introduced.

## Candidates

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
