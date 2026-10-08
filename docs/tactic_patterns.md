# Tactic pattern ledger

Record repeated proof patterns before introducing a new tactic. Prefer an
existing theorem, then a reusable lemma or simp set; promote a new abstraction
only after at least three genuine occurrences across two files. Occurrences
in a regression file are not additional mathematical consumers.

## Promoted

No new tactic or automation is introduced for shifted spectral truncation.
The proofs reuse existing functional-calculus identities, projection
rank/trace comparison, range-of-composition, and scalar real-power bounds.

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

### Exponential on an actual joint label resolution — candidate (2026-10-08)

- **Pattern:** Construct a joint resolution from commuting actual label projections, identify its marginal observables using the projection sums, and apply `Matrix.IsOrthogonalResolution.exp_hom` before a positive-dimension scalar logarithm calculation.
- **Seen:** `Representation/SchurSurprisal.lean` and `Representation/MergeExponential.lean`; two mathematical exponential calculations in two files.
- **Abstraction:** The existing resolution homomorphism and `exp_hom` already supply the functional-calculus step. Continue using these results and finite-sum identities; no additional tactic or duplicate spectral calculus is introduced.
- **Caveat:** Derive the joint resolution from the actual projections. Positive irreducible dimensions justify the logarithms even when their ambient label projections vanish.

### Positive weighted trace of a difference square — candidate (2026-10-08)

- **Pattern:** Apply positive-semidefinite trace positivity to `(U - V)ᴴ * (U - V)`, then use Hermitian symmetry and commutation to identify the product terms and obtain the arithmetic-mean bound.
- **Seen:** `Analysis/WeightedTraceExponential.lean`; one calculation, reused for exponential matrices in the same file.
- **Abstraction:** The private product inequality isolates this calculation. Existing `Matrix.PosSemidef.trace_mul_nonneg` and exponential commutation identities supply the mathematical steps; no new tactic is needed.
- **Caveat:** Commutation of the two factors is a hypothesis, while no commutation with the positive semidefinite trace weight is used.
