# Mathlib 4.35 replacement audit

Date: 2026-09-25.

This audit records Mathlib material that became available between Mathlib
`v4.34.0-rc1` and `v4.35.0-rc3` and compares it with QICLean's local
infrastructure. It is the first such audit for QICLean. The `v4.35.0-rc1`
upgrade changed toolchain pins only, so the comparison range starts at the last
pin that was audited, the TNLean `v4.34.0-rc1` baseline.

## Dependency pins and comparison range

- Lean: `leanprover/lean4:v4.35.0-rc3`;
- Mathlib: `v4.35.0-rc3`, commit `c55e6e786f49471c72fbddbec5415808896aec1e`;
- baseline: Mathlib `v4.34.0-rc1`, commit
  `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`;
- Gametheory: unchanged at `ec93e4daed4ad8b4784a9d760e492832e7711433`.

The range contains 1,207 non-merge commits. The audit split the Mathlib tree
into three slices: linear algebra, abstract algebra, and matrices; analysis,
topology, and dynamics; and data, order, logic, combinatorics, and tactics. For
each slice it listed the added declarations, separated genuinely new names from
moved ones by checking the baseline tree, and matched the new names against
QICLean by name and by statement shape. A candidate was accepted only when the
Mathlib statement implies the local one under the same or weaker hypotheses.

## Summary

The range contains no module-level replacement for QICLean. It contains one
declaration-level replacement and five proof-level simplifications, removing
30 lines net.

1. Mathlib's `Matrix.col_mul_eq_mulVec_col` replaces the local square complex
   `Matrix.col_mul`.
2. `Multiset.nnnorm_prod` replaces a multiset induction bounding the norm of a
   product of eigenvalues.
3. `ZMod.neg_one_eq_one_iff` replaces a divisibility argument that `-1 ≠ 1` in
   `ZMod d` for `d ≥ 3`.
4. `tendsto_nhds_unique_of_forall` removes an intermediate `congr'` limit.
5. `Finset.sum_sq_eq_zero_iff` removes two nonnegativity side arguments.

## Column of a matrix product

Mathlib commit `f965aad7c52`, `feat: supporting API for Cartan matrix
realisations (#43460)`, adds

```lean
theorem Matrix.col_mul_eq_mulVec_col {M : Matrix l m R} {N : Matrix m n R} {i : n} :
    (M * N).col i = M *ᵥ N.col i
```

in `Mathlib.Data.Matrix.Mul`, for any non-unital non-associative semiring and
rectangular shapes, proved by `rfl`. The local `Matrix.col_mul` in
`QICLean/Algebra/MatrixMulRange.lean` stated the square complex case and was
used only in `mem_range_mulLeft_iff_cols` in the same file. The local lemma is
deleted and both uses cite the Mathlib lemma. TNLean does not use it.

## Norm of a multiset product

Mathlib commit `f80bb87e4c`, `feat(Analysis/Normed): norm and {List,
Multiset}.prod commute`, adds `Multiset.norm_prod` and `Multiset.nnnorm_prod` for
rings with `NormMulClass`. The body of
`ChannelDeterminant.Internal.norm_prod_le_one_of_forall_mem'` in
`QICLean/Channel/Determinant/Bound.lean` now rewrites the norm of the product
as the product of norms and applies `Multiset.prod_le_pow_card`, replacing the
multiset induction.

## Negative one in `ZMod`

Mathlib commit `f59c32e784e`, `feat(NumberTheory): define Carmichael numbers
(#42801)`, adds

```lean
lemma ZMod.neg_one_eq_one_iff {n : ℕ} : (-1 : ZMod n) = 1 ↔ n = 1 ∨ n = 2
```

in `Mathlib.Data.ZMod.Basic`. In `haCyclicWeight_mul_star`
(`QICLean/Channel/ChoiTypeMap/HaBlockTranspose.lean`), the eight-line proof of
`(-1 : ZMod d) ≠ 1` through integer divisibility is now a case split on this
equivalence, closed by `omega` from `3 ≤ d`.

## Limits and sums of squares

Mathlib commit `f86d48590e`, `feat(Topology/Separation/Hausdorff): add
tendsto_nhds_unique_of_forall`, compares two limits of pointwise equal
functions directly. It replaces a `tendsto_const_nhds.congr'` intermediate in
`QICLean/Channel/Peripheral/CesaroRecurrence.lean`.

Mathlib commit `cae66e9de4e`, `feat: add zero lemmas for even powers (#43161)`,
adds `Finset.sum_sq_eq_zero_iff` for linearly ordered semirings. It replaces a
`sum_eq_zero_iff_of_nonneg` argument with an explicit `sq_nonneg` witness in
`QICLean/Algebra/FiniteCauchySchwarz.lean`, and a squared-norm step in
`QICLean/Channel/Schwarz/PetzEqualityPrerequisites.lean`.

## Deprecations without replacement

Mathlib replaced the set-valued standard simplex `stdSimplex 𝕜 ι` by the type
`Convexity.StdSimplex 𝕜 ι` (deprecated since 2026-08-29), together with
`isClosed_stdSimplex`, `isCompact_stdSimplex`, and
`stdSimplexHomeomorphUnitInterval`. The deprecated names still elaborate, and
four modules use them: `Analysis/ConvexHullCompact`, `Analysis/CyclicReciprocal`,
`Channel/ChoiTypeMap/YamagamiPositivity`, and `Topology/BrouwerProduct`.

The new API does not shorten these proofs. `Topology/BrouwerProduct` depends on
Gametheory's `ProductSimplices`, which is defined through the set-valued
simplex, so it cannot migrate before Gametheory does. The other three modules
use closedness and compactness of subsets of `Fin N → ℝ` or `ZMod N → ℝ`; the
type-valued simplex would add a coercion layer through its weights without
removing an argument. Mathlib still has no compactness theorem for convex hulls
of compact sets in finite dimension, so `IsCompact.convexHull` remains local.
The migration is recorded as follow-up work and is not part of this upgrade.

`spectralRadius` is now defined over the quasispectrum. QICLean's unital uses
are unaffected because `spectralRadius_eq_of_unital` recovers the spectrum
form.

## New APIs that do not replace QICLean mathematics

The audit checked and rejected the following additions:

- `Matrix.IsHermitian.star_dotProduct_mulVec_comm` has a Hermitian hypothesis
  that QICLean's general adjoint-transfer lemmas in `Algebra/MatrixAux` do not
  carry.
- `Matrix.PosDef.star_dotProduct_mulVec_mul_le` requires an ordered ring, which
  excludes complex matrices.
- the positive-definite `mulVec` injectivity lemmas have no local counterpart;
  QICLean's injectivity proofs concern isometries.
- `quasispectrum_smul` does not give QICLean's `spectralRadius_smul`.
- `IsUnit.one_sub_of_norm_lt_one` and `hasSummableGeomSeries_iff_isUnit` are
  qualitative; the quantitative Neumann bounds in `Analysis/NeumannInverse`
  have no Mathlib counterpart.
- the new positivity API for continuous functionals on a C*-algebra does not
  apply to maps between matrix algebras or to functionals on an operator
  system.
- `cfcHomTransfer` transports a continuous functional calculus instance and
  does not shorten `Analysis/CfcConjugation`.
- `map_comp_birkhoffAverage` and `birkhoffAverage_apply_of_comp_eq` could
  replace the trace computation in
  `IsTracePreservingMap.meanErgodicProjection_isTracePreservingMap`, but the
  resulting term was ill-typed and took over ten minutes to elaborate, so the
  local proof was kept.
- `Subalgebra.map_center_eq` would save at most two lines in
  `Algebra/StarSubalgebraFactor` and was not applied.

## Validation

`lake build` completes on `v4.35.0-rc3` (9,597 jobs). The only warnings are the
`stdSimplex` deprecations listed above.
