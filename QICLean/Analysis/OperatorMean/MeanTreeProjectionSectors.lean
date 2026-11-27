/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.FiniteTree
import QICLean.Analysis.FunctionalCalculus.OrthogonalResolutionCfc
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import QICLean.Analysis.OperatorMean.MeanTreeLogFloorExp
import QICLean.Analysis.FunctionalCalculus.MatrixPowers
import QICLean.Analysis.Order.FloorPin
import QICLean.Analysis.Logarithm.InversePowerLogJensen

/-!
# Weighted means on two complementary projection ranges

Let `P` be an orthogonal projection. Suppose that each leaf of a weighted
mean tree is scalar on the range of `P` and on its orthogonal complement,
with the same positive scalar `b` on the complement. The root has scalar
`b` on the complement and the weighted geometric mean of the leaf scalars
on the range of `P`.

This identity and monotonicity pass a two-sector lower comparison through
the tree. The original leaf operators need not commute with `P` or with
each other. Repeated leaf labels and zero edge weights are permitted.

It also contains the following results.

* `Matrix.MeanTree.log_projection_sectors_le_log_eval`,
  `Matrix.MeanTree.re_dotProduct_log_eval_ge_of_projection_mass`: logarithmic lower bounds from two
  projection ranges.

## Main results

* `Matrix.MeanTree.mul_sum_log_lower_le_neg_log_norm_sq_of_projection_lower_bound`,
  `Matrix.MeanTree.explicit_lower_norm_of_exponential_projection_lower_bound`: the explicit lower
  norm rate from exponential projection bounds.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 603–621, in the proof of
  `comparator:tree-log-lower`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

section MeanTreeProjectionSectors

section MeanTreeProjectionSectors

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem projection_sectors_mul {P : Matrix n n ℂ}
    (hP : IsStarProjection P) (a b c d : ℝ) :
    (a • (1 - P) + b • P) * (c • (1 - P) + d • P) =
      (a * c) • (1 - P) + (b * d) • P := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hP.one_sub.isIdempotentElem.eq, hP.isIdempotentElem.eq,
    hP.mul_one_sub_self, hP.one_sub_mul_self, smul_zero, add_zero, zero_add]
  rw [mul_comm c a, mul_comm d b]

/-- Positive scalar values on two complementary orthogonal ranges define a
positive definite operator. Used for the two-sector comparison in
`07-comparators.tex`, lines 603–621. -/
theorem posDef_smul_one_sub_add_smul_projection {P : Matrix n n ℂ}
    (hP : IsStarProjection P) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    (b • (1 - P) + d • P).PosDef := by
  have hnonneg : 0 ≤ b • (1 - P) + d • P :=
    add_nonneg (smul_nonneg hb.le hP.one_sub.nonneg) (smul_nonneg hd.le hP.nonneg)
  refine (nonneg_iff_posSemidef.mp hnonneg).posDef_iff_isUnit.mpr ?_
  refine isUnit_iff_exists_inv.mpr ⟨b⁻¹ • (1 - P) + d⁻¹ • P, ?_⟩
  rw [projection_sectors_mul hP, mul_inv_cancel₀ hb.ne', mul_inv_cancel₀ hd.ne',
    one_smul, one_smul, sub_add_cancel]

namespace MeanTree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A mean tree acts independently on the two complementary ranges of an
orthogonal projection. The common scalar on the complement is unchanged.
Source: `07-comparators.tex`, lines 603–621, `comparator:tree-log-lower`. -/
theorem eval_smul_one_sub_add_smul_projection {P : Matrix n n ℂ}
    (hP : IsStarProjection P) {b : ℝ} (hb : 0 < b)
    {d : ι → ℝ} (hd : ∀ j, 0 < d j) (T : MeanTree ι) :
    T.eval (fun j ↦ b • (1 - P) + d j • P) =
      b • (1 - P) + (∏ j, (d j) ^ T.weight j) • P := by
  let A (j : ι) : Matrix n n ℂ := b • (1 - P) + d j • P
  have hA (j : ι) : (A j).PosDef :=
    posDef_smul_one_sub_add_smul_projection hP hb (hd j)
  have hsector (j : ι) : A j * P = P * (d j • (1 : Matrix n n ℂ)) := by
    simp only [A, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      hP.one_sub_mul_self, hP.isIdempotentElem.eq, smul_zero, zero_add]
  have hcomplement (j : ι) :
      A j * (1 - P) = (1 - P) * (b • (1 : Matrix n n ℂ)) := by
    simp only [A, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      hP.mul_one_sub_self, hP.one_sub.isIdempotentElem.eq, smul_zero, add_zero]
  have hsectorRoot := eval_intertwine hA
    (fun j ↦ (PosDef.one : (1 : Matrix n n ℂ).PosDef).smul (hd j)) P hsector T
  rw [eval_smul (fun _ ↦ (PosDef.one : (1 : Matrix n n ℂ).PosDef)) hd,
    eval_const PosDef.one, Matrix.mul_smul, Matrix.mul_one] at hsectorRoot
  have hcomplementRoot := eval_intertwine hA
    (fun _ ↦ (PosDef.one : (1 : Matrix n n ℂ).PosDef).smul hb)
    (1 - P) hcomplement T
  rw [eval_const ((PosDef.one : (1 : Matrix n n ℂ).PosDef).smul hb),
    Matrix.mul_smul, Matrix.mul_one] at hcomplementRoot
  change T.eval A = _
  calc
    T.eval A = T.eval A * ((1 - P) + P) := by rw [sub_add_cancel, Matrix.mul_one]
    _ = b • (1 - P) + (∏ j, (d j) ^ T.weight j) • P := by
      rw [Matrix.mul_add, hcomplementRoot, hsectorRoot]

/-- Two-sector lower bounds pass through a mean tree. The original operators
are not required to commute with the projection or with one another.
Source: `07-comparators.tex`, lines 603–621, `comparator:tree-log-lower`. -/
theorem smul_one_sub_add_smul_projection_le_eval {P : Matrix n n ℂ}
    (hP : IsStarProjection P) {b : ℝ} (hb : 0 < b)
    {d : ι → ℝ} (hd : ∀ j, 0 < d j) {A : ι → Matrix n n ℂ}
    (hbound : ∀ j, b • (1 - P) + d j • P ≤ A j) (T : MeanTree ι) :
    b • (1 - P) + (∏ j, (d j) ^ T.weight j) • P ≤ T.eval A := by
  rw [← eval_smul_one_sub_add_smul_projection hP hb hd T]
  exact eval_mono (fun j ↦ posDef_smul_one_sub_add_smul_projection hP hb (hd j)) hbound T

end MeanTree

end Matrix

end

end MeanTreeProjectionSectors

section MeanTreeProjectionLogBound

/-!
## Logarithmic lower bounds from two projection ranges

A positive two-sector comparison can be passed through a weighted mean tree
and then through the operator logarithm. The complementary scalar remains
fixed, while the scalar on the distinguished range becomes the terminally
weighted average of its logarithms.

No commutation of the original leaf operators with the distinguished
projection is required. Strict positivity follows from the positive
comparison operators. All terminal weights, including zero weights, are
retained.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 603–640,
  `comparator:tree-log-lower`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.MeanTree

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The logarithm of a mean tree dominates the logarithm of its two-sector
comparison. The original leaves need not commute with the projection or
with one another. Source: `07-comparators.tex`, lines 603–640,
`comparator:tree-log-lower`. -/
theorem log_projection_sectors_le_log_eval {P : Matrix n n ℂ}
    (hP : IsStarProjection P) {b : ℝ} (hb : 0 < b)
    {d : ι → ℝ} (hd : ∀ j, 0 < d j) {A : ι → Matrix n n ℂ}
    (hbound : ∀ j, b • (1 - P) + d j • P ≤ A j) (T : MeanTree ι) :
    Real.log b • (1 - P) + (∑ j, T.weight j * Real.log (d j)) • P ≤
      CFC.log (T.eval A) := by
  let r : ℝ := ∏ j, (d j) ^ T.weight j
  have hr : 0 < r := Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hd j) _
  have hlogr : Real.log r = ∑ j, T.weight j * Real.log (d j) := by
    dsimp only [r]
    rw [Real.log_prod (fun j _ ↦ (Real.rpow_pos_of_pos (hd j) _).ne')]
    exact Finset.sum_congr rfl fun j _ ↦ Real.log_rpow (hd j) _
  have hpositive : (b • (1 - P) + r • P).PosDef :=
    Matrix.posDef_smul_one_sub_add_smul_projection hP hb hr
  have horder : b • (1 - P) + r • P ≤ T.eval A :=
    smul_one_sub_add_smul_projection_le_eval hP hb hd hbound T
  have hlog := CFC.log_le_log horder hpositive.isStrictlyPositive
  have haffine : b • (1 - P) + r • P =
      b • (1 : Matrix n n ℂ) + (r - b) • P := by
    rw [smul_sub, sub_smul]
    abel
  rw [CFC.log, haffine,
    Matrix.cfc_affine_of_isSelfAdjoint_isIdempotentElem P hP.isSelfAdjoint
      hP.isIdempotentElem b r Real.log, hlogr] at hlog
  exact hlog

end Matrix.MeanTree

section MeanTreeProjectionMassBound

/-!
# A logarithmic lower bound from retained projection mass

Suppose that the leaves dominate positive matrices which are scalar on
two complementary projection ranges. If a unit vector has mass at least
`1 - δ` on the distinguished range, its logarithmic expectation at the
root is bounded below by the weighted logarithmic value on that range,
less `δ` times the difference of the two logarithmic values.

The distinguished scalar is assumed to be at least the complementary
scalar. In the lower area-law comparison this follows from averaging
the positive whole-space bound with the positive projection bound.
No upper bound on `δ` is required.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 603–640,
  `comparator:tree-log-lower`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.MeanTree

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Retained projection mass gives the lower logarithmic expectation of a
weighted mean tree. The error is linear in the mass deficit, uniformly
over the terminal probabilities, including zero probabilities.
Source: `07-comparators.tex`, lines 603–640,
`comparator:tree-log-lower`. -/
theorem re_dotProduct_log_eval_ge_of_projection_mass {P : Matrix n n ℂ}
    (hP : IsStarProjection P) {b : ℝ} (hb : 0 < b)
    {d : ι → ℝ} (hbd : ∀ j, b ≤ d j) {A : ι → Matrix n n ℂ}
    (hbound : ∀ j, b • (1 - P) + d j • P ≤ A j) (T : MeanTree ι)
    (v : EuclideanSpace ℂ n) (hv : ‖v‖ = 1) {δ : ℝ}
    (hmass : 1 - δ ≤ (star v ⬝ᵥ (P *ᵥ v)).re) :
    let ell := ∑ j, T.weight j * Real.log (d j)
    ell - δ * (ell - Real.log b) ≤
      (star v ⬝ᵥ (CFC.log (T.eval A) *ᵥ v)).re := by
  intro ell
  have hell : Real.log b ≤ ell := by
    calc
      Real.log b = ∑ j, T.weight j * Real.log b := by
        rw [← Finset.sum_mul, T.sum_weight, one_mul]
      _ ≤ ell := Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (Real.log_le_log hb (hbd j)) (T.weight_nonneg j)
  have horder := log_projection_sectors_le_log_eval hP hb
    (fun j ↦ hb.trans_le (hbd j)) hbound T
  have hreal := (Complex.nonneg_iff.mp
    ((Matrix.le_iff.mp horder).dotProduct_mulVec_nonneg v)).1
  simp only [sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub, dotProduct_add,
    dotProduct_smul, one_mulVec, Complex.sub_re, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hreal
  have hn : (star v ⬝ᵥ v).re = 1 := by
    have hnorm : (star v ⬝ᵥ v).re = ‖v‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct_comm]
      rfl
    simpa only [hv, one_pow] using hnorm
  rw [hn] at hreal
  have hmass' := mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hell)
  change 0 ≤ (star v ⬝ᵥ (CFC.log (T.eval A) *ᵥ v)).re -
    (Real.log b * (1 - (star v ⬝ᵥ (P *ᵥ v)).re) +
      ell * (star v ⬝ᵥ (P *ᵥ v)).re) at hreal
  nlinarith only [hreal, hmass']

end Matrix.MeanTree
end

end MeanTreeProjectionMassBound

end

end MeanTreeProjectionLogBound

end MeanTreeProjectionSectors

section MeanTreeExponentialLowerNorm

/-!
## The explicit lower norm rate from exponential projection bounds

The projection lower bounds on each band imply a norm comparison whose remainder
is independent of the terminal probabilities and of the discarded mass.
The proof first truncates each mass deficit at one, obtains the uniform
remainder, and then weakens the leading term to the original deficit.

The projection lower bounds and the mass estimates are hypotheses
of this analytic implication. Their derivation from the physical state is
a separate part of the area-law comparison.

It also contains the following results.

* `Matrix.MeanTree.mul_sum_log_lower_le_neg_log_norm_sq_of_projection_lower_bound`: a lower norm
  comparison for several bands.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 585–651,
  `comparator:inverse-compression` through `comparator:tree-log-lower`,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

section MeanTreeMultibandLowerNorm

/-!
## A lower norm comparison for several bands

Projection lower bounds and a positive floor give a logarithmic lower
bound for each mean tree. For pairwise commuting roots these logarithmic
bounds add. Exponential Jensen in the normalized inverse-power image then
bounds the negative logarithm of its squared norm.

The projection may differ between bands and need not commute with the
leaves or roots. The retained mass is measured in the actual normalized
inverse-power image. The projection lower bounds remain hypotheses of this analytic statement;
their derivation from the actual replica metrics is separate.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 585–651,
  `comparator:inverse-compression` through `comparator:tree-log-lower`,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.MeanTree

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Projection lower bounds, positive floors and retained projection mass
give the lower norm comparison for an ordered product of commuting mean
roots. Empty products and zero terminal weights are included.
Source: `07-comparators.tex`, lines 585–651. -/
theorem mul_sum_log_lower_le_neg_log_norm_sq_of_projection_lower_bound
    {G : ℕ} (T : Fin G → MeanTree ι) {A : ι → Fin G → Matrix n n ℂ}
    (hA : ∀ j g, (A j g).PosDef)
    (hcomm : ∀ g h, g ≠ h → Commute ((T g).eval (A · g)) ((T h).eval (A · h)))
    {P : Fin G → Matrix n n ℂ} (hP : ∀ g, IsStarProjection (P g))
    {b : Fin G → ℝ} (hb : ∀ g, 0 < b g)
    {c : ι → Fin G → ℝ} (hc : ∀ j g, 0 < c j g)
    (hfloor : ∀ j g, (2 * b g) • (1 : Matrix n n ℂ) ≤ A j g)
    (hpin : ∀ j g, c j g • P g ≤ A j g)
    {s : ℝ} (hs : 0 ≤ s) (p : EuclideanSpace ℂ n)
    (hp : p ≠ 0) (hnorm : ‖p‖ ≤ 1) (δ : Fin G → ℝ) :
    let M := (List.ofFn fun g ↦ (T g).eval (A · g)).prod
    let u := toEuclideanLin (M ^ (-s)) p
    let v := (‖u‖⁻¹ : ℂ) • u
    let ell : Fin G → ℝ := fun g ↦ ∑ j, (T g).weight j * Real.log (b g + c j g / 2)
    (∀ g, 1 - δ g ≤ (star v ⬝ᵥ (P g *ᵥ v)).re) →
      2 * s * Finset.sum Finset.univ
        (fun g : Fin G ↦ ell g - δ g * (ell g - Real.log (b g))) ≤
        -Real.log (‖u‖ ^ 2) := by
  intro M u v ell hmass
  have hroots : ∀ g, ((T g).eval (A · g)).PosDef := fun g ↦
    (T g).posDef_eval (fun j ↦ hA j g)
  have hM : M.PosDef := posDef_listProd_ofFn hroots hcomm
  have hcancel : toEuclideanLin (M ^ s) u = p := by
    change ((toLpLin 2 2 (M ^ s) ∘ₗ toLpLin 2 2 (M ^ (-s))) p) = p
    rw [← toLpLin_mul_same, hM.rpow_mul_rpow_neg, toLpLin_one, LinearMap.id_apply]
  have hu : u ≠ 0 := by
    intro h
    apply hp
    simpa only [h, map_zero] using hcancel.symm
  have hv : ‖v‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) hu
  have hlog : ∀ g, ell g - δ g * (ell g - Real.log (b g)) ≤
      (star v ⬝ᵥ (CFC.log ((T g).eval (A · g)) *ᵥ v)).re := by
    intro g
    apply re_dotProduct_log_eval_ge_of_projection_mass (hP g) (hb g)
      (fun j ↦ le_add_of_nonneg_right (half_pos (hc j g)).le)
      _ (T g) v hv (hmass g)
    intro j
    exact Matrix.floor_pin_le (hfloor j g) (hpin j g)
  have hsum : (∑ g, (ell g - δ g * (ell g - Real.log (b g)))) ≤
      (star v ⬝ᵥ (CFC.log M *ᵥ v)).re := by
    change _ ≤ (star v ⬝ᵥ
      (CFC.log (List.ofFn fun g ↦ (T g).eval (A · g)).prod *ᵥ v)).re
    rw [Matrix.cfc_log_listProd_ofFn hroots hcomm, sum_mulVec,
      dotProduct_sum, Complex.re_sum]
    exact Finset.sum_le_sum fun g _ ↦ hlog g
  have hJ := hM.mul_re_inner_cfc_log_normalized_inverse_le_neg_log_norm_sq
    s p hp hnorm
  have hJ' : 2 * s * (star v ⬝ᵥ (CFC.log M *ᵥ v)).re ≤
      -Real.log (‖u‖ ^ 2) := by
    simpa only [u, v, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
      WithLp.ofLp_toLp, dotProduct_comm] using hJ
  exact (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hs)).trans hJ'

end Matrix.MeanTree

end

end MeanTreeMultibandLowerNorm

section MeanTreeExponentialLowerNorm

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.MeanTree

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Exponential projection lower bounds yield an explicit lower norm
rate. The error is uniform in all terminal probabilities and all nonnegative
mass deficits; no upper bound on those deficits is assumed.
Source: `07-comparators.tex`, lines 585–651. -/
theorem explicit_lower_norm_of_exponential_projection_lower_bound
    {G : ℕ} (T : Fin G → MeanTree ι) {A : ι → Fin G → Matrix n n ℂ}
    (hA : ∀ j g, (A j g).PosDef)
    (hcomm : ∀ g h, g ≠ h → Commute ((T g).eval (A · g)) ((T h).eval (A · h)))
    {P : Fin G → Matrix n n ℂ} (hP : ∀ g, IsStarProjection (P g))
    {b : Fin G → ℝ} (hb : ∀ g, 0 < b g)
    {κ : Fin G → ℝ} (hκ : ∀ g, 0 ≤ κ g)
    (L : ι → Fin G → ℝ) (U r : Fin G → ℝ) (hU : ∀ j g, L j g ≤ U g)
    (hfloor : ∀ j g, (2 * b g) • (1 : Matrix n n ℂ) ≤ A j g)
    (hpin : ∀ j g, Real.exp (κ g * L j g - r g) • P g ≤ A j g)
    {s : ℝ} (hs : 0 ≤ s) (p : EuclideanSpace ℂ n)
    (hp : p ≠ 0) (hnorm : ‖p‖ ≤ 1)
    {δ : Fin G → ℝ} (hδ : ∀ g, 0 ≤ δ g) :
    let M := (List.ofFn fun g ↦ (T g).eval (A · g)).prod
    let u := toEuclideanLin (M ^ (-s)) p
    let v := (‖u‖⁻¹ : ℂ) • u
    (∀ g, 1 - δ g ≤ (star v ⬝ᵥ (P g *ᵥ v)).re) →
      2 * s * (∑ g,
        (κ g * ((∑ j, (T g).weight j * L j g) - δ g * max 0 (U g)) -
          (2 * |r g| + |Real.log (b g)| + Real.log 2 + Real.log (3 / 2)))) ≤
        -Real.log (‖u‖ ^ 2) := by
  intro M u v hmass
  let ε := fun g ↦ min 1 (δ g)
  have hε : ∀ g, 0 ≤ ε g := fun g ↦ le_min zero_le_one (hδ g)
  have hεone : ∀ g, ε g ≤ 1 := fun g ↦ min_le_left _ _
  have hεδ : ∀ g, ε g ≤ δ g := fun g ↦ min_le_right _ _
  have hretained : ∀ g, 1 - ε g ≤ (star v ⬝ᵥ (P g *ᵥ v)).re := by
    intro g
    by_cases h : δ g ≤ 1
    · simpa only [ε, min_eq_right h] using hmass g
    · have hq : 0 ≤ (star v ⬝ᵥ (P g *ᵥ v)).re :=
        (Complex.nonneg_iff.mp
          ((Matrix.nonneg_iff_posSemidef.mp (hP g).nonneg).dotProduct_mulVec_nonneg v)).1
      simpa only [ε, min_eq_left (le_of_not_ge h), sub_self] using hq
  have hnormLower := mul_sum_log_lower_le_neg_log_norm_sq_of_projection_lower_bound
    T hA hcomm hP hb (fun j g ↦ Real.exp_pos (κ g * L j g - r g))
    hfloor hpin hs p hp hnorm ε hretained
  apply le_trans _ hnormLower
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hs)
  apply Finset.sum_le_sum
  intro g _
  have hlocal := (T g).weighted_log_floor_deficit_lower (hb g) (hκ g)
    (L · g) (fun j ↦ hU j g) (r g) (hε g) (hεone g)
  have hleading :
      κ g * ((∑ j, (T g).weight j * L j g) - δ g * max 0 (U g)) ≤
      κ g * ((∑ j, (T g).weight j * L j g) - ε g * max 0 (U g)) :=
    mul_le_mul_of_nonneg_left
      (sub_le_sub_left
        (mul_le_mul_of_nonneg_right (hεδ g) (le_max_left 0 (U g))) _)
      (hκ g)
  exact (sub_le_sub_right hleading _).trans hlocal

end Matrix.MeanTree

end

end MeanTreeExponentialLowerNorm

end MeanTreeExponentialLowerNorm
