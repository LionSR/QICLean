/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CfcLogListProduct
import QICLean.Analysis.FloorPin
import QICLean.Analysis.MeanTreeProjectionMassBound
import QICLean.Analysis.NormalizedInversePowerLogBound

/-!
# A lower norm comparison for several bands

Projection lower bounds and a positive floor give a logarithmic lower
bound for each mean tree. For pairwise commuting roots these logarithmic
bounds add. Exponential Jensen in the normalized inverse-power image then
bounds the negative logarithm of its squared norm.

The projection may differ between bands and need not commute with the
leaves or roots. The retained mass is measured in the actual normalized
inverse-power image. The projection lower bounds remain hypotheses of this analytic statement;
their derivation from the actual replica metrics is separate.

## References

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
    let ell := fun g ↦ ∑ j, (T g).weight j * Real.log (b g + c j g / 2)
    (∀ g, 1 - δ g ≤ (star v ⬝ᵥ (P g *ᵥ v)).re) →
      2 * s * (∑ g : Fin G, ell g - δ g * (ell g - Real.log (b g))) ≤
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
      (fun j ↦ le_add_of_nonneg_right (half_nonneg (hc j g).le))
      _ (T g) v hv (hmass g)
    intro j
    exact Matrix.floor_pin_le (hfloor j g) (hpin j g)
  have hsum : (∑ g, ell g - δ g * (ell g - Real.log (b g))) ≤
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
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
      WithLp.ofLp_toLp, dotProduct_comm] using hJ
  exact (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hs)).trans hJ'

end Matrix.MeanTree
