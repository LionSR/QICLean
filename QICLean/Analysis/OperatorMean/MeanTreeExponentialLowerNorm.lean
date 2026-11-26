/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.MeanTreeLogFloorExp
import QICLean.Analysis.FunctionalCalculus.MatrixPowers
import QICLean.Analysis.Order.FloorPin
import QICLean.Analysis.OperatorMean.MeanTreeProjectionSectors
import QICLean.Analysis.Logarithm.InversePowerLogJensen

/-!
# The explicit lower norm rate from exponential projection bounds

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

## References

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
