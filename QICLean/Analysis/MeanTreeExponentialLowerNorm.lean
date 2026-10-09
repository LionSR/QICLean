/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MeanTreeMultibandLowerNorm
import QICLean.Analysis.MeanTreeLogFloorDeficit

/-!
# The explicit lower norm rate from exponential projection bounds

The projection lower bounds on each band imply a norm comparison whose remainder
is independent of the terminal probabilities and of the discarded mass.
The proof first truncates each mass deficit at one, obtains the uniform
remainder, and then weakens the leading term to the original deficit.

The projection lower bounds and the mass estimates are hypotheses
of this analytic implication. Their derivation from the physical state is
a separate part of the area-law comparison.

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
        κ g * ((∑ j, (T g).weight j * L j g) - δ g * max 0 (U g)) -
          (2 * |r g| + |Real.log (b g)| + Real.log 2 + Real.log (3 / 2))) ≤
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
