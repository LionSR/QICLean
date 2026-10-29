/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.AGSPGeometricTails

/-!
# Schmidt tails from a specified product overlap

Powers of an actual invariant-line approximate projector give tails of its
original fixed vector. The product overlap and shrinking parameter are retained;
no favorable shrinking-to-rank tradeoff is required.

**Local fix (general entropy estimate):** These tails support a correction of
AKLV, arXiv:1301.1162v1, Lemma 2.3 (`lem:S`), lines 339–348, whose printed
uniform bound misses an additive logarithmic rank contribution. The original
counterexample is retained in `docs/paper-gaps/aklv13_entropy_small_shrinking.tex`.
The hypotheses concern one invariant line, as in the source's unique-ground
applications in Sections 4 and 6.1, not an arbitrary degenerate ground space.
-/

open scoped BigOperators InnerProductSpace Matrix ComplexOrder

namespace Matrix

/-- Tails of the original fixed vector from an actual unit product vector.
The rank-one condition means that the specified vector is a product vector;
no approximant or tail is supplied. Supporting AKLV, arXiv:1301.1162v1,
Lemma 2.3 (`lem:S`), lines 339–348, and entropy summation, lines 1059–1075. -/
theorem sum_eigenvalues_tail_of_operatorSchmidtRank_of_product_overlap
    {m n : Type*} [Fintype m] [Fintype n]
    (K : Matrix (m × n) (m × n) ℂ)
    (Γ φ : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1) (hφ : ‖φ‖ = 1)
    (hφrank : schmidtRank (WithLp.ofLp φ) ≤ 1)
    (hfix : Matrix.toEuclideanLin K Γ = Γ)
    {D : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hperp : ∀ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ)
    (hrank : Matrix.operatorSchmidtRank K ≤ D)
    (ha : ⟪Γ, φ⟫_ℂ ≠ 0) (j : ℕ) :
    let C := schmidtCoeffMatrix (WithLp.ofLp Γ)
    let hρ := posSemidef_self_mul_conjTranspose C
    (∑ b ∈ Finset.univ.filter
      (fun b : Fin (Fintype.card m) ↦ D ^ j ≤ b.val), hρ.isHermitian.eigenvalues₀ b) ≤
      min 1 (((1 - ‖⟪Γ, φ⟫_ℂ‖ ^ 2) / ‖⟪Γ, φ⟫_ℂ‖ ^ 2) * δ ^ j) := by
  classical
  let a : ℂ := ⟪Γ, φ⟫_ℂ
  let v := φ - a • Γ
  have hv : ⟪Γ, v⟫_ℂ = 0 := by
    simp [v, a, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hΓ]
  have hdecomp : φ = a • Γ + v := by
    dsimp only [v]
    rw [add_comm (a • Γ), sub_add_cancel]
  have hvnorm : ‖v‖ ^ 2 = 1 - ‖a‖ ^ 2 := by
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (𝕜 := ℂ) (a • Γ) v (by simp only [inner_smul_left, hv, mul_zero])
    rw [← hdecomp, hφ, norm_smul, hΓ, mul_one] at hpyth
    nlinarith
  have hnonneg : 0 ≤ 1 - ‖a‖ ^ 2 := by rw [← hvnorm]; positivity
  let A : Module.End ℂ (EuclideanSpace ℂ (m × n)) := toEuclideanLin K
  let χ := (A ^ j) φ
  let z := (A ^ j) v
  obtain ⟨hzorth, hznorm⟩ := LinearMap.inner_pow_eq_zero_and_norm_sq_le A Γ hδ
    (perpendicular_shrinking_homogeneous A Γ δ hperp) v hv j
  have hfixpow : (A ^ j) Γ = Γ := by
    simpa only [Module.End.pow_apply] using Function.iterate_fixed hfix j
  have hχdecomp : χ = a • Γ + z := by
    dsimp only [χ, z]
    rw [hdecomp, map_add, map_smul, hfixpow]
  have hχrank : schmidtRank (WithLp.ofLp χ) ≤ D ^ j := by
    change schmidtRank (WithLp.ofLp ((toEuclideanLin K ^ j) φ)) ≤ D ^ j
    have hpow := congrArg
      (fun A : Module.End ℂ (EuclideanSpace ℂ (m × n)) ↦ A φ)
      (toLpLin_pow 2 K j)
    rw [← hpow]
    simpa only [toLpLin_apply, WithLp.ofLp_toLp, Nat.mul_one] using
      (schmidtRank_pow_mulVec_le K (WithLp.ofLp φ) hrank j).trans
        (Nat.mul_le_mul_left (D ^ j) hφrank)
  let C := schmidtCoeffMatrix (WithLp.ofLp Γ)
  let hρ := posSemidef_self_mul_conjTranspose C
  have htr : ((C * Cᴴ).trace).re = 1 := by
    simpa only [Complex.one_re] using
      congrArg Complex.re (trace_schmidtCoeffMatrix_mul_conjTranspose_of_norm_one Γ hΓ)
  change (∑ b ∈ Finset.univ.filter
    (fun b : Fin (Fintype.card m) ↦ D ^ j ≤ b.val), hρ.isHermitian.eigenvalues₀ b) ≤ _
  apply le_min
  · rw [hρ.isHermitian.sum_eigenvalues₀_filter_le, htr]
    linarith [hρ.kyFanNorm_nonneg (D ^ j)]
  · by_cases hk : D ^ j < Fintype.card m
    · have htail := one_sub_kyFanNorm_le_of_orthogonal_decomposition
        Γ χ z a hΓ ha hzorth hχdecomp hk hχrank
      rw [hρ.isHermitian.sum_eigenvalues₀_filter_le, htr]
      calc
        _ ≤ ‖z‖ ^ 2 / ‖a‖ ^ 2 := htail
        _ ≤ (δ ^ j * (1 - ‖a‖ ^ 2)) / ‖a‖ ^ 2 :=
          div_le_div_of_nonneg_right (by simpa only [hvnorm] using hznorm) (sq_nonneg _)
        _ = _ := by ring
    · have he : Finset.univ.filter
          (fun b : Fin (Fintype.card m) ↦ D ^ j ≤ b.val) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro b _hb
        exact not_le_of_gt (b.isLt.trans_le (Nat.le_of_not_gt hk))
      rw [he, Finset.sum_empty]
      exact mul_nonneg (div_nonneg hnonneg (sq_nonneg _)) (pow_nonneg hδ j)

/-- Zero shrinking sends the specified product vector onto a nonzero multiple
of the fixed vector, so its Schmidt rank is at most the operator rank.
This is the exact-projection endpoint of the corrected AKLV `lem:S` estimate. -/
theorem schmidtRank_le_of_zero_perpendicular_shrinking
    {m n : Type*} [Fintype m] [Fintype n]
    (K : Matrix (m × n) (m × n) ℂ)
    (Γ φ : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1)
    (hφrank : schmidtRank (WithLp.ofLp φ) ≤ 1)
    (hfix : Matrix.toEuclideanLin K Γ = Γ)
    (hperp : ∀ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ 0)
    {D : ℕ} (hrank : Matrix.operatorSchmidtRank K ≤ D)
    (ha : ⟪Γ, φ⟫_ℂ ≠ 0) : schmidtRank (WithLp.ofLp Γ) ≤ D := by
  let a : ℂ := ⟪Γ, φ⟫_ℂ
  let v := φ - a • Γ
  have hv : ⟪Γ, v⟫_ℂ = 0 := by
    simp [v, a, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hΓ]
  have hz := (perpendicular_shrinking_homogeneous (toEuclideanLin K) Γ 0 hperp v hv).2
  have hvzero : toEuclideanLin K v = 0 := by
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    exact le_antisymm (by simpa only [zero_mul] using hz) (sq_nonneg _)
  have himage : toEuclideanLin K φ = a • Γ := by
    have hd : φ = a • Γ + v := by dsimp only [v]; module
    rw [hd, map_add, map_smul, hfix, hvzero, add_zero]
  have hr := (schmidtRank_mulVec_le K (WithLp.ofLp φ)).trans
    (Nat.mul_le_mul hrank hφrank)
  simp only [Nat.mul_one] at hr
  have hr' : schmidtRank (WithLp.ofLp (a • Γ)) ≤ D := by
    change schmidtRank (WithLp.ofLp (toEuclideanLin K φ)) ≤ D at hr
    simpa only [himage] using hr
  simpa only [WithLp.ofLp_smul, schmidtRank_smul_eq_of_ne_zero a ha] using hr'

end Matrix
