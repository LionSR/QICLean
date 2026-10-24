/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.MaximalOverlap
import QICLean.Analysis.SpectralTailTraceNorm
import QICLean.Analysis.OptimizedPureStateTraceError
import QICLean.Analysis.OptimizedPureErrorMass

/-!
# Half-error spectral tails for pure-state approximation

A unit target vector approximated in full pure-density trace norm by an arbitrary
vector has missing normalized squared overlap at most half the error, provided
the error is strictly below one. Combining this with the maximal Schmidt overlap
bound controls the target's discarded marginal spectrum by half the same error.
The approximant is normalized only within the proof; no normalization or
nonvanishing hypothesis on it is imposed.

These estimates combine the optimized pure-state error formula in
Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2, lines 160–173, with the
Ky Fan argument underlying the spectral-tail bound at lines 247–264.
-/

open scoped ComplexOrder InnerProductSpace

namespace Matrix

/-- Unit-vector overlap is bounded by the leading Schmidt mass; subtracting from
the trace gives the discarded-tail bound. -/
private theorem tail_le_one_sub_normSq_inner {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m]
    (ψ φ : EuclideanSpace ℂ (m × n)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    {D : ℕ} (hrank : (schmidtCoeffMatrix (WithLp.ofLp φ)).rank ≤ D) :
    ∑ i ∈ Finset.Ico D (Fintype.card m),
      (posSemidef_self_mul_conjTranspose
        (schmidtCoeffMatrix (WithLp.ofLp ψ))).isHermitian.descEigenvalue i
        ≤ 1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
  classical
  let C := schmidtCoeffMatrix (WithLp.ofLp ψ)
  have hb := normSq_inner_le_kyFanNorm ψ φ hφ D hrank
  have htrace : (C * Cᴴ).trace.re = 1 := by
    rw [trace_mul_comm, ← star_dotProduct_self_eq_trace_conjTranspose_mul]
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hψ]
    simp
  by_cases hD : D < Fintype.card m
  · have hs := (posSemidef_self_mul_conjTranspose C).isHermitian.kyFanNorm_card_eq_trace_re
    rw [htrace] at hs
    rw [Finset.sum_Ico_eq_sub _ hD.le]
    change (posSemidef_self_mul_conjTranspose C).isHermitian.kyFanNorm (Fintype.card m) -
      (posSemidef_self_mul_conjTranspose C).isHermitian.kyFanNorm D ≤ _
    rw [hs]
    linarith
  · have hi := norm_inner_le_norm (𝕜 := ℂ) ψ φ
    rw [hψ, hφ, one_mul] at hi
    simp only [Finset.Ico_eq_empty_of_le (Nat.le_of_not_gt hD), Finset.sum_empty]
    nlinarith [norm_nonneg (inner (𝕜 := ℂ) ψ φ)]

/-- Full trace error strictly below one controls the missing normalized squared
overlap, even for an unnormalized approximant. This follows from the optimized
pure-state formula of SWVC08, arXiv:0705.0292v2, lines 160–173. -/
theorem one_sub_normalized_overlap_le_half_pure_trace_error {n : Type*} [Fintype n] [DecidableEq n]
    (ψ φ : EuclideanSpace ℂ n) (hψ : ‖ψ‖ = 1) {δ : ℝ} (hδ : δ < 1)
    (herror : rectangularTraceNorm (euclideanOuterProduct ψ ψ - euclideanOuterProduct φ φ) ≤ δ) :
    1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2 / ‖φ‖ ^ 2 ≤ δ / 2 := by
  have hden : rectangularTraceNorm (euclideanOuterProduct ψ ψ) = 1 := by
    simp only [rectangularTraceNorm_euclideanOuterProduct_self, hψ, one_pow]
  have hψ0 : ψ ≠ 0 := by intro h; simp [h] at hψ
  have hφ0 : φ ≠ 0 := by
    intro h
    have he : rectangularTraceNorm (euclideanOuterProduct ψ ψ) ≤ δ := by
      simpa [h, euclideanOuterProduct] using herror
    rw [hden] at he
    linarith
  have hopt := (isLeast_optimizedPureTraceError ψ φ hψ0 hφ0).2
    (show rectangularTraceNorm (euclideanOuterProduct ψ ψ - euclideanOuterProduct φ φ) /
      rectangularTraceNorm (euclideanOuterProduct ψ ψ) ∈ _ from ⟨1, by simp⟩)
  simp only [hψ, one_pow, one_mul, hden, div_one] at hopt
  have hf : ‖⟪ψ, φ⟫_ℂ‖ ^ 2 / ‖φ‖ ^ 2 ≤ 1 := by
    apply (div_le_one (pow_pos (norm_pos_iff.mpr hφ0) 2)).mpr
    have hi := norm_inner_le_norm (𝕜 := ℂ) ψ φ
    rw [hψ, one_mul] at hi
    nlinarith [norm_nonneg φ, norm_nonneg (inner (𝕜 := ℂ) ψ φ)]
  exact Real.one_sub_le_half_error_of_optimizedPureTraceError_le hf hδ (hopt.trans herror)

/-- A rank bound on the approximating pure vector's marginal gives a discarded
spectral tail bounded by half the global full trace error. This combines the
optimized pure-state formula and Ky Fan bound in SWVC08, arXiv:0705.0292v2,
lines 160–173 and 247–264. Only the target vector is normalized. -/
theorem sum_descEigenvalue_tail_le_half_pure_trace_error {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ψ φ : EuclideanSpace ℂ (m × n)) (hψ : ‖ψ‖ = 1)
    {D : ℕ} (hrank : (partialTraceRight (euclideanOuterProduct φ φ)).rank ≤ D)
    {δ : ℝ} (hδ : δ < 1)
    (herror : rectangularTraceNorm
      (euclideanOuterProduct ψ ψ - euclideanOuterProduct φ φ) ≤ δ) :
    ∑ i ∈ Finset.Ico D (Fintype.card m),
      (posSemidef_vecMulVec_self_star
        (WithLp.ofLp ψ)).partialTraceRight.isHermitian.descEigenvalue i ≤ δ / 2 := by
  have hmass := one_sub_normalized_overlap_le_half_pure_trace_error ψ φ hψ hδ herror
  have hφ : φ ≠ 0 := by
    intro h
    simp only [h, inner_zero_right, norm_zero, zero_pow (by decide : 2 ≠ 0),
      div_zero, sub_zero] at hmass
    linarith
  let u := (‖φ‖⁻¹ : ℂ) • φ
  have hu : ‖u‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) hφ
  have hc : schmidtCoeffMatrix (WithLp.ofLp u) =
      (‖φ‖⁻¹ : ℂ) • schmidtCoeffMatrix (WithLp.ofLp φ) := by
    ext i j
    rfl
  have hr : (schmidtCoeffMatrix (WithLp.ofLp u)).rank ≤ D := by
    rw [hc, rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr hφ)))]
    simpa only [euclideanOuterProduct, partialTraceRight_vecMulVec_eq,
      rank_self_mul_conjTranspose] using hrank
  have hi : ‖⟪ψ, u⟫_ℂ‖ ^ 2 = ‖⟪ψ, φ⟫_ℂ‖ ^ 2 / ‖φ‖ ^ 2 := by
    simp only [u, inner_smul_right, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg φ), mul_pow, inv_pow, div_eq_mul_inv]
    ring
  have ht := tail_le_one_sub_normSq_inner ψ u hψ hu hr
  rw [hi] at ht
  have heq := (ht.trans hmass)
  simpa only [partialTraceRight_vecMulVec_eq] using heq

end Matrix
