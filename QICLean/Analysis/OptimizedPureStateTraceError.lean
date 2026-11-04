/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.WeightedPureStateTraceNorm
import QICLean.Analysis.SubnormalizedPureStateError
import QICLean.Analysis.OptimizedPureTraceError

/-!
# Optimized trace-norm approximation of pure states

For two nonzero vectors, minimize the full trace-norm error between their
rank-one densities over all complex coefficients. The minimum depends only
on their normalized squared overlap f. It is `2√(f(1-f))` when `f ≥ 1/2`,
and one otherwise. Both original vector norms are arbitrary.

The weighted projection formula gives the minimum over nonnegative real
coefficients. Taking the Hermitian part cannot increase the trace norm;
trace duality handles coefficients with negative real part.

Source: Schuch, Wolf, Verstraete and Cirac, *Entropy Scaling and Simulability
by Matrix Product States*, arXiv:0705.0292v2, lines 139 and 160–173.
The printed trigonometric formula concerns angles between zero and π/4;
the minimum over all coefficients also includes the saturated branch.
-/

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace

namespace Matrix

variable {n : Type*} [Fintype n]

private theorem sqrt_weighted_error_minimum {f : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    IsLeast {r : ℝ | ∃ t : ℝ, 0 ≤ t ∧
      Real.sqrt ((1 - t) ^ 2 + 4 * (t * (1 - f))) = r}
      (if 1 / 2 ≤ f then 2 * Real.sqrt (f * (1 - f)) else 1) := by
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by positivity)]
  split_ifs with hf
  · refine ⟨⟨2 * f - 1, by linarith, ?_⟩, ?_⟩
    · rw [show (1 - (2 * f - 1)) ^ 2 + 4 * ((2 * f - 1) * (1 - f)) =
        4 * (f * (1 - f)) by ring, Real.sqrt_mul (by positivity : 0 ≤ (4 : ℝ))]
      rw [hsqrt4]
    · rintro r ⟨t, ht, rfl⟩
      have hmon := Real.sqrt_le_sqrt
        (show (f * (1 - f)) * 4 ≤ (1 - t) ^ 2 + 4 * (t * (1 - f)) by
          nlinarith only [sq_nonneg (t - (2 * f - 1))])
      simpa only [Real.sqrt_mul (mul_nonneg hf0 (sub_nonneg.mpr hf1)), hsqrt4,
        mul_comm (Real.sqrt (f * (1 - f))) 2] using hmon
  · refine ⟨⟨0, le_rfl, by norm_num⟩, ?_⟩
    rintro r ⟨t, ht, rfl⟩
    apply Real.one_le_sqrt.mpr
    nlinarith only [sq_nonneg t, mul_nonneg ht (show 0 ≤ 1 - 2 * f by linarith)]

omit [Fintype n] in
/-- Multiplying a vector by `c` scales its rank-one matrix by `‖c‖²`.
In particular, a scalar of norm one leaves that matrix unchanged.
Auxiliary to the pure-state normalizations in Schuch--Wolf--Verstraete--Cirac,
arXiv:0705.0292v2, lines 139 and 160--173. -/
theorem vecMulVec_ofLp_smul_self (ψ : EuclideanSpace ℂ n) (c : ℂ) :
    vecMulVec (WithLp.ofLp (c • ψ)) (star (WithLp.ofLp (c • ψ))) =
      (‖c‖ ^ 2 : ℝ) • vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) := by
  have hcoeff : star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm (star c) c, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [WithLp.ofLp_smul, star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul,
    hcoeff, Complex.coe_smul]

open Classical in
private theorem re_trace_abs_smul (X : Matrix n n ℂ) (r : ℝ) (hr : 0 ≤ r) :
    (CFC.abs (r • X)).trace.re = r * (CFC.abs X).trace.re := by
  simp only [CFC.abs_smul, trace_smul, Complex.smul_re, Real.norm_eq_abs,
    abs_of_nonneg hr, smul_eq_mul]

private theorem pure_density_normalize_rescale (ψ : EuclideanSpace ℂ n) (hψ : ψ ≠ 0) :
    (‖ψ‖ ^ 2 : ℝ) • vecMulVec (WithLp.ofLp ((‖ψ‖⁻¹ : ℂ) • ψ))
      (star (WithLp.ofLp ((‖ψ‖⁻¹ : ℂ) • ψ))) =
        vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) := by
  rw [vecMulVec_ofLp_smul_self, smul_smul]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg ψ),
    inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hψ)), one_smul]

private theorem normSq_inner_normalized (ψ φ : EuclideanSpace ℂ n) :
    ‖⟪(‖ψ‖⁻¹ : ℂ) • ψ, (‖φ‖⁻¹ : ℂ) • φ⟫_ℂ‖ ^ 2 =
      ‖⟪ψ, φ⟫_ℂ‖ ^ 2 / (‖ψ‖ ^ 2 * ‖φ‖ ^ 2) := by
  simp only [inner_smul_left, inner_smul_right, norm_mul]
  simp only [RCLike.norm_conj, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg ψ), abs_of_nonneg (norm_nonneg φ),
    mul_pow, inv_pow, div_eq_mul_inv, mul_inv]
  ring

open Classical in
private theorem re_trace_abs_pure_density_self (ψ : EuclideanSpace ℂ n) :
    (CFC.abs (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)))).trace.re = ‖ψ‖ ^ 2 := by
  rw [CFC.abs_of_nonneg _ (posSemidef_vecMulVec_self_star (WithLp.ofLp ψ)).nonneg,
    trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
  exact RCLike.re_ofReal_pow (K := ℂ) ‖ψ‖ 2

open Classical in
private theorem re_trace_abs_pure_density_sub_smul_normalized
    (ψ φ : EuclideanSpace ℂ n) (hψ : ψ ≠ 0) (hφ : φ ≠ 0) (s : ℝ) (hs : 0 ≤ s) :
    (CFC.abs (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) -
      s • vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).trace.re / ‖ψ‖ ^ 2 =
        Real.sqrt ((1 - s * ‖φ‖ ^ 2 / ‖ψ‖ ^ 2) ^ 2 +
          4 * ((s * ‖φ‖ ^ 2 / ‖ψ‖ ^ 2) *
            (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2 / (‖ψ‖ ^ 2 * ‖φ‖ ^ 2)))) := by
  let ψ₀ : EuclideanSpace ℂ n := (‖ψ‖⁻¹ : ℂ) • ψ
  let φ₀ : EuclideanSpace ℂ n := (‖φ‖⁻¹ : ℂ) • φ
  have hψ₀ : ‖ψ₀‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) hψ
  have hφ₀ : ‖φ₀‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) hφ
  let a : ℝ := ‖ψ‖ ^ 2
  let b : ℝ := ‖φ‖ ^ 2
  let P := vecMulVec (WithLp.ofLp ψ₀) (star (WithLp.ofLp ψ₀))
  let Q := vecMulVec (WithLp.ofLp φ₀) (star (WithLp.ofLp φ₀))
  have ha : 0 < a := pow_pos (norm_pos_iff.mpr hψ) 2
  have hψP : a • P = vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) :=
    pure_density_normalize_rescale ψ hψ
  have hφQ : b • Q = vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)) :=
    pure_density_normalize_rescale φ hφ
  have hcoef : a * (s * b / a) = s * b := by
    rw [← mul_div_assoc, mul_comm a (s * b), mul_div_cancel_right₀ _ ha.ne']
  have hdiff : vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) -
      s • vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)) =
        a • (P - (s * b / a) • Q) := by
    rw [← hψP, ← hφQ, smul_sub, smul_smul, smul_smul, hcoef]
  have heq := re_trace_abs_vecMulVec_sub_smul_eq ψ₀ φ₀ hψ₀ hφ₀ (s * b / a)
    (div_nonneg (mul_nonneg hs (sq_nonneg ‖φ‖)) ha.le)
  trans (CFC.abs (P - (s * b / a) • Q)).trace.re
  · rw [hdiff, re_trace_abs_smul _ a ha.le, show ‖ψ‖ ^ 2 = a from rfl,
      mul_div_cancel_left₀ _ ha.ne']
  · simpa only [ψ₀, φ₀, normSq_inner_normalized] using heq

private theorem normalized_fidelity_bounds (ψ φ : EuclideanSpace ℂ n)
    (hψ : ψ ≠ 0) (hφ : φ ≠ 0) :
    0 ≤ ‖⟪ψ, φ⟫_ℂ‖ ^ 2 / (‖ψ‖ ^ 2 * ‖φ‖ ^ 2) ∧
      ‖⟪ψ, φ⟫_ℂ‖ ^ 2 / (‖ψ‖ ^ 2 * ‖φ‖ ^ 2) ≤ 1 := by
  have hpos : 0 < ‖ψ‖ ^ 2 * ‖φ‖ ^ 2 :=
    mul_pos (pow_pos (norm_pos_iff.mpr hψ) 2) (pow_pos (norm_pos_iff.mpr hφ) 2)
  have hCauchy : ‖⟪ψ, φ⟫_ℂ‖ ^ 2 ≤ ‖ψ‖ ^ 2 * ‖φ‖ ^ 2 := by
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) ψ φ) 2
  exact ⟨div_nonneg (sq_nonneg _) hpos.le, (div_le_one hpos).mpr hCauchy⟩

open Classical in
private theorem isLeast_re_trace_abs_pure_density_sub_nonneg
    (ψ φ : EuclideanSpace ℂ n) (hψ : ψ ≠ 0) (hφ : φ ≠ 0) :
    let f := ‖⟪ψ, φ⟫_ℂ‖ ^ 2 / (‖ψ‖ ^ 2 * ‖φ‖ ^ 2)
    IsLeast {r : ℝ | ∃ s : ℝ, 0 ≤ s ∧
      (CFC.abs (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) -
        s • vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).trace.re /
          (CFC.abs (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)))).trace.re = r}
      (if 1 / 2 ≤ f then 2 * Real.sqrt (f * (1 - f)) else 1) := by
  rw [re_trace_abs_pure_density_self ψ]
  let a : ℝ := ‖ψ‖ ^ 2
  let b : ℝ := ‖φ‖ ^ 2
  have ha : 0 < a := pow_pos (norm_pos_iff.mpr hψ) 2
  have hb : 0 < b := pow_pos (norm_pos_iff.mpr hφ) 2
  have hf := normalized_fidelity_bounds ψ φ hψ hφ
  have hmin := sqrt_weighted_error_minimum hf.1 hf.2
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht, heq⟩ := hmin.1
    have hs : 0 ≤ t * a / b := div_nonneg (mul_nonneg ht ha.le) hb.le
    refine ⟨t * a / b, hs, ?_⟩
    have hcoef : (t * a / b) * b / a = t := by
      rw [div_mul_cancel₀ _ hb.ne', mul_div_cancel_right₀ _ ha.ne']
    rw [re_trace_abs_pure_density_sub_smul_normalized ψ φ hψ hφ _ hs, hcoef]
    exact heq
  · rintro r ⟨s, hs, rfl⟩
    rw [re_trace_abs_pure_density_sub_smul_normalized ψ φ hψ hφ s hs]
    exact hmin.2 ⟨s * b / a, div_nonneg (mul_nonneg hs hb.le) ha.le, rfl⟩

/-- The full trace norm of a weighted difference of unit pure-state densities.
This is the weighted calculation underlying Schuch--Wolf--Verstraete--Cirac,
arXiv:0705.0292v2, `paper_v2.tex`, lines 139 and 160–173. -/
theorem rectangularTraceNorm_vecMulVec_sub_smul_eq [DecidableEq n]
    (ψ φ : EuclideanSpace ℂ n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    rectangularTraceNorm (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) -
      t • vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) =
        Real.sqrt ((1 - t) ^ 2 + 4 * (t * (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2))) := by
  rw [rectangularTraceNorm_eq_re_trace_abs]
  exact re_trace_abs_vecMulVec_sub_smul_eq ψ φ hψ hφ t ht

private theorem isLeast_rectangularTraceNorm_pure_density_sub_nonneg [DecidableEq n]
    (ψ φ : EuclideanSpace ℂ n) (hψ : ψ ≠ 0) (hφ : φ ≠ 0) :
    let f := ‖⟪ψ, φ⟫_ℂ‖ ^ 2 / (‖ψ‖ ^ 2 * ‖φ‖ ^ 2)
    IsLeast {r : ℝ | ∃ s : ℝ, 0 ≤ s ∧
      rectangularTraceNorm (euclideanOuterProduct ψ ψ - s • euclideanOuterProduct φ φ) /
        rectangularTraceNorm (euclideanOuterProduct ψ ψ) = r}
      (Real.optimizedPureTraceError f) := by
  simpa only [rectangularTraceNorm_eq_re_trace_abs, euclideanOuterProduct,
    Real.optimizedPureTraceError] using
      isLeast_re_trace_abs_pure_density_sub_nonneg ψ φ hψ hφ

private theorem rectangularTraceNorm_hermitianPart_le [DecidableEq n]
    (A : Matrix n n ℂ) :
    rectangularTraceNorm ((1 / 2 : ℂ) • (A + Aᴴ)) ≤ rectangularTraceNorm A := by
  rw [rectangularTraceNorm_smul]
  have htri := rectangularTraceNorm_add_le A Aᴴ
  rw [rectangularTraceNorm_conjTranspose] at htri
  norm_num
  linarith only [htri]

private theorem rectangularTraceNorm_sub_re_smul_le [DecidableEq n]
    (P Q : Matrix n n ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian) (z : ℂ) :
    rectangularTraceNorm (P - (z.re : ℂ) • Q) ≤ rectangularTraceNorm (P - z • Q) := by
  have hre : (z.re : ℂ) = (z + star z) / 2 := RCLike.re_eq_add_conj z
  have hid : (1 / 2 : ℂ) • ((P - z • Q) + (P - z • Q)ᴴ) =
      P - (z.re : ℂ) • Q := by
    simp only [conjTranspose_sub, conjTranspose_smul, hP.eq, hQ.eq]
    rw [hre]
    module
  simpa only [hid] using rectangularTraceNorm_hermitianPart_le (P - z • Q)

open scoped Matrix.Norms.L2Operator in
private theorem norm_trace_le_rectangularTraceNorm [DecidableEq n] (A : Matrix n n ℂ) :
    ‖A.trace‖ ≤ rectangularTraceNorm A := by
  have h1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := l2_opNorm_unitary_le_one (by simp)
  simpa only [mul_one, trace_conjTranspose, norm_star] using
    norm_trace_conjTranspose_mul_le_rectangularTraceNorm A 1 h1

/-- The full trace norm of a pure density is the squared norm of its vector.
Wolf, Chapter 8, Section 8.1; Schuch--Wolf--Verstraete--Cirac,
arXiv:0705.0292v2, lines 139 and 169. -/
theorem rectangularTraceNorm_euclideanOuterProduct_self [DecidableEq n]
    (ψ : EuclideanSpace ℂ n) :
    rectangularTraceNorm (euclideanOuterProduct ψ ψ) = ‖ψ‖ ^ 2 := by
  simp only [rectangularTraceNorm_eq_re_trace_abs, euclideanOuterProduct,
    re_trace_abs_pure_density_self]

private theorem trace_euclideanOuterProduct_self (ψ : EuclideanSpace ℂ n) :
    (euclideanOuterProduct ψ ψ).trace = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [euclideanOuterProduct, trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K]
  exact (RCLike.ofReal_pow (K := ℂ) ‖ψ‖ 2).symm

/-- Optimizing the full relative trace-norm error over complex density
coefficients gives the scalar error of the normalized squared overlap.
The two original vectors have arbitrary nonzero norms.
Schuch, Wolf, Verstraete and Cirac, arXiv:0705.0292v2, `paper_v2.tex`,
lines 139 and 160–173. -/
theorem isLeast_optimizedPureTraceError [DecidableEq n]
    (ψ φ : EuclideanSpace ℂ n) (hψ : ψ ≠ 0) (hφ : φ ≠ 0) :
    IsLeast {r : ℝ | ∃ z : ℂ,
      rectangularTraceNorm (euclideanOuterProduct ψ ψ - z • euclideanOuterProduct φ φ) /
        rectangularTraceNorm (euclideanOuterProduct ψ ψ) = r}
      (Real.optimizedPureTraceError
        (‖⟪ψ, φ⟫_ℂ‖ ^ 2 / (‖ψ‖ ^ 2 * ‖φ‖ ^ 2))) := by
  have hreal := isLeast_rectangularTraceNorm_pure_density_sub_nonneg ψ φ hψ hφ
  have hden : 0 < rectangularTraceNorm (euclideanOuterProduct ψ ψ) := by
    simpa only [rectangularTraceNorm_euclideanOuterProduct_self] using
      pow_pos (norm_pos_iff.mpr hψ) 2
  refine ⟨?attained, ?lower⟩
  case lower =>
    rintro r ⟨z, rfl⟩
    by_cases hz : z.re < 0
    · have htrace : (euclideanOuterProduct ψ ψ - z • euclideanOuterProduct φ φ).trace =
          ((‖ψ‖ ^ 2 : ℝ) : ℂ) - z * ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
        simp only [trace_sub, trace_smul, trace_euclideanOuterProduct_self, smul_eq_mul]
      have hre : (euclideanOuterProduct ψ ψ - z • euclideanOuterProduct φ φ).trace.re =
          ‖ψ‖ ^ 2 - z.re * ‖φ‖ ^ 2 := by
        simp only [htrace, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
      have hbound := le_trans (Complex.re_le_norm
        (euclideanOuterProduct ψ ψ - z • euclideanOuterProduct φ φ).trace)
          (norm_trace_le_rectangularTraceNorm
            (euclideanOuterProduct ψ ψ - z • euclideanOuterProduct φ φ))
      have hone : 1 ≤ rectangularTraceNorm
          (euclideanOuterProduct ψ ψ - z • euclideanOuterProduct φ φ) /
            rectangularTraceNorm (euclideanOuterProduct ψ ψ) := by
        apply (one_le_div hden).mpr
        rw [rectangularTraceNorm_euclideanOuterProduct_self]
        nlinarith only [hbound, hre, mul_nonpos_of_nonpos_of_nonneg hz.le (sq_nonneg ‖φ‖)]
      have hzero := hreal.2 ⟨0, le_rfl, rfl⟩
      simp only [zero_smul, sub_zero, div_self hden.ne'] at hzero
      exact hzero.trans hone
    · have hmin := hreal.2 ⟨z.re, le_of_not_gt hz, rfl⟩
      have hcontract := rectangularTraceNorm_sub_re_smul_le
        (euclideanOuterProduct ψ ψ) (euclideanOuterProduct φ φ)
        (posSemidef_vecMulVec_self_star (WithLp.ofLp ψ)).isHermitian
        (posSemidef_vecMulVec_self_star (WithLp.ofLp φ)).isHermitian z
      exact hmin.trans (div_le_div_of_nonneg_right (by
        simpa only [Complex.coe_smul] using hcontract) hden.le)
  case attained =>
    obtain ⟨s, hs, heq⟩ := hreal.1
    exact ⟨(s : ℂ), by simpa only [Complex.coe_smul] using heq⟩

end Matrix
