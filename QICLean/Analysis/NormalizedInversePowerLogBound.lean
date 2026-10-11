/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.InversePowerLogJensen

/-!
# The norm rate bounds the logarithm in the deformed vector

Let `M` be positive definite and let `p` be a nonzero vector of norm at
most one. Normalize `M^(-s) p` to obtain `v`. Exponential Jensen and the
identity `M^s M^(-s) p = p` imply

`2s Re ⟨v, log(M) v⟩ ≤ -log ‖M^(-s) p‖²`.

This holds for every real exponent. In the lower area-law comparison
the exponent is positive and the vector `p` is the selected prevector.
No expectation identity is assumed: the normalization and the opposite
power cancellation give it directly.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 642–651, following
  `comparator:tree-log-lower`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}

/-- Exponential Jensen gives the lower norm-rate comparison from a scaled
positive-power norm bound. The exponent may be any real number.
Source: `07-comparators.tex`, lines 642–651. -/
theorem PosDef.mul_re_inner_cfc_log_le_neg_log_of_scaled_power_norm_le
    (hM : M.PosDef) (s : ℝ) (v : EuclideanSpace ℂ n) (hv : ‖v‖ = 1)
    {N : ℝ} (hN : 0 < N)
    (hbound : N * ‖toEuclideanLin (M ^ s) v‖ ^ 2 ≤ 1) :
    2 * s * (inner ℂ v (toEuclideanLin (CFC.log M) v)).re ≤ -Real.log N := by
  have hJ : Real.exp (2 * s * (inner ℂ v (toEuclideanLin (CFC.log M) v)).re) ≤
      ‖toEuclideanLin (M ^ s) v‖ ^ 2 := by
    simpa only [mul_neg, neg_mul, neg_neg] using
      hM.exp_neg_mul_re_inner_cfc_log_le_norm_rpow_neg_sq (-s) v hv
  have hproduct := (mul_le_mul_of_nonneg_left hJ hN.le).trans hbound
  have hlog := Real.log_le_log (mul_pos hN (Real.exp_pos _)) hproduct
  rw [Real.log_mul hN.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_one] at hlog
  linarith only [hlog]

/-- The actual normalization of an inverse-power image satisfies the lower
norm-rate comparison. The original vector is only required to be nonzero
and to have norm at most one.
Source: `07-comparators.tex`, lines 642–651. -/
theorem PosDef.mul_re_inner_cfc_log_normalized_inverse_le_neg_log_norm_sq
    (hM : M.PosDef) (s : ℝ) (p : EuclideanSpace ℂ n)
    (hp : p ≠ 0) (hnorm : ‖p‖ ≤ 1) :
    let u := toEuclideanLin (M ^ (-s)) p
    let v := (‖u‖⁻¹ : ℂ) • u
    2 * s * (inner ℂ v (toEuclideanLin (CFC.log M) v)).re ≤
      -Real.log (‖u‖ ^ 2) := by
  intro u v
  have hcancel : toEuclideanLin (M ^ s) u = p := by
    change ((toLpLin 2 2 (M ^ s) ∘ₗ toLpLin 2 2 (M ^ (-s))) p) = p
    rw [← toLpLin_mul_same, hM.rpow_mul_rpow_neg, toLpLin_one, LinearMap.id_apply]
  have hu : u ≠ 0 := by
    intro h
    apply hp
    simpa only [h, map_zero] using hcancel.symm
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hv : ‖v‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) hu
  have hscale : ‖u‖ ^ 2 * ‖toEuclideanLin (M ^ s) v‖ ^ 2 = ‖p‖ ^ 2 := by
    dsimp only [v]
    rw [map_smul, hcancel, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg u), mul_pow, inv_pow,
      ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hun), one_mul]
  apply hM.mul_re_inner_cfc_log_le_neg_log_of_scaled_power_norm_le s v hv
    (pow_pos (norm_pos_iff.mpr hu) 2)
  rw [hscale]
  nlinarith only [norm_nonneg p, hnorm]

end Matrix
