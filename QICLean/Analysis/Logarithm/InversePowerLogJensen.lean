/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FunctionalCalculus.SpectralQuadraticForm
import QICLean.Analysis.FunctionalCalculus.MatrixSqrt
import QICLean.Analysis.FunctionalCalculus.MatrixPowers

/-!
# Inverse-power norms from logarithmic expectations

For a positive definite matrix `M` and a unit vector `φ`, logarithmic
Jensen applied to `M^(-2s)` gives

`exp(-2s Re ⟨φ, log(M) φ⟩) ≤ ‖M^(-s) φ‖²`.

The exponent `s` is arbitrary in this inequality. For `s ≥ 0`, an upper
bound on the logarithmic expectation gives a lower bound on the inverse
norm. Normalizing a nonzero vector `p` and then undoing the normalization
retains the exact prefactor `‖p‖²`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 383--395, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is finite-dimensional Jensen, with no projection or metric transport
identity among its hypotheses.

It also contains the following results.

* `Matrix.PosDef.mul_re_inner_cfc_log_le_neg_log_of_scaled_power_norm_le`,
  `Matrix.PosDef.mul_re_inner_cfc_log_normalized_inverse_le_neg_log_norm_sq`: the norm rate bounds
  the logarithm in the deformed vector.
-/

section InversePowerLogJensen

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}

/-- Exponential Jensen for the inverse power of a positive definite matrix.
The assertion follows from the existing logarithmic Jensen theorem applied
to `M^(-2s)`, and holds for every real exponent.
Source: `07-comparators.tex`, lines 383--395. -/
theorem PosDef.exp_neg_mul_re_inner_cfc_log_le_norm_rpow_neg_sq
    (hM : M.PosDef) (s : ℝ) (φ : EuclideanSpace ℂ n) (hφ : ‖φ‖ = 1) :
    Real.exp (-2 * s * (inner ℂ φ (toEuclideanLin (CFC.log M) φ)).re) ≤
      ‖toEuclideanLin (M ^ (-s)) φ‖ ^ 2 := by
  let v := WithLp.ofLp φ
  have hv : star v ⬝ᵥ v = (1 : ℂ) := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) φ
    rw [hφ, RCLike.ofReal_one, one_pow] at h
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using h
  have hvne : v ≠ 0 := by
    intro h
    simp [h] at hv
  have hN := hM.rpow (-2 * s)
  have hpos : 0 < (star v ⬝ᵥ (M ^ (-2 * s) *ᵥ v)).re := hN.re_dotProduct_pos hvne
  have hJ := hN.posSemidef.re_dotProduct_cfc_log_mulVec_le_log hv
    (by rw [hN.supportProj_eq_one, Matrix.one_mulVec])
  rw [hM.cfc_log_rpow, Matrix.smul_mulVec, dotProduct_smul] at hJ
  simp only [← RCLike.re_to_complex, RCLike.smul_re] at hJ
  have hsym : (toEuclideanLin (M ^ (-s))).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr (hM.rpow_isHermitian (-s))
  have hnorm : ‖toEuclideanLin (M ^ (-s)) φ‖ ^ 2 =
      (inner ℂ φ (toEuclideanLin (M ^ (-2 * s)) φ)).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hsym φ (toEuclideanLin (M ^ (-s)) φ)]
    change (inner ℂ φ ((toLpLin 2 2 (M ^ (-s)) ∘ₗ toLpLin 2 2 (M ^ (-s))) φ)).re = _
    rw [← toLpLin_mul_same, hM.rpow_mul_rpow,
      show -s + -s = -2 * s by ring]
  rw [hnorm]
  have h := Real.exp_le_exp.mpr hJ
  simp only [RCLike.re_to_complex, Real.exp_log hpos] at h
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, dotProduct_comm] using h

/-- An upper bound on the logarithmic expectation in the actual normalized
vector yields an inverse-power norm bound for the original unnormalized
vector. Its squared norm is retained exactly.
Source: `07-comparators.tex`, lines 383--395. -/
theorem PosDef.norm_sq_mul_exp_le_norm_rpow_neg_sq_of_normalized_log_le
    (hM : M.PosDef) (p : EuclideanSpace ℂ n) (hp : 0 < ‖p‖ ^ 2)
    {L : ℝ}
    (hlog : let φ := (‖p‖⁻¹ : ℂ) • p
      (inner ℂ φ (toEuclideanLin (CFC.log M) φ)).re ≤ L)
    {s : ℝ} (hs : 0 ≤ s) :
    ‖p‖ ^ 2 * Real.exp (-2 * s * L) ≤ ‖toEuclideanLin (M ^ (-s)) p‖ ^ 2 := by
  let φ := (‖p‖⁻¹ : ℂ) • p
  have hn : ‖p‖ ≠ 0 := by
    intro h
    simp [h] at hp
  have hφ : ‖φ‖ = 1 :=
    norm_smul_inv_norm (𝕜 := ℂ) (norm_ne_zero_iff.mp hn)
  have hscale : ‖p‖ ^ 2 * ‖toEuclideanLin (M ^ (-s)) φ‖ ^ 2 =
      ‖toEuclideanLin (M ^ (-s)) p‖ ^ 2 := by
    dsimp only [φ]
    rw [map_smul, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg p), mul_pow, inv_pow,
      ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hn), one_mul]
  calc
    _ ≤ ‖p‖ ^ 2 *
        Real.exp (-2 * s * (inner ℂ φ (toEuclideanLin (CFC.log M) φ)).re) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left hlog (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hs)))
          hp.le
    _ ≤ ‖p‖ ^ 2 * ‖toEuclideanLin (M ^ (-s)) φ‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (hM.exp_neg_mul_re_inner_cfc_log_le_norm_rpow_neg_sq s φ hφ) hp.le
    _ = _ := hscale

end Matrix

end

end InversePowerLogJensen

section NormalizedInversePowerLogBound

/-!
## The norm rate bounds the logarithm in the deformed vector

Let `M` be positive definite and let `p` be a nonzero vector of norm at
most one. Normalize `M^(-s) p` to obtain `v`. Exponential Jensen and the
identity `M^s M^(-s) p = p` imply

`2s Re ⟨v, log(M) v⟩ ≤ -log ‖M^(-s) p‖²`.

This holds for every real exponent. In the lower area-law comparison
the exponent is positive and the vector `p` is the selected prevector.
No expectation identity is assumed: the normalization and the opposite
power cancellation give it directly.

### References

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

end

end NormalizedInversePowerLogBound
