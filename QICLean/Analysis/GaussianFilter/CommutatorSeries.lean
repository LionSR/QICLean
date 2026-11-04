/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.MatrixIntegral
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The Gaussian filter as a convergent commutator series

For a Hermitian matrix `H`, Gaussian averaging of `exp(itH) W exp(-itH)` with variance
`h` is the exponential of `-(h/2) ad_H²`, where `ad_H(W) = HW - WH`. Thus its expansion
is `∑ᵣ (-h/2)ʳ/r! ad_H^{2r}(W)`, convergent in the operator norm.

This is the corrected commutator expansion in Hastings, *Solving gapped Hamiltonians
locally*, arXiv:cond-mat/0508554v3, lines 1005–1009. For the source's variance
`h = q/ΔE²`, the coefficient at order `2r` contains `(q/ΔE²)ʳ`, rather than the printed
power `(q/ΔE²)^{2r}`. The proof uses the finite-dimensional spectral theorem and the
norm-convergent exponential series, without interchanging an integral and a series.

**Local fix (Gaussian moments):** The corrected variance power is documented at
https://sirui-lu.com/QICLean/paper-gaps/hastings05_gaussian_series_coefficients.pdf.
-/

open Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace NNReal

namespace GaussianFilter

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Commutation with `H`, as a continuous linear map on matrices.
Hastings, arXiv:cond-mat/0508554v3, lines 856–877 and 1005–1009. -/
noncomputable def commutatorCLM (H : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  ContinuousLinearMap.mul ℂ _ H - (ContinuousLinearMap.mul ℂ _).flip H

@[simp] theorem commutatorCLM_apply (H W : Matrix n n ℂ) :
    commutatorCLM H W = H * W - W * H := rfl

private noncomputable def matrixCoefficientCLM (v w : n → ℂ) : Matrix n n ℂ →L[ℂ] ℂ :=
  ((dotProductBilin ℂ ℂ (star v)).comp ((Matrix.mulVecBilin ℂ ℂ).flip w)).toContinuousLinearMap

omit [DecidableEq n] in
private theorem matrixCoefficientCLM_apply (v w : n → ℂ) (W : Matrix n n ℂ) :
    matrixCoefficientCLM v w W = star v ⬝ᵥ (W *ᵥ w) := rfl

private theorem matrixCoefficientCLM_commutator {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {v w : n → ℂ} {E E' : ℝ} (hv : H *ᵥ v = (E : ℂ) • v)
    (hw : H *ᵥ w = (E' : ℂ) • w) (W : Matrix n n ℂ) :
    matrixCoefficientCLM v w (commutatorCLM H W) =
      ((E : ℂ) - E') * matrixCoefficientCLM v w W := by
  have hstar : star v ᵥ* H = (E : ℂ) • star v := by
    rw [← hH.eq, ← Matrix.star_mulVec, hv, star_smul]
    simp only [Complex.star_def, Complex.conj_ofReal]
  change star v ⬝ᵥ ((H * W - W * H) *ᵥ w) =
    ((E : ℂ) - E') * (star v ⬝ᵥ (W *ᵥ w))
  rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec, hw,
    mulVec_smul, dotProduct_smul, dotProduct_mulVec, hstar, smul_dotProduct, smul_eq_mul]
  simp only [smul_eq_mul, sub_mul]

private theorem apply_exp_of_comp_eq_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (T : E →L[ℂ] E) (L : E →L[ℂ] ℂ) (c : ℂ)
    (hL : ∀ x, L (T x) = c * L x) (x : E) :
    L (NormedSpace.exp T x) = Complex.exp c * L x := by
  have hpow : ∀ k : ℕ, L ((T ^ k) x) = c ^ k * L x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [pow_succ', mul_apply_eq_comp, hL, ih, mul_assoc]
  let eval : (E →L[ℂ] E) →L[ℂ] ℂ := L.comp (ContinuousLinearMap.apply ℂ E x)
  have hexp := eval.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T)
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).mul_right (L x)
  have hleft : HasSum (fun k : ℕ ↦ (k.factorial : ℂ)⁻¹ * c ^ k * L x)
      (L (NormedSpace.exp T x)) := by
    simpa only [eval, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      _root_.smul_apply, map_smul, hpow, smul_eq_mul, mul_assoc] using hexp
  exact hleft.unique (by simpa only [Complex.exp_eq_exp_ℂ, smul_eq_mul] using hscalar)

private theorem matrixCoefficientCLM_exp_commutator (h : ℝ≥0) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {v w : n → ℂ} {E E' : ℝ}
    (hv : H *ᵥ v = (E : ℂ) • v) (hw : H *ᵥ w = (E' : ℂ) • w)
    (W : Matrix n n ℂ) :
    matrixCoefficientCLM v w
        (NormedSpace.exp ((-(h : ℂ) / 2) • commutatorCLM H ^ 2) W) =
      Complex.exp (-(h : ℂ) * ((E - E' : ℝ) : ℂ) ^ 2 / 2) *
        matrixCoefficientCLM v w W := by
  apply apply_exp_of_comp_eq_mul
  intro V
  rw [_root_.smul_apply, map_smul, pow_two, mul_apply_eq_comp,
    matrixCoefficientCLM_commutator hH hv hw, matrixCoefficientCLM_commutator hH hv hw]
  simp only [smul_eq_mul, Complex.ofReal_sub]
  ring

/-- The Gaussian filter is the exponential of `-(h/2) ad_H²`.
Hastings, arXiv:cond-mat/0508554v3, lines 1005–1009, with the corrected
variance power stated in the module docstring. -/
theorem gaussianIntertwiner_eq_exp_commutator (h : ℝ≥0) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (W : Matrix n n ℂ) :
    gaussianIntertwiner h H H W =
      NormedSpace.exp ((-(h : ℂ) / 2) • commutatorCLM H ^ 2) W := by
  apply Matrix.toEuclideanLin.injective
  apply hH.eigenvectorBasis.toBasis.ext
  intro j
  apply InnerProductSpace.ext_inner_left_basis hH.eigenvectorBasis.toBasis
  intro i
  simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply, matrixCoefficientCLM_apply, dotProduct_comm] using
    (dotProduct_gaussianIntertwiner_mulVec h hH hH W
      (SpectralFilter.mulVec_eigenvectorBasis_complex hH i)
      (SpectralFilter.mulVec_eigenvectorBasis_complex hH j)).trans
      (matrixCoefficientCLM_exp_commutator h hH
        (SpectralFilter.mulVec_eigenvectorBasis_complex hH i)
        (SpectralFilter.mulVec_eigenvectorBasis_complex hH j) W).symm

/-- The Gaussian filter has a norm-convergent expansion in even commutators.
Hastings, arXiv:cond-mat/0508554v3, lines 1005–1009, with the corrected
coefficient `(-h/2)^r/r!`. -/
theorem hasSum_gaussianIntertwiner_commutator (h : ℝ≥0) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (W : Matrix n n ℂ) :
    HasSum (fun r : ℕ ↦
      ((-(h : ℂ) / 2) ^ r / (r.factorial : ℂ)) •
        ((commutatorCLM H) ^ (2 * r)) W)
      (gaussianIntertwiner h H H W) := by
  rw [gaussianIntertwiner_eq_exp_commutator h hH]
  have hs := (ContinuousLinearMap.apply ℂ (Matrix n n ℂ) W).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
      ((-(h : ℂ) / 2) • commutatorCLM H ^ 2))
  have hpow : ∀ r : ℕ,
      (((-(h : ℂ) / 2) • commutatorCLM H ^ 2) ^ r) W =
        (-(h : ℂ) / 2) ^ r • ((commutatorCLM H ^ 2) ^ r) W := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ' ((-(h : ℂ) / 2) • commutatorCLM H ^ 2), mul_apply_eq_comp,
        _root_.smul_apply, ih, map_smul, smul_smul, pow_succ' (-(h : ℂ) / 2),
        pow_succ' (commutatorCLM H ^ 2), mul_apply_eq_comp]
  simp only [ContinuousLinearMap.apply_apply, _root_.smul_apply] at hs
  simp_rw [hpow] at hs
  simpa only [← pow_mul, smul_smul, div_eq_mul_inv, mul_comm] using hs

end GaussianFilter
