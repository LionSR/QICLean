/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ApproximateDiagonalization.Recursive

/-!
# Weighted commutator kernels and a constructed orthonormal basis

Normalization by an operator norm envelope, followed by the actual spectral
refinement, gives a basis with at most dimension minus one anchors.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708.
-/

open scoped InnerProductSpace

namespace ApproximateDiagonalization

variable {E κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Normalization by a norm envelope can be undone even for zero terms.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem smul_inv_smul_eq_of_norm_le (B : κ → E →L[ℂ] E) (w : κ → ℝ)
    (hNorm : ∀ i, ‖B i‖ ≤ w i) (i : κ) : w i • ((w i)⁻¹ • B i) = B i := by
  by_cases hi : w i = 0
  · have hBi : B i = 0 := norm_eq_zero.mp
      (((hNorm i).trans_eq hi).antisymm (norm_nonneg _))
    simp [hi, hBi]
  · simp only [smul_smul, mul_inv_cancel₀ hi, one_smul]

omit [CompleteSpace E] in
/-- Weighted commutator decay becomes an unweighted estimate after normalization.
No nonzero-term hypothesis is needed.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_commutator_inv_smul_le (B : κ → E →L[ℂ] E) (w : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    {C : ℝ} (hC : 0 ≤ C) (f : κ → κ → ℝ) (hf : ∀ i j, 0 ≤ f i j)
    (hcomm : ∀ i j, ‖B i * B j - B j * B i‖ ≤ C * w i * w j * f i j) (i j : κ) :
    ‖((w i)⁻¹ • B i) * ((w j)⁻¹ • B j) -
        ((w j)⁻¹ • B j) * ((w i)⁻¹ • B i)‖ ≤ C * f i j := by
  by_cases hi : w i = 0
  · simp only [hi, inv_zero, zero_smul, zero_mul, mul_zero, sub_self, norm_zero]
    exact mul_nonneg hC (hf i j)
  by_cases hj : w j = 0
  · simp only [hj, inv_zero, zero_smul, zero_mul, mul_zero, sub_self, norm_zero]
    exact mul_nonneg hC (hf i j)
  have hwi : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hi)
  have hwj : 0 < w j := lt_of_le_of_ne (hw j) (Ne.symm hj)
  have heq : ((w i)⁻¹ • B i) * ((w j)⁻¹ • B j) -
        ((w j)⁻¹ • B j) * ((w i)⁻¹ • B i) =
      ((w i)⁻¹ * (w j)⁻¹) • (B i * B j - B j * B i) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_comm ((w j)⁻¹) ((w i)⁻¹), smul_sub]
  rw [heq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hwi.le) (inv_nonneg.mpr hwj.le))]
  calc
    _ ≤ ((w i)⁻¹ * (w j)⁻¹) * (C * w i * w j * f i j) :=
      mul_le_mul_of_nonneg_left (hcomm i j) (by positivity)
    _ = _ := by field_simp

/-- Applying the recursive basis theorem after one normalization restores the original
term weights. Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem exists_orthonormalBasis_uniform_weighted_kernel [FiniteDimensional ℂ E] [Finite κ]
    (B : κ → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i))
    (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hNorm : ∀ i, ‖B i‖ ≤ w i)
    (k : κ → κ → ℝ) (hk0 : ∀ i j, 0 ≤ k i j) (hk1 : ∀ i j, k i j ≤ 1)
    (hksymm : ∀ i j, k i j = k j i) (hktri : ∀ i j l, k i j * k j l ≤ k i l)
    {C : ℝ} (hC : 0 ≤ C)
    (hcomm : ∀ i j, ‖B i * B j - B j * B i‖ ≤ C * w i * w j * k i j) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (s : List κ),
      s.length ≤ Module.finrank ℂ E - 1 ∧
      ∀ i a c, a ≠ c → ‖⟪b a, B i (b c)⟫_ℂ‖ ≤
        recursiveBasisCoeff (Module.finrank ℂ E) C * w i *
          listKernelSum (sqrtKernel k (Module.finrank ℂ E)) s i := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let D : κ → E →L[ℂ] E := fun i ↦ (w i)⁻¹ • B i
  have hD (i : κ) : IsSelfAdjoint (D i) := (IsSelfAdjoint.all ((w i)⁻¹)).smul (hB i)
  obtain ⟨b, s, hs, hb⟩ := exists_orthonormalBasis_uniform_kernel D hD k hk0 hk1 hksymm hktri
    hC (norm_commutator_inv_smul_le B w hw hC k hk0 hcomm)
  refine ⟨b, s, hs, fun i a c hac ↦ ?_⟩
  have heq : ‖⟪b a, B i (b c)⟫_ℂ‖ = w i * ‖⟪b a, D i (b c)⟫_ℂ‖ := by
    rw [← smul_inv_smul_eq_of_norm_le B w hNorm i]
    simp only [D, _root_.smul_apply, ← Complex.coe_smul, inner_smul_right, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left (hb i a c hac) (hw i)).trans_eq (by ring)

end ApproximateDiagonalization
