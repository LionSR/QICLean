/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralFunUnique
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Complex powers vanishing on the kernel

For a Hermitian matrix `A` with eigenbasis `U` and eigenvalues `λ`, the complex power
`A^{[z]} = ∑_{λ ≠ 0} λ^z Π_λ` vanishes on the kernel for every `z`, including `z = 0`,
where it is the support projection.  This file proves the algebra of these powers, their
analyticity in `z`, and the sandwich bound
`‖A^{[z]} c A^{[1/2 - z]}‖₂ ≤ 1` for a density matrix `A`, a contraction `c` and
`0 ≤ Re z ≤ 1/2`.

## Main definitions

* `Matrix.supportCPow`.

## Main results

* `Matrix.supportCPow_mul_supportCPow`, `Matrix.conjTranspose_supportCPow`.
* `Matrix.differentiable_supportCPow`.
* `Matrix.re_trace_supportCPow_sandwich_le`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), Section 5,
  `04-conditional.tex`, lines 14–25 (the notation `ρ^{[z]}`) and lines 523–529 (the
  sandwich bound).
-/

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The complex power `A^{[z]}` vanishing on the kernel.  Area-law manuscript,
`04-conditional.tex`, lines 14–22. -/
def supportCPow (hA : A.IsHermitian) (z : ℂ) : Matrix n n ℂ :=
  spectralFun hA.eigenvectorUnitary
    (fun k => if hA.eigenvalues k = 0 then 0 else ((hA.eigenvalues k : ℝ) : ℂ) ^ z)

theorem supportCPow_mul_supportCPow (hA : A.IsHermitian) (z w : ℂ) :
    supportCPow hA z * supportCPow hA w = supportCPow hA (z + w) := by
  rw [supportCPow, supportCPow, supportCPow, spectralFun_mul]
  congr 1; funext k
  by_cases h : hA.eigenvalues k = 0
  · simp [h]
  · simp only [Pi.mul_apply, h, ite_false]
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 h)]

theorem conjTranspose_supportCPow (hA : A.PosSemidef) (z : ℂ) :
    (supportCPow hA.1 z)ᴴ = supportCPow hA.1 (starRingEnd ℂ z) := by
  rw [supportCPow, conjTranspose_spectralFun, supportCPow]
  congr 1; funext k
  by_cases h : hA.1.eigenvalues k = 0
  · simp [h]
  · simp only [Pi.star_apply, h, ite_false, RCLike.star_def]
    have hpos : 0 < hA.1.eigenvalues k := lt_of_le_of_ne (hA.eigenvalues_nonneg k) (Ne.symm h)
    rw [Complex.cpow_conj _ _ (by rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_ne_zero.symm),
      Complex.conj_ofReal]

theorem spectralFun_apply (U : unitary (Matrix n n ℂ)) (f : n → ℂ) (i j : n) :
    spectralFun U f i j = ∑ k, (U : Matrix n n ℂ) i k * f k * star (U : Matrix n n ℂ) k j := by
  simp [spectralFun, mul_apply, diagonal, Finset.sum_mul, mul_assoc]

theorem differentiable_spectralFun_apply (U : unitary (Matrix n n ℂ)) {φ : ℂ → n → ℂ}
    (hφ : ∀ k, Differentiable ℂ (fun z => φ z k)) (i j : n) :
    Differentiable ℂ (fun z => spectralFun U (φ z) i j) := by
  simp only [spectralFun_apply]
  exact Differentiable.fun_sum fun k _ =>
    ((differentiable_const _).mul (hφ k)).mul (differentiable_const _)

theorem differentiable_supportCPow_apply (hA : A.IsHermitian) (i j : n) :
    Differentiable ℂ (fun z => supportCPow hA z i j) := by
  refine differentiable_spectralFun_apply _ (fun k => ?_) i j
  by_cases h : hA.eigenvalues k = 0
  · simp only [h, ite_true]; exact differentiable_const _
  · simp only [h, ite_false]
    exact differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 h))

theorem differentiable_mul_apply {l m p : Type*} [Fintype m] {M : ℂ → Matrix l m ℂ}
    {N : ℂ → Matrix m p ℂ} (hM : ∀ i j, Differentiable ℂ (fun z => M z i j))
    (hN : ∀ i j, Differentiable ℂ (fun z => N z i j)) (i : l) (j : p) :
    Differentiable ℂ (fun z => (M z * N z) i j) := by
  simp only [mul_apply]
  exact Differentiable.fun_sum fun k _ => (hM i k).mul (hN k j)

theorem norm_ofReal_cpow_of_pos {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ‖((a : ℝ) : ℂ) ^ z‖ = a ^ z.re := Complex.norm_cpow_eq_rpow_re_of_pos ha z

/-- A contraction has diagonal entries of `c cᴴ` at most one in every orthonormal basis. -/
theorem re_diag_conj_le_one {c : Matrix n n ℂ} (hc : c * cᴴ ≤ 1) (U : unitary (Matrix n n ℂ))
    (j : n) : (((star (U : Matrix n n ℂ) * c * (U : Matrix n n ℂ)) *
      (star (U : Matrix n n ℂ) * c * (U : Matrix n n ℂ))ᴴ) j j).re ≤ 1 := by
  have h := (le_iff.1 hc).conjTranspose_mul_mul_same (U : Matrix n n ℂ)
  have hd := h.diag_nonneg (i := j)
  have heq : (U : Matrix n n ℂ)ᴴ * (1 - c * cᴴ) * (U : Matrix n n ℂ) =
      1 - (star (U : Matrix n n ℂ) * c * (U : Matrix n n ℂ)) *
        (star (U : Matrix n n ℂ) * c * (U : Matrix n n ℂ))ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem U.2, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix n n ℂ) (star (U : Matrix n n ℂ)),
      Unitary.mul_star_self_of_mem U.2, Matrix.one_mul]
  rw [heq] at hd
  rw [Complex.nonneg_iff] at hd
  simp only [sub_apply, one_apply_eq, Complex.sub_re, Complex.one_re] at hd
  linarith [hd.1]

end Matrix

end
