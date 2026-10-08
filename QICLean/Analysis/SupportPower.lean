/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralFunUnique
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.MeanInequalities

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
    rw [Complex.cpow_conj _ _
        (by rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_ne_zero.symm),
      Complex.conj_ofReal]

theorem spectralFun_apply (U : unitary (Matrix n n ℂ)) (f : n → ℂ) (i j : n) :
    spectralFun U f i j = ∑ k, (U : Matrix n n ℂ) i k * f k * star (U : Matrix n n ℂ) k j := by
  simp [spectralFun, mul_apply, diagonal, mul_assoc]

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

omit [DecidableEq n] in
theorem re_trace_conjTranspose_mul_self_eq_sum {m : Type*} [Fintype m] (N : Matrix n m ℂ) :
    (Nᴴ * N).trace.re = ∑ j, ∑ k, Complex.normSq (N j k) := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.normSq_apply, Complex.mul_re]

omit [Fintype n] [DecidableEq n] in
theorem sum_normSq_row_eq {m : Type*} [Fintype m] (N : Matrix n m ℂ) (j : n) :
    ∑ k, Complex.normSq (N j k) = ((N * Nᴴ) j j).re := by
  simp only [mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.normSq_apply, Complex.mul_re]

theorem normSq_supportCPow_entry {a : ℝ} (ha : 0 ≤ a) (z : ℂ) :
    Complex.normSq (if a = 0 then (0 : ℂ) else ((a : ℝ) : ℂ) ^ z) =
      if a = 0 then 0 else a ^ (2 * z.re) := by
  by_cases h : a = 0
  · simp [h]
  · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
    simp only [h, ite_false]
    rw [Complex.normSq_eq_norm_sq, norm_ofReal_cpow_of_pos hpos, ← Real.rpow_natCast,
      ← Real.rpow_mul hpos.le]
    ring_nf

/-- **Sandwich bound.**  For a positive semidefinite `A` with `tr A ≤ 1`, a contraction `c`
(`c cᴴ ≤ 1`, `cᴴ c ≤ 1`) and `0 ≤ Re z ≤ 1/2`, the Hilbert--Schmidt norm of
`A^{[z]} c A^{[1/2 - z]}` is at most one.  Area-law manuscript, `04-conditional.tex`,
lines 523–529. -/
theorem re_trace_supportCPow_sandwich_le (hA : A.PosSemidef) (htr : A.trace.re ≤ 1)
    {c : Matrix n n ℂ} (hc1 : c * cᴴ ≤ 1) (hc2 : cᴴ * c ≤ 1) {z : ℂ} (hz0 : 0 ≤ z.re)
    (hz1 : z.re ≤ 1 / 2) :
    ((supportCPow hA.1 z * c * supportCPow hA.1 (1 / 2 - z))ᴴ *
      (supportCPow hA.1 z * c * supportCPow hA.1 (1 / 2 - z))).trace.re ≤ 1 := by
  set U := hA.1.eigenvectorUnitary
  set a := hA.1.eigenvalues
  set φ : ℂ → n → ℂ := fun w k => if a k = 0 then 0 else ((a k : ℝ) : ℂ) ^ w
  set c' := star (U : Matrix n n ℂ) * c * (U : Matrix n n ℂ)
  set M := supportCPow hA.1 z * c * supportCPow hA.1 (1 / 2 - z)
  have hUU : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := Unitary.star_mul_self_of_mem U.2
  have hUU' : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := Unitary.mul_star_self_of_mem U.2
  -- conjugate to the eigenbasis
  set N := diagonal (φ z) * c' * diagonal (φ (1 / 2 - z))
  have hM : M = (U : Matrix n n ℂ) * N * star (U : Matrix n n ℂ) := by
    simp only [M, N, c', supportCPow, spectralFun, Matrix.mul_assoc]
    rfl
  have hUU2 : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := by
    rw [← star_eq_conjTranspose]; exact hUU
  have htrace : (Mᴴ * M).trace = (Nᴴ * N).trace := by
    rw [hM, conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose,
      conjTranspose_conjTranspose]
    rw [show (U : Matrix n n ℂ) * (Nᴴ * (U : Matrix n n ℂ)ᴴ) *
        ((U : Matrix n n ℂ) * N * (U : Matrix n n ℂ)ᴴ) =
        (U : Matrix n n ℂ) * (Nᴴ * ((U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ)) * N) *
          (U : Matrix n n ℂ)ᴴ by simp only [Matrix.mul_assoc],
      hUU2, Matrix.mul_one, trace_mul_cycle, hUU2, Matrix.one_mul]
  rw [htrace, re_trace_conjTranspose_mul_self_eq_sum]
  set s := z.re
  have ha : ∀ k, 0 ≤ a k := hA.eigenvalues_nonneg
  -- the pointwise weights
  have hw : ∀ j k, Complex.normSq (φ z j) * Complex.normSq (φ (1 / 2 - z) k) ≤
      2 * s * a j + (1 - 2 * s) * a k := by
    intro j k
    simp only [φ, normSq_supportCPow_entry (ha j), normSq_supportCPow_entry (ha k)]
    by_cases hj : a j = 0
    · simp only [hj, ite_true, zero_mul]
      nlinarith [ha k]
    · by_cases hk : a k = 0
      · simp only [hk, ite_true, mul_zero, hj, ite_false]
        nlinarith [ha j]
      · simp only [hj, hk, ite_false]
        have hre : (1 / 2 - z).re = 1 / 2 - s := by simp [s]
        rw [hre, show 2 * (1 / 2 - s) = 1 - 2 * s by ring]
        exact Real.geom_mean_le_arith_mean2_weighted (by linarith) (by linarith) (ha j) (ha k)
          (by ring)
  have hrow : ∀ j, ∑ k, Complex.normSq (c' j k) ≤ 1 := by
    intro j
    have := re_diag_conj_le_one hc1 U j
    change ((c' * c'ᴴ) j j).re ≤ 1 at this
    rwa [← sum_normSq_row_eq] at this
  have hcol : ∀ k, ∑ j, Complex.normSq (c' j k) ≤ 1 := by
    intro k
    have hc : cᴴ * cᴴᴴ ≤ 1 := by rwa [conjTranspose_conjTranspose]
    have := re_diag_conj_le_one hc U k
    have heq : star (U : Matrix n n ℂ) * cᴴ * (U : Matrix n n ℂ) = c'ᴴ := by
      simp only [c', conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    rw [heq, ← sum_normSq_row_eq] at this
    simpa [conjTranspose_apply, Complex.normSq_conj] using this
  have htrA : ∑ k, a k ≤ 1 := by
    rw [hA.1.trace_eq_sum_eigenvalues] at htr
    simpa using htr
  calc ∑ j, ∑ k, Complex.normSq (N j k)
      = ∑ j, ∑ k, Complex.normSq (c' j k) *
          (Complex.normSq (φ z j) * Complex.normSq (φ (1 / 2 - z) k)) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        simp only [N, mul_diagonal, diagonal_mul, Complex.normSq_mul]
        ring
    _ ≤ ∑ j, ∑ k, Complex.normSq (c' j k) * (2 * s * a j + (1 - 2 * s) * a k) := by
        gcongr with j _ k _
        · exact Complex.normSq_nonneg _
        · exact hw j k
    _ = 2 * s * ∑ j, a j * ∑ k, Complex.normSq (c' j k) +
          (1 - 2 * s) * ∑ k, a k * ∑ j, Complex.normSq (c' j k) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 2 * s * ∑ j, a j * 1 + (1 - 2 * s) * ∑ k, a k * 1 := by
        have h2s : 0 ≤ 2 * s := by linarith
        have h12s : 0 ≤ 1 - 2 * s := by linarith
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hrow j) (ha j)) h2s
        · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hcol k) (ha k)) h12s
    _ = ∑ k, a k := by simp only [mul_one]; ring
    _ ≤ 1 := htrA

end Matrix

end
