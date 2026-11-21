/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef

/-!
# Uniqueness of a density matrix eigenvector above one half

For a positive semidefinite matrix of trace one, an eigenvalue larger than one half has
multiplicity one. Thus any two unit eigenvectors with eigenvalues larger than one half have
the same eigenvalue and differ by a complex scalar of norm one.

This is an auxiliary spectral fact for the choice of the leading eigenvector in Landau,
Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`, lines 493–505.
It depends only on the density matrix, without a Hamiltonian or ground vector.
-/

open scoped InnerProductSpace ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n]

/-- Two unit eigenvectors of a density matrix with eigenvalues larger than one half have
identical eigenvalues and differ by a unit complex phase. Auxiliary spectral uniqueness
for LVV13, `algo53.tex`, Lemma `l:leading`, lines 493–505. -/
theorem PosSemidef.eigenvalue_eq_and_exists_unit_smul_of_gt_half
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u v : EuclideanSpace ℂ n} {μ ν : ℝ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hvσ : σ *ᵥ WithLp.ofLp v = (ν : ℂ) • WithLp.ofLp v)
    (hμ : 1 / 2 < μ) (hν : 1 / 2 < ν) :
    μ = ν ∧ ∃ z : ℂ, ‖z‖ = 1 ∧ v = z • u := by
  classical
  let hS := hσ.isHermitian
  let b := hS.eigenvectorBasis
  let lam := hS.eigenvalues
  have hlam0 (i : n) : 0 ≤ lam i := hσ.eigenvalues_nonneg i
  have hlam1 : ∑ i, lam i = 1 := by
    have hh := congrArg Complex.re hS.trace_eq_sum_eigenvalues
    rw [htr, Complex.re_sum] at hh
    simpa [lam] using hh.symm
  have hunique {i j : n} (hi : 1 / 2 < lam i) (hj : 1 / 2 < lam j) : i = j := by
    by_contra hne
    have hpair : lam i + lam j ≤ ∑ k, lam k := by
      rw [← Finset.sum_pair (f := lam) hne]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun k _ _ ↦ hlam0 k
    linarith only [hpair, hlam1, hi, hj]
  have hcoeff (w : EuclideanSpace ℂ n) (α : ℝ)
      (hwσ : σ *ᵥ WithLp.ofLp w = (α : ℂ) • WithLp.ofLp w) (i : n) :
      (lam i : ℂ) * b.repr w i = (α : ℂ) * b.repr w i := by
    have hw : toEuclideanLin σ w = (α : ℂ) • w := by
      apply WithLp.ofLp_injective 2
      simpa only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using hwσ
    have hb : toEuclideanLin σ (b i) = (lam i : ℂ) • b i := by
      apply WithLp.ofLp_injective 2
      simp only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul]
      exact (hS.mulVec_eigenvectorBasis i).trans (Complex.coe_smul _ _).symm
    have hh := (isSymmetric_toEuclideanLin_iff.mpr hS) (b i) w
    rw [hb, hw, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      ← b.repr_apply_apply] at hh
    exact hh
  have hrepr (w : EuclideanSpace ℂ n) (α : ℝ) (hw : ‖w‖ = 1)
      (hwσ : σ *ᵥ WithLp.ofLp w = (α : ℂ) • WithLp.ofLp w) (hα : 1 / 2 < α) :
      ∃ (i : n) (z : ℂ), lam i = α ∧ ‖z‖ = 1 ∧ w = z • b i := by
    obtain ⟨i, hi⟩ : ∃ i, b.repr w i ≠ 0 := by
      by_contra! hz
      have hw0 : w = 0 := b.repr.injective (by ext j; simpa using hz j)
      rw [hw0, norm_zero] at hw
      norm_num at hw
    have hlam : lam i = α := by
      exact Complex.ofReal_injective (mul_right_cancel₀ hi (hcoeff w α hwσ i))
    have hz (j : n) (hji : j ≠ i) : b.repr w j = 0 := by
      by_contra hj
      have hlamj : lam j = α := by
        exact Complex.ofReal_injective (mul_right_cancel₀ hj (hcoeff w α hwσ j))
      exact hji (hunique (hlamj ▸ hα) (hlam ▸ hα))
    have hwrepr : w = b.repr w i • b i := by
      calc
        w = ∑ j, b.repr w j • b j := (b.sum_repr w).symm
        _ = b.repr w i • b i :=
          Finset.sum_eq_single i (fun j _ hji ↦ by rw [hz j hji, zero_smul])
            (fun hi ↦ (hi (Finset.mem_univ i)).elim)
    refine ⟨i, b.repr w i, hlam, ?_, hwrepr⟩
    have hh := congrArg norm hwrepr
    simpa only [hw, norm_smul, b.orthonormal.1 i, mul_one] using hh.symm
  obtain ⟨i, a, hi, ha, hua⟩ := hrepr u μ hu huσ hμ
  obtain ⟨j, d, hj, hd, hvd⟩ := hrepr v ν hv hvσ hν
  have hij : i = j := hunique (hi ▸ hμ) (hj ▸ hν)
  subst j
  have ha0 : a ≠ 0 := by
    intro hh
    simp only [hh, norm_zero, zero_ne_one] at ha
  refine ⟨hi.symm.trans hj, d / a, ?_, ?_⟩
  · rw [norm_div, hd, ha, div_one]
  · rw [hvd, hua, smul_smul, div_mul_cancel₀ _ ha0]

end Matrix
