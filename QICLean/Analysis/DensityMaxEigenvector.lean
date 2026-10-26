/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef

/-!
# A unit eigenvector for the largest eigenvalue of a density matrix

A positive semidefinite matrix of trace one has a unit eigenvector with a positive eigenvalue
at least as large as every real eigenvalue. The first vector of the sorted orthonormal
eigenbasis gives a choice determined by the density matrix alone.

This is an auxiliary spectral selection fact for Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`, lines 493–505.
-/

open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n]

/-- A density matrix has a unit eigenvector for its largest eigenvalue, which is positive.
The maximum bounds every supplied real eigenvalue with a nonzero eigenvector.
Auxiliary spectral selection for LVV13, `algo53.tex`, Lemma `l:leading`, lines 493–505. -/
theorem PosSemidef.exists_unit_eigenvector_max_eigenvalue
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    ∃ (u : EuclideanSpace ℂ n) (μ₀ : ℝ), ‖u‖ = 1 ∧
      σ *ᵥ WithLp.ofLp u = (μ₀ : ℂ) • WithLp.ofLp u ∧ 0 < μ₀ ∧
      ∀ (μ : ℝ) (w : EuclideanSpace ℂ n), w ≠ 0 →
        σ *ᵥ WithLp.ofLp w = (μ : ℂ) • WithLp.ofLp w → μ ≤ μ₀ := by
  classical
  let hS := hσ.isHermitian
  have hsum : ∑ i, hS.eigenvalues i = 1 := by
    simpa [hS.trace_eq_sum_eigenvalues] using congrArg Complex.re htr
  obtain ⟨i, hi⟩ : ∃ i, 0 < hS.eigenvalues i := by
    have hpos : 0 < ∑ i, hS.eigenvalues i := by rw [hsum]; norm_num
    simpa only [Finset.mem_univ, true_and] using
      (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hσ.eigenvalues_nonneg i)).mp hpos
  have hdim : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let k : Fin (Fintype.card n) := ⟨0, hdim⟩
  let mu := hS.eigenvalues₀ k
  have hmax (j : Fin (Fintype.card n)) : hS.eigenvalues₀ j ≤ mu := by
    apply hS.eigenvalues₀_antitone
    change 0 ≤ j.val
    exact Nat.zero_le _
  have heig : hS.eigenvalues (e k) = mu := by
    change hS.eigenvalues₀ (e.symm (e k)) = hS.eigenvalues₀ k
    rw [e.symm_apply_apply]
  have hpos : 0 < mu := by
    have hh := hmax (e.symm i)
    change hS.eigenvalues i ≤ mu at hh
    exact hi.trans_le hh
  refine ⟨hS.eigenvectorBasis (e k), mu, hS.eigenvectorBasis.orthonormal.1 _, ?_, hpos, ?_⟩
  · rw [← heig]
    exact (hS.mulVec_eigenvectorBasis (e k)).trans (Complex.coe_smul _ _).symm
  intro μ w hw hwσ
  have hwlin : toEuclideanLin σ w = (μ : ℂ) • w := by
    apply WithLp.ofLp_injective 2
    simpa only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using hwσ
  have hev : Module.End.HasEigenvalue (toEuclideanLin σ) (μ : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hwlin, hw⟩
  obtain ⟨j, hj⟩ := (isSymmetric_toEuclideanLin_iff.mpr hS).exists_eigenvalues_eq
    finrank_euclideanSpace hev
  have heq : μ = hS.eigenvalues₀ j := Complex.ofReal_injective hj.symm
  rw [heq]
  exact hmax j

end Matrix
