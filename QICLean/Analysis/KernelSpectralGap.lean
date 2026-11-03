/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.EuclideanEigenvectorBasis
import QICLean.Analysis.LowEnergyPerturbation

/-!
# The quadratic-form gap above a Hermitian kernel

A lower bound for every nonzero real eigenvalue bounds the quadratic form
on the orthogonal complement of the whole kernel. No dimension-one
assumption is required. This is the spectral step used with detectability
in ALVV, arXiv:1602.08828v2, `lem:dl` and `thm:FF-tH`, lines 1508–1519
and 1562–1568.
-/

open Matrix
open scoped BigOperators InnerProductSpace

namespace Matrix.IsHermitian

/-- The actual spectral gap controls every vector orthogonal to the kernel.
The real bound may have either sign. Auxiliary to ALVV,
arXiv:1602.08828v2, `lem:dl` and `thm:FF-tH`, lines 1508–1519 and 1562–1568. -/
theorem mul_norm_sq_le_re_inner_of_spectral_gap
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {gamma : ℝ} (hgap : ∀ e ∈ spectrum ℝ A, e = 0 ∨ gamma ≤ e)
    (x : EuclideanSpace ℂ n)
    (horth : ∀ z : EuclideanSpace ℂ n,
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A z = 0 → ⟪z, x⟫_ℂ = 0) :
    gamma * ‖x‖ ^ 2 ≤ (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A x⟫_ℂ).re := by
  have hnorm : ‖x‖ ^ 2 = ∑ j, ‖hA.eigenvectorBasis.repr x j‖ ^ 2 := by
    simpa only [LinearIsometryEquiv.norm_map] using
      EuclideanSpace.norm_sq_eq (hA.eigenvectorBasis.repr x)
  change gamma * ‖x‖ ^ 2 ≤
    (⟪x, (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A).toLinearMap x⟫_ℂ).re
  rw [hnorm, Finset.mul_sum,
    hA.eigenvectorBasis.re_inner_apply_eq_sum_of_eigen hA.eigenvalues
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A).toLinearMap
      hA.toEuclideanCLM_eigenvectorBasis x]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rcases hgap (hA.eigenvalues j) (hA.eigenvalues_mem_spectrum_real j) with hz | hj
  · have hzero : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A
        (hA.eigenvectorBasis j) = 0 := by
      simpa only [hz, map_zero, zero_smul] using
        hA.toEuclideanCLM_eigenvectorBasis j
    have hcoeff : hA.eigenvectorBasis.repr x j = 0 :=
      (hA.eigenvectorBasis.repr_apply_apply x j).trans (horth _ hzero)
    simpa only [hcoeff, norm_zero, zero_pow two_ne_zero, mul_zero] using (le_refl (0 : ℝ))
  · exact mul_le_mul_of_nonneg_right hj (sq_nonneg _)

end Matrix.IsHermitian
