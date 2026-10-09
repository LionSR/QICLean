/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixUnitConjugator
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Hermitian derivatives of inner matrix actions

A differentiable family of unitarily inner actions, equal to the identity at zero,
has derivative `i[H, ·]` for one Hermitian matrix `H`. The matrix-unit column
produces a differentiable intertwiner directly from the action; the pointwise
unitary witnesses are never differentiated or chosen coherently.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix
variable {D : ℕ} [NeZero D]

/-- The derivative at the identity of a differentiable family of unitarily inner
matrix actions is the commutator with a Hermitian generator, multiplied by `i`.
No regularity of the unitary witnesses is assumed. -/
theorem exists_hermitian_generator_of_differentiable_innerAction
    (α : ℝ → Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ)
    (hα : ∀ M, DifferentiableAt ℝ (fun t => α t M) 0)
    (hzero : ∀ M, α 0 M = M)
    (hinner : ∀ t, ∃ V : Matrix (Fin D) (Fin D) ℂ,
      V * Vᴴ = 1 ∧ ∀ M, α t M = V * M * Vᴴ) :
    ∃ H : Matrix (Fin D) (Fin D) ℂ, H.IsHermitian ∧
      ∀ M, HasDerivAt (fun t => α t M) (Complex.I • (H * M - M * H)) 0 := by
  let a : Fin D := 0
  let δ (M : Matrix (Fin D) (Fin D) ℂ) := deriv (fun t => α t M) 0
  let X (t : ℝ) := matrixUnitConjugator (α t) 1 a
  let Z : Matrix (Fin D) (Fin D) ℂ := fun i j => δ (single j a 1) i a
  have hX : HasDerivAt X Z 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    simpa [X, matrixUnitConjugator, Z, δ] using
      hasDerivAt_pi.mp (hasDerivAt_pi.mp (hα (single j a 1)).hasDerivAt i) a
  have hXzero : X 0 = 1 := by
    ext i j
    simp [X, matrixUnitConjugator, hzero, Matrix.single, Matrix.one_apply, eq_comm]
  have hinter (t : ℝ) (M : Matrix (Fin D) (Fin D) ℂ) : α t M * X t = X t * M := by
    obtain ⟨V, hV, hconj⟩ := hinner t
    let Y : GL (Fin D) ℂ := ⟨V, Vᴴ, hV, mul_eq_one_comm.mp hV⟩
    exact matrixUnitConjugator_intertwines (α t) 1 a Y hconj M
  have hδ (M : Matrix (Fin D) (Fin D) ℂ) : δ M = Z * M - M * Z := by
    have heq := (((hα M).hasDerivAt.mul hX).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => (hinter t M).symm)).unique (hX.mul_const M)
    simp only [hXzero, hzero, mul_one] at heq
    exact eq_sub_iff_add_eq.mpr heq
  have hstar (t : ℝ) (M : Matrix (Fin D) (Fin D) ℂ) : α t Mᴴ = (α t M)ᴴ := by
    obtain ⟨V, _, hconj⟩ := hinner t
    simp [hconj, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hδstar (M : Matrix (Fin D) (Fin D) ℂ) : δ Mᴴ = (δ M)ᴴ := by
    exact (hα Mᴴ).hasDerivAt.unique
      (((hα M).hasDerivAt.star).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => hstar t M))
  have hcenter (M : Matrix (Fin D) (Fin D) ℂ) :
      (Z + Zᴴ) * M = M * (Z + Zᴴ) := by
    have h := hδstar Mᴴ
    simp only [Matrix.conjTranspose_conjTranspose, hδ, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul] at h
    linear_combination (norm := noncomm_ring) h
  let H : Matrix (Fin D) (Fin D) ℂ := (-Complex.I / 2) • (Z - Zᴴ)
  have hH : H.IsHermitian := by
    change Hᴴ = H
    simp only [H, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    rw [show Zᴴ - Z = -(Z - Zᴴ) from (neg_sub _ _).symm, smul_neg]
    simp [neg_div]
  refine ⟨H, hH, fun M => (hα M).hasDerivAt.congr_deriv ?_⟩
  change δ M = _
  rw [hδ]
  have h := hcenter M
  dsimp [H]
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_smul]
  have hscalar : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
    norm_num [div_eq_mul_inv, ← mul_assoc]
  rw [hscalar]
  apply (smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0)).eq_iff.mp
  simp only [smul_smul, show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_smul,
    Matrix.sub_mul, Matrix.mul_sub]
  change (2 : ℂ) • (Z * M - M * Z) = _
  simp only [smul_sub, two_smul]
  linear_combination (norm := noncomm_ring) h

end Matrix
