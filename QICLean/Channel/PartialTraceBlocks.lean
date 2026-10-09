/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RectangularTraceNormAlgebra
import QICLean.Channel.PartialTrace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Reconstructing the physical operator from its affected blocks

Fixing the affected physical ket and bra indices leaves a matrix on the
exterior physical registers. Reinserting the affected matrix units recovers
the full operator, and its trace norm is at most the sum of the block trace
norms. No discarded or exterior dimension enters this estimate.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 518–549.
-/

noncomputable section
open scoped Kronecker Matrix
open MeasureTheory
namespace Matrix

/-- Reinsert each rectangular block with its corresponding physical matrix unit. -/
theorem eq_sum_single_kronecker_submatrix {X Y m n : Type}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (M : Matrix (X × m) (Y × n) ℂ) :
    M = ∑ x, ∑ y, single x y 1 ⊗ₖ M.submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j)) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp [Matrix.sum_apply, Matrix.single, Matrix.submatrix_apply, ite_and]

open Classical in
/-- The full trace norm is bounded by the sum of the affected physical block norms. -/
theorem rectangularTraceNorm_le_sum_submatrix {X Y m n : Type}
    [Fintype X] [Fintype Y] [Fintype m] [Fintype n]
    (M : Matrix (X × m) (Y × n) ℂ) :
    rectangularTraceNorm M ≤ ∑ x, ∑ y,
      rectangularTraceNorm (M.submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j))) := by
  classical
  calc
    _ = rectangularTraceNorm (∑ x, ∑ y,
        single x y 1 ⊗ₖ M.submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j))) :=
      congrArg rectangularTraceNorm (eq_sum_single_kronecker_submatrix M)
    _ ≤ ∑ x, rectangularTraceNorm (∑ y,
        single x y 1 ⊗ₖ M.submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j))) :=
      rectangularTraceNorm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun x _ ↦ by
      apply (rectangularTraceNorm_sum_le Finset.univ (fun y ↦
        single x y 1 ⊗ₖ M.submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j)))).trans
      apply Finset.sum_le_sum
      intro y _
      exact le_of_eq (rectangularTraceNorm_single_kronecker x y _)

/-- Fixing independent physical ket and bra indices commutes with tracing
the retained discarded registers. -/
theorem submatrix_partialTraceRight {X Y d : Type} [Fintype d]
    (M : Matrix ((X × Y) × d) ((X × Y) × d) ℂ) (x y : X) :
    (partialTraceRight M).submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j)) =
      partialTraceRight (M.submatrix (fun p : Y × d ↦ ((x, p.1), p.2))
        (fun q : Y × d ↦ ((y, q.1), q.2))) := by
  ext i j
  rfl

open Classical in
/-- Integrable block norms control the expected full physical trace norm. -/
theorem integral_rectangularTraceNorm_le_sum_submatrix
    {Ω X Y m n : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype X] [Fintype Y] [Fintype m] [Fintype n]
    (M : Ω → Matrix (X × m) (Y × n) ℂ)
    (hblock : ∀ x y, Integrable (fun ω ↦ rectangularTraceNorm
      ((M ω).submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j)))) μ) :
    (∫ ω, rectangularTraceNorm (M ω) ∂μ) ≤ ∑ x, ∑ y,
      ∫ ω, rectangularTraceNorm
        ((M ω).submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j))) ∂μ := by
  have hs := integrable_finsetSum Finset.univ fun x _ ↦
    integrable_finsetSum Finset.univ fun y _ ↦ hblock x y
  calc
    _ ≤ ∫ ω, ∑ x, ∑ y, rectangularTraceNorm
        ((M ω).submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j))) ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω ↦
        rectangularTraceNorm_nonneg (M ω)) hs
          (Filter.Eventually.of_forall fun ω ↦ rectangularTraceNorm_le_sum_submatrix (M ω))
    _ = _ := by
      rw [integral_finsetSum _ (fun x _ ↦
        integrable_finsetSum Finset.univ fun y _ ↦ hblock x y)]
      apply Finset.sum_congr rfl
      intro x _
      exact integral_finsetSum _ (fun y _ ↦ hblock x y)

end Matrix
