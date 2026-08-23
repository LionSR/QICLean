/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.SpinCover.Basic
import QICLean.Channel.LorentzNormalForm.QubitNormalForm
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The spinor action on qubit Pauli coordinates

This module formalizes the four-dimensional action in Wolf, Equations (2.41)--(2.43).
For `X ∈ SL(2,ℂ)`, the action is the Hermitian congruence
`M ↦ X * M * Xᴴ`.  In the real Pauli coordinates of a Hermitian qubit matrix,
this action preserves the Minkowski determinant form.

This is not `SpinCover.pauliConjAd`: that existing construction is the
three-dimensional adjoint action `M ↦ U * M * U⁻¹` on the traceless Pauli
matrices.  The two constructions agree on the spatial block only when the
conjugating matrix is unitary.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Equations (2.41)--(2.44)]
* `Notes/WolfNoteTexSource/ch02_representations.tex`, lines 1037--1081
-/

open scoped Matrix MatrixGroups BigOperators ComplexOrder
open Matrix Finset

noncomputable section

namespace Wolf

/-! ### Pauli coordinates and the Minkowski determinant form -/

/-- The real four-dimensional coordinate space used in Wolf, Equation (2.41). -/
abbrev MinkowskiSpace := Fin 4 → ℝ

/-- The spatial Pauli matrices in the four-coordinate convention agree with
the three Pauli matrices in `SpinCover`. -/
@[simp] theorem pauliMatrices_succ (i : Fin 3) :
    pauliMatrices i.succ = SpinCover.pauli i := by
  fin_cases i <;> rfl

/-- Each of the four Pauli matrices is Hermitian. -/
theorem pauliMatrices_isHermitian (i : Fin 4) : (pauliMatrices i).IsHermitian := by
  fin_cases i <;>
    (rw [Matrix.IsHermitian]
     ext a b
     fin_cases a <;> fin_cases b <;>
       simp [pauliMatrices, Matrix.conjTranspose_apply, Complex.conj_I])

/-- The trace pairing of the four Pauli matrices is
`tr(σᵢ σⱼ) = 2 δᵢⱼ`. -/
theorem trace_pauliMatrices_mul_pauliMatrices (i j : Fin 4) :
    Matrix.trace (pauliMatrices i * pauliMatrices j) = if i = j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliMatrices, Matrix.trace_fin_two, Matrix.mul_apply]

/-- The Hermitian qubit matrix with real Pauli coordinates `x`, namely
`M(x) = ∑ᵢ xᵢ σᵢ` in Wolf, lines 1040--1043. -/
def pauliMatrixOfMinkowski (x : MinkowskiSpace) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i : Fin 4, (x i : ℂ) • pauliMatrices i

/-- A matrix assembled from real Pauli coordinates is Hermitian. -/
theorem pauliMatrixOfMinkowski_isHermitian (x : MinkowskiSpace) :
    (pauliMatrixOfMinkowski x).IsHermitian := by
  apply isSelfAdjoint_sum
  intro i _
  exact (pauliMatrices_isHermitian i).smul (by simp [isSelfAdjoint_iff])

/-- The Minkowski quadratic form
`x₀² - x₁² - x₂² - x₃²` in Wolf, lines 1041--1044. -/
def minkowskiQuadratic (x : MinkowskiSpace) : ℝ :=
  x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2

/-- The determinant of a Hermitian qubit matrix is its Minkowski quadratic
form, as stated immediately before Wolf, Equation (2.41). -/
theorem det_pauliMatrixOfMinkowski (x : MinkowskiSpace) :
    Matrix.det (pauliMatrixOfMinkowski x) = (minkowskiQuadratic x : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [pauliMatrixOfMinkowski, Fin.sum_univ_four, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, pauliMatrices, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one]
  ring_nf
  rw [Complex.I_sq]
  simp [minkowskiQuadratic]
  ring

end Wolf
