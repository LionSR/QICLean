/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Canonical metric blocks for Minkowski-selfadjoint matrices

This file develops the signed reversal matrices and real conjugate-pair blocks used in the real
canonical-pair theorem for selfadjoint matrices in an indefinite scalar product.

The conventions follow Gohberg--Lancaster--Rodman, *Matrices and Indefinite Scalar Products*
(1983), Part I, Chapter 5, Section 5.1, Theorem 5.3 (statement near p. 89, proof pp. 91--92).
Their ``sip'' matrix is the reversal permutation matrix. A sign `+1` or `-1` is attached to each
real-eigenvalue Jordan block, while a block for a non-real conjugate pair carries an unsigned
even-dimensional sip matrix. These are also the blocks denoted `N_J` in the proof of Theorem 3
of Verstraete--Dehaene--De Moor, arXiv:quant-ph/0011111v1, lines 175--196.

No channel or quantum-state definitions are used here.
-/

open Matrix

namespace Matrix

/-- Reversal of the ordered basis `0, ..., n - 1`, viewed as a permutation.

This is the permutation underlying the ``standard involutory permutation (sip) matrix'' in
GLR Theorem 5.3, Part I, Chapter 5, Section 5.1. -/
def finReversePerm (n : ℕ) : Equiv.Perm (Fin n) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

@[simp]
theorem finReversePerm_apply {n : ℕ} (i : Fin n) : finReversePerm n i = i.rev :=
  rfl

@[simp]
theorem finReversePerm_inv (n : ℕ) : (finReversePerm n)⁻¹ = finReversePerm n := by
  ext i
  rfl

@[simp]
theorem finReversePerm_mul_self (n : ℕ) : finReversePerm n * finReversePerm n = 1 := by
  ext i
  simp [finReversePerm]

/-- The `n × n` sip matrix `P_n`, with ones on the anti-diagonal.

GLR Theorem 5.3 uses `P_n` for the metric block paired with a Jordan block. -/
def sipMatrix (n : ℕ) (R : Type*) [Zero R] [One R] : Matrix (Fin n) (Fin n) R :=
  (finReversePerm n).permMatrix R

@[simp]
theorem sipMatrix_transpose (n : ℕ) (R : Type*) [Zero R] [One R] :
    (sipMatrix n R).transpose = sipMatrix n R := by
  simp [sipMatrix]

@[simp]
theorem sipMatrix_mul_self (n : ℕ) (R : Type*) [Semiring R] :
    sipMatrix n R * sipMatrix n R = 1 := by
  calc
    (finReversePerm n).permMatrix R * (finReversePerm n).permMatrix R =
        (finReversePerm n * finReversePerm n).permMatrix R :=
      (Matrix.permMatrix_mul (R := R) (finReversePerm n) (finReversePerm n)).symm
    _ = 1 := by simp

/-- A sign in the sign characteristic of a real-eigenvalue block in GLR Theorem 5.3. -/
inductive GLRSign where
  | positive
  | negative
  deriving DecidableEq

/-- The real scalar represented by a GLR sign. -/
def GLRSign.toReal : GLRSign → ℝ
  | .positive => 1
  | .negative => -1

@[simp] theorem GLRSign.toReal_positive : GLRSign.positive.toReal = 1 := rfl
@[simp] theorem GLRSign.toReal_negative : GLRSign.negative.toReal = -1 := rfl

@[simp]
theorem GLRSign.toReal_sq (ε : GLRSign) : ε.toReal ^ 2 = 1 := by
  cases ε <;> norm_num

/-- The signed sip block `ε P_n` attached to a real-eigenvalue Jordan block.

By GLR's convention, this construction is not used for non-real conjugate-pair blocks: those use
an unsigned even-dimensional `sipMatrix`. -/
def signedSipMatrix (ε : GLRSign) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ε.toReal • sipMatrix n ℝ

@[simp]
theorem signedSipMatrix_transpose (ε : GLRSign) (n : ℕ) :
    (signedSipMatrix ε n).transpose = signedSipMatrix ε n := by
  simp [signedSipMatrix]

@[simp]
theorem signedSipMatrix_mul_self (ε : GLRSign) (n : ℕ) :
    signedSipMatrix ε n * signedSipMatrix ε n = 1 := by
  rw [signedSipMatrix, Matrix.smul_mul, Matrix.mul_smul, sipMatrix_mul_self]
  have hε : ε.toReal * ε.toReal = 1 := by
    nlinarith [GLRSign.toReal_sq ε]
  rw [← mul_smul, hε, one_smul]

/-- Every signed sip block is invertible; it is its own inverse. -/
theorem signedSipMatrix_isUnit (ε : GLRSign) (n : ℕ) : IsUnit (signedSipMatrix ε n) := by
  rw [isUnit_iff_exists_inv]
  exact ⟨signedSipMatrix ε n, signedSipMatrix_mul_self ε n⟩

/-- An explicit change of basis diagonalizing the two-dimensional sip quadratic form. -/
def sipBasisTwo : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]

/-- An explicit change of basis diagonalizing the three-dimensional sip quadratic form. -/
def sipBasisThree : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 1; 0, 1, 0; 1, 0, -1]

/-- An explicit change of basis diagonalizing the four-dimensional sip quadratic form. -/
def sipBasisFour : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 1, 0; 0, 1, 0, 1; 0, 1, 0, -1; 1, 0, -1, 0]

/-- The two-dimensional sip matrix has one positive and one negative square after congruence. -/
theorem sipBasisTwo_congr :
    sipBasisTwo.transpose * sipMatrix 2 ℝ * sipBasisTwo = diagonal ![2, -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sipBasisTwo, sipMatrix, finReversePerm, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.rev] <;> norm_num

/-- The three-dimensional sip matrix has two positive and one negative square after congruence. -/
theorem sipBasisThree_congr :
    sipBasisThree.transpose * sipMatrix 3 ℝ * sipBasisThree = diagonal ![2, 1, -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sipBasisThree, sipMatrix, finReversePerm, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.rev] <;> norm_num

/-- The four-dimensional sip matrix has two positive and two negative squares after congruence. -/
theorem sipBasisFour_congr :
    sipBasisFour.transpose * sipMatrix 4 ℝ * sipBasisFour = diagonal ![2, 2, -2, -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sipBasisFour, sipMatrix, finReversePerm, Matrix.mul_apply,
      Fin.sum_univ_four, Fin.rev] <;> norm_num

end Matrix
