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


/-! ## Real blocks for non-real conjugate eigenvalues -/

/-- The real `2 × 2` block representing the conjugate eigenvalues `a ± τ i`.

This is the block displayed in GLR Example 5.2 immediately before Theorem 5.3. The parameter
`τ` is nonzero when the eigenvalues are genuinely non-real; the definition is total because its
algebraic identities do not require that hypothesis. -/
def realConjugatePairBlock (a τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, τ; -τ, a]

/-- The basic realification block is selfadjoint for the unsigned two-dimensional sip metric. -/
theorem sipMatrix_two_mul_realConjugatePairBlock (a τ : ℝ) :
    sipMatrix 2 ℝ * realConjugatePairBlock a τ =
      (realConjugatePairBlock a τ).transpose * sipMatrix 2 ℝ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sipMatrix, finReversePerm, realConjugatePairBlock, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.rev]

/-- Reversing the row coordinate of the basic realification block is equivalent to reversing its
column coordinate after transposition. -/
theorem realConjugatePairBlock_rev_apply (a τ : ℝ) (i j : Fin 2) :
    realConjugatePairBlock a τ i.rev j = realConjugatePairBlock a τ j.rev i := by
  fin_cases i <;> fin_cases j <;> simp [realConjugatePairBlock, Fin.rev]

/-- The identity matrix on the realification coordinate has the same reversal symmetry. -/
theorem one_fin_two_rev_apply (i j : Fin 2) :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) i.rev j = (1 : Matrix (Fin 2) (Fin 2) ℝ) j.rev i := by
  simp only [Matrix.one_apply]
  congr 1
  apply propext
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [← h]
    simp

/-- Reversal of both the Jordan-chain index and the realification index.

Under the lexicographic identification `(Fin m × Fin 2) ≃ Fin (2m)`, its permutation matrix is
the unsigned even-dimensional sip block prescribed by GLR Theorem 5.3 for a non-real conjugate
pair. -/
def complexPairReversePerm (m : ℕ) : Equiv.Perm (Fin m × Fin 2) :=
  (finReversePerm m).prodCongr (finReversePerm 2)

@[simp]
theorem complexPairReversePerm_inv (m : ℕ) :
    (complexPairReversePerm m)⁻¹ = complexPairReversePerm m := by
  apply Equiv.ext
  intro i
  rfl

/-- The unsigned metric block for a length-`m` real Jordan chain associated with `a ± τ i`. -/
def complexPairSipMatrix (m : ℕ) : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  (complexPairReversePerm m).permMatrix ℝ

@[simp]
theorem complexPairSipMatrix_transpose (m : ℕ) :
    (complexPairSipMatrix m).transpose = complexPairSipMatrix m := by
  simp [complexPairSipMatrix]

@[simp]
theorem complexPairSipMatrix_mul_self (m : ℕ) :
    complexPairSipMatrix m * complexPairSipMatrix m = 1 := by
  change (complexPairReversePerm m).permMatrix ℝ *
      (complexPairReversePerm m).permMatrix ℝ = 1
  calc
    _ = (complexPairReversePerm m * complexPairReversePerm m).permMatrix ℝ :=
      (Matrix.permMatrix_mul (R := ℝ) (complexPairReversePerm m)
        (complexPairReversePerm m)).symm
    _ = 1 := by
      have h : complexPairReversePerm m * complexPairReversePerm m = 1 := by
        ext i <;> simp [complexPairReversePerm]
      rw [h]
      exact Matrix.permMatrix_one

/-- A real Jordan block for the conjugate pair `a ± τ i`, written in `2 × 2` blocks.

The diagonal blocks are `[[a, τ], [-τ, a]]`, the first block superdiagonal consists of `I₂`,
and all remaining blocks vanish. This is GLR's real Jordan form convention in Theorem 5.3. -/
def realConjugatePairJordanBlock (m : ℕ) (a τ : ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ := fun i j =>
  if i.1 = j.1 then realConjugatePairBlock a τ i.2 j.2
  else if i.1.val + 1 = j.1.val then (1 : Matrix (Fin 2) (Fin 2) ℝ) i.2 j.2
  else 0

/-- Left multiplication by a permutation matrix permutes matrix rows. -/
theorem permMatrix_mul_apply' {n : Type*} [Fintype n] [DecidableEq n]
    (σ : Equiv.Perm n) (A : Matrix n n ℝ) (i j : n) :
    (σ.permMatrix ℝ * A) i j = A (σ i) j := by
  change (σ.permMatrix ℝ *ᵥ fun k => A k j) i = _
  rw [Matrix.permMatrix_mulVec]
  rfl

/-- Right multiplication by a permutation matrix permutes matrix columns by the inverse. -/
theorem mul_permMatrix_apply' {n : Type*} [Fintype n] [DecidableEq n]
    (σ : Equiv.Perm n) (A : Matrix n n ℝ) (i j : n) :
    (A * σ.permMatrix ℝ) i j = A i (σ.symm j) := by
  change ((fun k => A i k) ᵥ* σ.permMatrix ℝ) j = _
  rw [Matrix.vecMul_permMatrix]
  rfl

/-- The real conjugate-pair Jordan block is selfadjoint for its unsigned sip metric.

This verifies the block identity `H A = Aᵀ H` from GLR Section 5.1. It also records why no sign
is attached to a non-real block: its canonical metric is the unsigned even-dimensional sip block. -/
theorem complexPairSipMatrix_mul_realConjugatePairJordanBlock
    (m : ℕ) (a τ : ℝ) :
    complexPairSipMatrix m * realConjugatePairJordanBlock m a τ =
      (realConjugatePairJordanBlock m a τ).transpose * complexPairSipMatrix m := by
  ext i j
  change (((complexPairReversePerm m).permMatrix ℝ *
      realConjugatePairJordanBlock m a τ) i j) =
    ((realConjugatePairJordanBlock m a τ).transpose *
      (complexPairReversePerm m).permMatrix ℝ) i j
  rw [permMatrix_mul_apply', mul_permMatrix_apply']
  simp only [transpose_apply]
  change realConjugatePairJordanBlock m a τ (i.1.rev, i.2.rev) j =
    realConjugatePairJordanBlock m a τ (j.1.rev, j.2.rev) i
  rcases i with ⟨i, ii⟩
  rcases j with ⟨j, jj⟩
  change (if i.rev = j then realConjugatePairBlock a τ ii.rev jj
      else if i.rev.val + 1 = j.val then (1 : Matrix (Fin 2) (Fin 2) ℝ) ii.rev jj
      else 0) =
    if j.rev = i then realConjugatePairBlock a τ jj.rev ii
      else if j.rev.val + 1 = i.val then (1 : Matrix (Fin 2) (Fin 2) ℝ) jj.rev ii
      else 0
  have hdiag : i.rev = j ↔ j.rev = i := by
    constructor
    · intro h
      rw [← h]
      simp
    · intro h
      rw [← h]
      simp
  have hsuperNat : m - (i.val + 1) + 1 = j.val ↔
      m - (j.val + 1) + 1 = i.val := by
    omega
  by_cases hd : i.rev = j
  · have hd' : j.rev = i := hdiag.mp hd
    simp [hd, hd', realConjugatePairBlock_rev_apply]
  · have hd' : j.rev ≠ i := fun h ↦ hd (hdiag.mpr h)
    by_cases hs : m - (i.val + 1) + 1 = j.val
    · have hs' : m - (j.val + 1) + 1 = i.val := hsuperNat.mp hs
      simp [hd, hd', hs, hs', one_fin_two_rev_apply]
    · have hs' : m - (j.val + 1) + 1 ≠ i.val := fun h ↦ hs (hsuperNat.mpr h)
      simp [hd, hd', hs, hs']

end Matrix
