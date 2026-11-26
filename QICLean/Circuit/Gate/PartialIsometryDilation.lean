/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# A unitary dilation of a partial isometry

A square partial isometry admits a unitary dilation on two copies of its
space. The first output copy records its action, while the second records
the component orthogonal to its initial space. This is the one-flag
dilation in Section 5 of
TNLean `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

The declarations are ported from `TNLean/Circuit/PartialIsometryDilation.lean` at commit
`4150a33bacefe5ca311874b20cc4b90237fa447e` (Apache-2.0), with statements and names unchanged.

Moved from TNLean, `TNLean/MPS/MPU/Circuit/Merging/BalancedIntervalDilation.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The two-copy dilation of a square partial isometry. Source: the unitary
merging construction in Section 5 of
TNLean `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def partialIsometryDilation (A : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks A (1 - A * Aᴴ) (1 - Aᴴ * A) (-Aᴴ)

/-- The dilation is unitary whenever its input matrix is a partial isometry.
Source: the unitary merging construction in Section 5 of
TNLean `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem partialIsometryDilation_mem_unitaryGroup (A : Matrix n n ℂ)
    (hA : A * Aᴴ * A = A) : partialIsometryDilation A ∈ unitaryGroup (n ⊕ n) ℂ := by
  have hP : IsIdempotentElem (Aᴴ * A) := by
    change (Aᴴ * A) * (Aᴴ * A) = Aᴴ * A
    calc
      (Aᴴ * A) * (Aᴴ * A) = Aᴴ * (A * Aᴴ * A) := by simp only [Matrix.mul_assoc]
      _ = Aᴴ * A := by rw [hA]
  have hQ : IsIdempotentElem (A * Aᴴ) := by
    change (A * Aᴴ) * (A * Aᴴ) = A * Aᴴ
    calc
      (A * Aᴴ) * (A * Aᴴ) = (A * Aᴴ * A) * Aᴴ := by
        simp only [Matrix.mul_assoc]
      _ = A * Aᴴ := by rw [hA]
  rw [mem_unitaryGroup_iff']
  simp only [partialIsometryDilation, star_eq_conjTranspose, fromBlocks_conjTranspose,
    conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
    conjTranspose_conjTranspose, conjTranspose_neg, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hP.one_sub.eq]
    noncomm_ring
  · noncomm_ring
  · noncomm_ring
  · simp only [neg_mul_neg, hQ.one_sub.eq]
    noncomm_ring

/-- On an input in the first copy, the dilation records the partial isometry
in its first output and the complementary initial projection in its second.
Source: the unitary merging construction in Section 5 of
TNLean `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem partialIsometryDilation_mul_fromRows {m : Type*}
    (A : Matrix n n ℂ) (V : Matrix n m ℂ) :
    partialIsometryDilation A * fromRows V 0 =
      fromRows (A * V) ((1 - Aᴴ * A) * V) := by
  simp only [partialIsometryDilation, fromBlocks_mul_fromRows, Matrix.mul_zero, add_zero]

/-- The dilation preserves the Gram matrix of every collection of input
columns. Source: the unitary merging construction in Section 5 of
TNLean `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem partialIsometryDilation_initial_gram {m : Type*}
    (A : Matrix n n ℂ) (hA : A * Aᴴ * A = A) (V : Matrix n m ℂ) :
    (partialIsometryDilation A * fromRows V 0)ᴴ *
        (partialIsometryDilation A * fromRows V 0) = Vᴴ * V := by
  have hu := partialIsometryDilation_mem_unitaryGroup A hA
  rw [mem_unitaryGroup_iff'] at hu
  simp only [star_eq_conjTranspose] at hu
  rw [conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (partialIsometryDilation A)ᴴ, hu, Matrix.one_mul]
  simp only [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows,
    conjTranspose_zero, Matrix.zero_mul, add_zero]

/-- Projection onto the first output copy records exactly the Gram matrix
of the partial isometry applied to the input columns. This identity does
not require the partial-isometry hypothesis. Source: the unitary merging
construction in Section 5 of
TNLean `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem partialIsometryDilation_success_gram {m : Type*}
    (A : Matrix n n ℂ) (V : Matrix n m ℂ) :
    (partialIsometryDilation A * fromRows V 0)ᴴ *
        fromBlocks (1 : Matrix n n ℂ) 0 0 0 *
        (partialIsometryDilation A * fromRows V 0) = (A * V)ᴴ * (A * V) := by
  rw [partialIsometryDilation_mul_fromRows]
  simp only [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
    Matrix.mul_one, Matrix.mul_zero, add_zero, fromCols_mul_fromRows, Matrix.zero_mul]

end Matrix

section

open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace Matrix

variable {a b c : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- A matrix of output columns with an additional register in a basis state. -/
def basisResetOutput (V : Matrix a c ℂ) (z : b) : Matrix (a × b) c ℂ :=
  fun p j ↦ V p.1 j * (Pi.single z (1 : ℂ) : b → ℂ) p.2

omit [DecidableEq a] in
/-- Attaching a basis state preserves all inner products. -/
theorem basisResetOutput_gram (V : Matrix a c ℂ) (z : b) :
    (basisResetOutput V z)ᴴ * basisResetOutput V z = Vᴴ * V := by
  ext i j
  simp [mul_apply, basisResetOutput, Fintype.sum_prod_type, Pi.single_apply]

omit [DecidableEq a] [DecidableEq b] in
/-- Gram matrices are invariant under a reordering of output coordinates. -/
theorem reindex_rows_gram (V : Matrix a c ℂ) (e : a ≃ b) :
    (reindexLinearEquiv ℂ ℂ e (Equiv.refl c) V)ᴴ *
        reindexLinearEquiv ℂ ℂ e (Equiv.refl c) V = Vᴴ * V := by
  exact reindexLinearEquiv_mul ℂ ℂ (Equiv.refl c) e (Equiv.refl c) Vᴴ V

/-- A dilation on one tensor factor leaves the other factor unchanged. -/
theorem partialIsometryDilation_one_kronecker (A : Matrix b b ℂ) :
    partialIsometryDilation ((1 : Matrix a a ℂ) ⊗ₖ A) =
      reindexLinearEquiv ℂ ℂ (Equiv.prodSumDistrib a b b) (Equiv.prodSumDistrib a b b)
        ((1 : Matrix a a ℂ) ⊗ₖ partialIsometryDilation A) := by
  simp only [partialIsometryDilation, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul]
  ext (⟨p, x⟩ | ⟨p, x⟩) (⟨q, y⟩ | ⟨q, y⟩)
  all_goals simp [reindexLinearEquiv, Matrix.reindex, kroneckerMap_apply, one_apply, mul_sub]
  all_goals split_ifs <;> simp_all

end Matrix

end
