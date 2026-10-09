/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.HermitianUnitaryPath
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Ring

/-!
# Exponentials of the two tensor-factor actions

The two commuting tensor-factor actions exponentiate separately.
-/

open scoped Matrix Kronecker Matrix.Norms.Operator
open NormedSpace

namespace Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Exponentiation commutes with adjoining an identity on the right. -/
theorem exp_kronecker_one (X : Matrix m m ℂ) :
    exp (X ⊗ₖ (1 : Matrix n n ℂ)) = exp X ⊗ₖ (1 : Matrix n n ℂ) := by
  let f : Matrix m m ℂ →+* Matrix (m × n) (m × n) ℂ := {
    toFun := fun Y => Y ⊗ₖ (1 : Matrix n n ℂ)
    map_one' := Matrix.one_kronecker_one
    map_mul' := fun Y Z => by rw [← Matrix.mul_kronecker_mul]; simp
    map_zero' := Matrix.zero_kronecker _
    map_add' := fun Y Z => Matrix.add_kronecker Y Z _ }
  have hf : Continuous f := by
    change Continuous (fun Y : Matrix m m ℂ =>
      Matrix.kroneckerMap (· * ·) Y (1 : Matrix n n ℂ))
    unfold Matrix.kroneckerMap
    fun_prop
  exact (NormedSpace.map_exp f hf X).symm

/-- Exponentiation commutes with adjoining an identity on the left. -/
theorem exp_one_kronecker (Y : Matrix n n ℂ) :
    exp ((1 : Matrix m m ℂ) ⊗ₖ Y) = (1 : Matrix m m ℂ) ⊗ₖ exp Y := by
  let f : Matrix n n ℂ →+* Matrix (m × n) (m × n) ℂ := {
    toFun := fun X => (1 : Matrix m m ℂ) ⊗ₖ X
    map_one' := Matrix.one_kronecker_one
    map_mul' := fun X Z => by rw [← Matrix.mul_kronecker_mul]; simp
    map_zero' := Matrix.kronecker_zero _
    map_add' := fun X Z => Matrix.kronecker_add _ X Z }
  have hf : Continuous f := by
    change Continuous (fun X : Matrix n n ℂ =>
      Matrix.kroneckerMap (· * ·) (1 : Matrix m m ℂ) X)
    unfold Matrix.kroneckerMap
    fun_prop
  exact (NormedSpace.map_exp f hf Y).symm

/-- The tensor factors commute, so their sum exponentiates as their product. -/
theorem exp_kronecker_sum (X : Matrix m m ℂ) (Y : Matrix n n ℂ) :
    exp (X ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ Y) =
      exp X ⊗ₖ exp Y := by
  have hcomm : Commute (X ⊗ₖ (1 : Matrix n n ℂ)) ((1 : Matrix m m ℂ) ⊗ₖ Y) := by
    change _ = _
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp
  rw [Matrix.exp_add_of_commute _ _ hcomm, exp_kronecker_one,
    exp_one_kronecker, ← Matrix.mul_kronecker_mul]
  simp

/-- Entrywise complex conjugation commutes with the matrix exponential. -/
theorem exp_map_conjugate (X : Matrix n n ℂ) :
    exp (X.map (starRingEnd ℂ)) = (exp X).map (starRingEnd ℂ) := by
  change exp Xᴴᵀ = (exp X)ᴴᵀ
  rw [Matrix.exp_transpose, Matrix.exp_conjTranspose]

/-- Exponentiating the row-vectorized commutator gives the two-factor
conjugation representation. -/
theorem exp_rowCommutator (H : Matrix n n ℂ) (t : ℝ) :
    exp (t • (Complex.I • (H ⊗ₖ (1 : Matrix n n ℂ) -
      (1 : Matrix n n ℂ) ⊗ₖ H.map (starRingEnd ℂ)))) =
      hermitianUnitaryPath H t ⊗ₖ (hermitianUnitaryPath H t).map (starRingEnd ℂ) := by
  have hsplit : t • (Complex.I • (H ⊗ₖ (1 : Matrix n n ℂ) -
      (1 : Matrix n n ℂ) ⊗ₖ H.map (starRingEnd ℂ))) =
      (t • (Complex.I • H)) ⊗ₖ (1 : Matrix n n ℂ) +
        (1 : Matrix n n ℂ) ⊗ₖ (t • (Complex.I • H)).map (starRingEnd ℂ) := by
    ext ⟨a, b⟩ ⟨c, e⟩
    simp [Complex.real_smul, mul_sub]
    ring
  rw [hsplit, exp_kronecker_sum, exp_map_conjugate]
  rfl

end Matrix
