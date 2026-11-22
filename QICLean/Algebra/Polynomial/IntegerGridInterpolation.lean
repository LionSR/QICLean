/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Finite interpolation on integer product grids

Let O be a finite coordinate type and let K be a natural number. Evaluation
of the monomials with exponent vectors in O → Fin (K + 1) on the grid
{0, ..., K}^O has a specified left inverse. Its entries are products of rows
of the univariate inverse Vandermonde matrix.

The same scalar weights recover coefficients in any complex module.
The formulas include cutoff zero and an empty coordinate type.

## References

* AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 626–644.
* ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333.
-/

open scoped BigOperators

namespace FiniteScalarInterpolation

/-- The prescribed interpolation nodes are the integers from zero through K. -/
def integerNode (K : ℕ) (r : Fin (K + 1)) : ℂ := (r.val : ℂ)

/-- Rows of the inverse Vandermonde matrix are scalar coefficient-recovery
weights at the prescribed integer nodes. This is an auxiliary explicit
choice supporting finite interpolation in AKLV, arXiv:1301.1162v1,
Lemma l:agsp, lines 626–644, and ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
noncomputable def integerRecovery (K : ℕ) : Matrix (Fin (K + 1)) (Fin (K + 1)) ℂ :=
  (Matrix.vandermonde (integerNode K))⁻¹

/-- The specified integer nodes and inverse Vandermonde weights recover each
monomial coefficient, including cutoff zero. No determinant or inverse
hypothesis is required. This is the univariate finite-interpolation identity
supporting AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 626–644, and ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem integerRecovery_sum (K : ℕ) (alpha beta : Fin (K + 1)) :
    (∑ r : Fin (K + 1), integerRecovery K alpha r * (integerNode K r) ^ beta.val) =
      if alpha = beta then 1 else 0 := by
  have hnode : Function.Injective (integerNode K) := by
    intro r s hrs
    exact Fin.val_injective (Nat.cast_injective (R := ℂ) hrs)
  have hdet : (Matrix.vandermonde (integerNode K)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hnode
  have hinv := Matrix.nonsing_inv_mul (Matrix.vandermonde (integerNode K))
    (isUnit_iff_ne_zero.mpr hdet)
  have hentry := congrArg
    (fun A : Matrix (Fin (K + 1)) (Fin (K + 1)) ℂ ↦ A alpha beta) hinv
  simpa only [integerRecovery, Matrix.mul_apply, Matrix.vandermonde_apply,
    Matrix.one_apply] using hentry

open Classical in
/-- A scalar left-inverse identity tensorizes over an arbitrary finite set of coordinates. -/
private theorem tensor_recovery_sum
    {O J : Type*} [Fintype O] [Fintype J] [DecidableEq J]
    (C A : J → J → ℂ)
    (hCA : ∀ alpha beta, (∑ r, C alpha r * A r beta) =
      if alpha = beta then 1 else 0)
    (alpha beta : O → J) :
    (∑ g : O → J, (∏ a, C (alpha a) (g a)) * (∏ a, A (g a) (beta a))) =
      if alpha = beta then 1 else 0 := by
  classical
  calc
    (∑ g : O → J, (∏ a, C (alpha a) (g a)) * (∏ a, A (g a) (beta a))) =
        ∑ g : O → J, ∏ a, C (alpha a) (g a) * A (g a) (beta a) := by
      simp only [Finset.prod_mul_distrib]
    _ = ∏ a, ∑ r : J, C (alpha a) r * A r (beta a) :=
      (Fintype.prod_sum (fun a (r : J) ↦ C (alpha a) r * A r (beta a))).symm
    _ = ∏ a, (if alpha a = beta a then (1 : ℂ) else 0) := by simp_rw [hCA]
    _ = if alpha = beta then 1 else 0 := by
      simp only [Fintype.prod_boole, ← funext_iff]

/-- Evaluate bounded monomials on the product of the integer nodes from zero through K. -/
noncomputable def integerEvaluationGrid (O : Type*) [Fintype O] (K : ℕ) :
    Matrix (O → Fin (K + 1)) (O → Fin (K + 1)) ℂ :=
  fun g beta ↦ ∏ a, (integerNode K (g a)) ^ (beta a).val

/-- Recovery weights on the integer product grid are products of the univariate weights. -/
noncomputable def integerRecoveryGrid (O : Type*) [Fintype O] (K : ℕ) :
    Matrix (O → Fin (K + 1)) (O → Fin (K + 1)) ℂ :=
  fun alpha g ↦ ∏ a, integerRecovery K (alpha a) (g a)

open Classical in
/-- The specified product-grid recovery matrix is a left inverse to evaluation,
including K=0 and an empty coordinate type. Supporting AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 626–644, and ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem integerRecoveryGrid_mul_integerEvaluationGrid
    (O : Type*) [Fintype O] (K : ℕ) :
    integerRecoveryGrid O K * integerEvaluationGrid O K = 1 := by
  classical
  ext alpha beta
  simpa only [integerRecoveryGrid, integerEvaluationGrid, Matrix.mul_apply,
    Matrix.one_apply] using
    (tensor_recovery_sum (integerRecovery K)
      (fun r b : Fin (K + 1) ↦ (integerNode K r) ^ b.val)
      (integerRecovery_sum K) alpha beta)

open Classical in
/-- The specified integer product grid recovers every coefficient in any
complex module. Points and scalar recovery weights are fixed by O and K,
before the coefficient function. No independence or inverse hypothesis is
needed. This is finite scalar interpolation supporting AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 626–644, and ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem integerRecoveryGrid_smul
    (O : Type*) [Fintype O] (K : ℕ)
    {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (f : (O → Fin (K + 1)) → M) (alpha : O → Fin (K + 1)) :
    (∑ g : O → Fin (K + 1), integerRecoveryGrid O K alpha g •
      (∑ beta : O → Fin (K + 1), integerEvaluationGrid O K g beta • f beta)) =
        f alpha := by
  classical
  have hCA (beta : O → Fin (K + 1)) :
      (∑ g : O → Fin (K + 1),
        integerRecoveryGrid O K alpha g * integerEvaluationGrid O K g beta) =
          if alpha = beta then 1 else 0 := by
    have h := congrArg
      (fun A : Matrix (O → Fin (K + 1)) (O → Fin (K + 1)) ℂ ↦ A alpha beta)
      (integerRecoveryGrid_mul_integerEvaluationGrid O K)
    simpa only [Matrix.mul_apply, Matrix.one_apply] using h
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hCA]
  simp [ite_smul]

end FiniteScalarInterpolation
