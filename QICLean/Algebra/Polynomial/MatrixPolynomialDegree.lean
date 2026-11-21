/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Matrix.Basic

/-!
# Degree bounds for matrices with polynomial entries

Entrywise degree ceilings add under multiplication and grow at most linearly
under powers. Evaluating a scalar polynomial of degree k multiplies an
entrywise ceiling d by at most k. The coefficient matrices need not commute.

These algebraic bounds support parameter interpolation in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333, and
`t:aisefficient`, lines 1373–1420. They assert no tensor or spectral estimate.
-/

open scoped BigOperators

namespace Matrix

/-- Entrywise degree ceilings add under matrix multiplication. This is
supporting algebra for polynomial parameter families associated with ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333. -/
theorem polynomial_natDegree_mul_apply_le
    {R row mid col : Type*} [Semiring R] [Fintype mid] {a b : ℕ}
    (A : Matrix row mid (Polynomial R)) (B : Matrix mid col (Polynomial R))
    (hA : ∀ i j, (A i j).natDegree ≤ a)
    (hB : ∀ i j, (B i j).natDegree ≤ b) (i : row) (j : col) :
    ((A * B) i j).natDegree ≤ a + b := by
  classical
  change (∑ k, A i k * B k j).natDegree ≤ a + b
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hA i k) (hB k j))

/-- Each entry of the r-th power of a matrix polynomial of entrywise
degree at most d has degree at most r*d. No commutation of its coefficient
matrices is required. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1311–1333. -/
theorem polynomial_natDegree_pow_apply_le
    {R n : Type*} [Semiring R] [Fintype n] [DecidableEq n] {d : ℕ}
    (A : Matrix n n (Polynomial R)) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (r : ℕ) (i j : n) : ((A ^ r) i j).natDegree ≤ r * d := by
  induction r generalizing i j with
  | zero =>
      by_cases hij : i = j <;> simp [hij]
  | succ r ih =>
      simpa only [pow_succ, Nat.succ_mul] using
        polynomial_natDegree_mul_apply_le (A ^ r) A ih hA i j

/-- Evaluating a scalar polynomial of degree k at a matrix polynomial of
entrywise degree d gives entrywise degree at most k*d. Supporting the
parameter interpolation for ALVV, arXiv:1602.08828v2,
`t:aisefficient`, lines 1373–1420. -/
theorem polynomial_natDegree_aeval_apply_le
    {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n] {d : ℕ}
    (A : Matrix n n (Polynomial R)) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (P : Polynomial R) (i j : n) :
    ((Polynomial.aeval A P) i j).natDegree ≤ P.natDegree * d := by
  classical
  simp only [Polynomial.aeval_eq_sum_range, Matrix.sum_apply, Matrix.smul_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r hr
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((polynomial_natDegree_pow_apply_le A hA r i j).trans
      (Nat.mul_le_mul_right d (Nat.le_of_lt_succ (Finset.mem_range.mp hr))))

end Matrix

section MatrixPolynomialInterpolation

/-!
# Interpolation of matrices with polynomial entries

A matrix whose entries have degree at most d is a scalar linear
combination of its values at d+1 fixed distinct nodes.
The interpolation weights do not depend on the matrix entries.

These elementary consequences of Mathlib's Lagrange interpolation support
a common family before the estimated soft center in ALVV,
arXiv:1602.08828v2, `t:aisefficient`, lines 1373–1420, and the polynomial
families of Proposition 5.7, lines 1311–1333. They assert no spectral,
matrix product or computational estimate.
-/

open scoped BigOperators

namespace Matrix

/-- A matrix polynomial of entrywise degree at most d is recovered from
its values at the fixed nodes 0 through d. The interpolation weights are
common to all entries. This is an algebraic auxiliary for the uniform
soft-center construction associated with ALVV, arXiv:1602.08828v2,
`t:aisefficient`, lines 1373–1420. -/
theorem map_polynomial_eval_eq_sum_lagrange
    {K row col : Type*} [Field K] [CharZero K] {d : ℕ}
    (A : Matrix row col (Polynomial K))
    (hdegree : ∀ i j, (A i j).natDegree ≤ d) (z : K) :
    A.map (Polynomial.eval z) =
      ∑ r : Fin (d + 1),
        (Polynomial.eval z
          (Lagrange.basis Finset.univ (fun s : Fin (d + 1) ↦ (s.val : K)) r)) •
          A.map (Polynomial.eval (r.val : K)) := by
  classical
  ext i j
  have hnodes : Function.Injective (fun r : Fin (d + 1) ↦ (r.val : K)) :=
    fun _ _ h ↦ Fin.val_injective (Nat.cast_injective h)
  have hdeg : (A i j).degree ≤ (d : WithBot ℕ) :=
    Polynomial.degree_le_of_natDegree_le (hdegree i j)
  have hdeg_lt : (A i j).degree <
      ((Finset.univ : Finset (Fin (d + 1))).card : WithBot ℕ) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      lt_of_le_of_lt hdeg (show (d : WithBot ℕ) < ↑(d + 1) by
        exact_mod_cast Nat.lt_succ_self d)
  have hinterp := Lagrange.eq_interpolate (s := Finset.univ) (f := A i j)
    hnodes.injOn hdeg_lt
  simpa only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, mul_comm] using
      congrArg (Polynomial.eval z) hinterp

end Matrix

end MatrixPolynomialInterpolation
