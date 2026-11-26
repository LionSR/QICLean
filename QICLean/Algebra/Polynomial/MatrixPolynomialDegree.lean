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

It also contains the following results.

* `Matrix.aeval_polynomial_parameter_eq_sum_lagrange`: interpolating a polynomial of a polynomial
  matrix parameter.
-/

open scoped BigOperators

section MatrixPolynomialDegree

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

end MatrixPolynomialDegree

section MatrixPolynomialParameter

/-!
## Interpolating a polynomial of a polynomial matrix parameter

For fixed coefficient matrices, a matrix polynomial of degree at most m
can be substituted into a scalar polynomial of degree at most k. The
result is recovered from the fixed integer parameter values 0 through m*k.
No commutation of the coefficient matrices is required.

This is supporting algebra for a common family before an estimated soft
center in ALVV, arXiv:1602.08828v2, `t:aisefficient`, lines 1373–1420,
and Proposition 5.7, lines 1311–1333. The matrix coefficients and the
polynomial degree bounds are the data of this algebraic statement;
no spectral or tensor decomposition is supplied as a hypothesis.
-/

namespace Matrix

/-- The fixed m*k+1 integer nodes recover a polynomial of an actual matrix
polynomial parameter. Its entrywise degree is derived from the coefficient
matrices and the degree of P. Supporting ALVV, arXiv:1602.08828v2,
Proposition 5.7 and `t:aisefficient`, lines 1311–1420. -/
theorem aeval_polynomial_parameter_eq_sum_lagrange
    {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n] {m k : ℕ}
    (B0 : Matrix n n K) (B : Fin (m + 1) → Matrix n n K)
    (P : Polynomial K) (hP : P.natDegree ≤ k) (z : K) :
    Polynomial.aeval (B0 + ∑ a : Fin (m + 1), z ^ a.val • B a) P =
      ∑ r : Fin (m * k + 1),
        Polynomial.eval z
            (Lagrange.basis Finset.univ (fun s : Fin (m * k + 1) ↦ (s.val : K)) r) •
          Polynomial.aeval (B0 + ∑ a : Fin (m + 1), (r.val : K) ^ a.val • B a) P := by
  classical
  let A : Matrix n n (Polynomial K) := Matrix.of fun i j ↦
    Polynomial.C (B0 i j) + ∑ a : Fin (m + 1), Polynomial.monomial a.val (B a i j)
  have hA (i j : n) : (A i j).natDegree ≤ m := by
    dsimp only [A, Matrix.of_apply]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun a _ ↦
        (Polynomial.natDegree_monomial_le (B a i j)).trans (Nat.le_of_lt_succ a.isLt)
  have hfilter (i j : n) : ((Polynomial.aeval A P) i j).natDegree ≤ m * k :=
    (polynomial_natDegree_aeval_apply_le A hA P i j).trans
      ((Nat.mul_le_mul_right m hP).trans_eq (Nat.mul_comm k m))
  have hAeval (u : K) : A.map (Polynomial.eval u) =
      B0 + ∑ a : Fin (m + 1), u ^ a.val • B a := by
    ext i j
    simp only [A, Matrix.of_apply, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_finsetSum, Polynomial.eval_monomial, smul_eq_mul, mul_comm]
  have htransport (u : K) :
      (Polynomial.aeval A P).map (Polynomial.eval u) =
        Polynomial.aeval (A.map (Polynomial.eval u)) P := by
    simpa only [AlgHom.mapMatrix_apply, Polynomial.coe_aeval_eq_eval] using
      (Polynomial.aeval_algHom_apply
        ((Polynomial.aeval u : Polynomial K →ₐ[K] K).mapMatrix (m := n)) A P).symm
  simpa only [htransport, hAeval] using
    map_polynomial_eval_eq_sum_lagrange (Polynomial.aeval A P) hfilter z

end Matrix

end MatrixPolynomialParameter
