/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixPolynomialDegree
import QICLean.Algebra.MatrixPolynomialInterpolation

/-!
# Interpolating a polynomial of a polynomial matrix parameter

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

open scoped BigOperators

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
