/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Matrix.Basic

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
