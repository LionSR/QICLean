/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.List.OfFn

/-!
# Ordered gap sums for a polynomial coefficient

For semiring elements `D` and `T`, the coefficient of degree `k` in
`(C D + C T * X)^(m + k)` is the sum of the ordered products
`D^n₀ * T * D^n₁ * ... * T * D^nₖ` over nonnegative gap lengths of total `m`.
Zero-length gaps and zero exponents are included.

The gap sums and polynomial coefficients satisfy the same left-multiplication
recurrence and boundary identities. A double induction proves the equality.
The final sum uses the existing finite set of antidiagonal tuples.

This is supporting algebra for AKLV, arXiv:1301.1162v1, Lemma l:agsp,
lines 646–653, with coefficients defined at lines 604–617.
The subsequent expansion of each gap into commuting contributions retains
its binomial multiplicities.
-/

open scoped BigOperators

private def gapWord {R : Type*} [Semiring R] (D T : R) (k : ℕ) (n : Fin (k + 1) → ℕ) : R :=
  (List.ofFn (fun j : Fin k ↦ D ^ n j.castSucc * T)).prod * D ^ n (Fin.last k)

private theorem gapWord_cons {R : Type*} [Semiring R] (D T : R) (k a : ℕ)
    (n : Fin (k + 1) → ℕ) :
    gapWord D T (k + 1) (Fin.cons a n) = D ^ a * T * gapWord D T k n := by
  simp only [gapWord, List.ofFn_succ, Fin.castSucc_zero, Fin.cons_zero,
    Fin.castSucc_succ, Fin.cons_succ, Fin.cons_last, List.prod_cons, mul_assoc]

private def gapSum {R : Type*} [Semiring R] (D T : R) (k m : ℕ) : R :=
  ((List.Nat.antidiagonalTuple (k + 1) m).map (gapWord D T k)).sum

private theorem sum_map_flatMap {α β R : Type*} [AddCommMonoid R]
    (l : List α) (f : α → List β) (g : β → R) :
    ((l.flatMap f).map g).sum = (l.map (fun a ↦ ((f a).map g).sum)).sum := by
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
  rfl

private theorem gapSum_head {R : Type*} [Semiring R] (D T : R) (k m : ℕ) :
    gapSum D T (k + 1) m =
      ((List.Nat.antidiagonal m).map (fun p ↦ D ^ p.1 * T * gapSum D T k p.2)).sum := by
  change ((List.Nat.antidiagonalTuple (k + 2) m).map (gapWord D T (k + 1))).sum = _
  rw [List.Nat.antidiagonalTuple, sum_map_flatMap]
  simp only [List.map_map, Function.comp_def, gapWord_cons, List.sum_map_mul_left, gapSum]

private theorem gapSum_succ_succ {R : Type*} [Semiring R] (D T : R) (k m : ℕ) :
    gapSum D T (k + 1) (m + 1) = D * gapSum D T (k + 1) m + T * gapSum D T k (m + 1) := by
  rw [gapSum_head, List.Nat.antidiagonal_succ]
  simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
    Prod.map_fst, Prod.map_snd, id_eq, pow_zero, one_mul, pow_succ', mul_assoc,
    List.sum_map_mul_left]
  simpa only [gapSum_head, mul_assoc] using
    (add_comm (T * gapSum D T k (m + 1)) (D * gapSum D T (k + 1) m))

private theorem gapSum_zero_left {R : Type*} [Semiring R] (D T : R) (m : ℕ) :
    gapSum D T 0 m = D ^ m := by
  simp [gapSum, gapWord]

private theorem gapSum_zero_right {R : Type*} [Semiring R] (D T : R) (k : ℕ) :
    gapSum D T k 0 = T ^ k := by
  induction k with
  | zero => simp [gapSum_zero_left]
  | succ k ih => simp [gapSum_head, ih, pow_succ']

private theorem gapCoeff_succ_succ {R : Type*} [Semiring R] (D T : R) (m k : ℕ) :
    ((Polynomial.C D + Polynomial.C T * Polynomial.X) ^ ((m + 1) + (k + 1))).coeff (k + 1) =
      D * ((Polynomial.C D + Polynomial.C T * Polynomial.X) ^ (m + (k + 1))).coeff (k + 1) +
      T * ((Polynomial.C D + Polynomial.C T * Polynomial.X) ^ ((m + 1) + k)).coeff k := by
  rw [Nat.add_right_comm m 1 (k + 1), pow_succ', add_mul,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul]
  simp only [Nat.add_assoc, Nat.add_comm 1 k]

private theorem gapCoeff_zero_left {R : Type*} [Semiring R] (D T : R) (k : ℕ) :
    ((Polynomial.C D + Polynomial.C T * Polynomial.X) ^ k).coeff k = T ^ k := by
  have hn : (Polynomial.C D + Polynomial.C T * Polynomial.X).natDegree ≤ 1 := by
    simpa only [Polynomial.natDegree_C_add] using
      (Polynomial.natDegree_C_mul_le T Polynomial.X).trans Polynomial.natDegree_X_le
  simpa using (Polynomial.coeff_pow_of_natDegree_le (m := k) hn)

private theorem gapCoeff_zero_right {R : Type*} [Semiring R] (D T : R) (m : ℕ) :
    ((Polynomial.C D + Polynomial.C T * Polynomial.X) ^ m).coeff 0 = D ^ m := by
  induction m with
  | zero => simp
  | succ m ih => simp [pow_succ, ih]

private theorem gapCoeff_eq_gapSum {R : Type*} [Semiring R] (D T : R) (m k : ℕ) :
    ((Polynomial.C D + Polynomial.C T * Polynomial.X) ^ (m + k)).coeff k = gapSum D T k m := by
  induction m generalizing k with
  | zero => simpa only [Nat.zero_add, gapSum_zero_right] using gapCoeff_zero_left D T k
  | succ m ih =>
    induction k with
    | zero => simp [gapCoeff_zero_right, gapSum_zero_left]
    | succ k ikh =>
      rw [gapCoeff_succ_succ, ih, ikh, gapSum_succ_succ]

/-- Ordered gap collection for the fixed distinguished-letter coefficient.
Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma l:agsp,
lines 646–653, with coefficients defined at lines 604–617. -/
theorem Polynomial.coeff_pow_C_add_C_mul_X_eq_sum_gaps
    {R : Type*} [Semiring R] (D T : R) (m k : ℕ) :
    ((Polynomial.C D + Polynomial.C T * Polynomial.X) ^ (m + k)).coeff k =
      ∑ n ∈ Finset.Nat.antidiagonalTuple (k + 1) m,
        (List.ofFn (fun j : Fin k ↦ D ^ n j.castSucc * T)).prod *
          D ^ n (Fin.last k) := by
  have hsets : Finset.Nat.antidiagonalTuple (k + 1) m =
      (List.Nat.antidiagonalTuple (k + 1) m).toFinset := by
    ext n
    simp only [Finset.Nat.mem_antidiagonalTuple, List.mem_toFinset,
      List.Nat.mem_antidiagonalTuple]
  rw [hsets, List.sum_toFinset _ (List.Nat.nodup_antidiagonalTuple (k + 1) m)]
  exact gapCoeff_eq_gapSum D T m k
