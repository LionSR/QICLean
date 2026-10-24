/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.FiniteSumPowers
import QICLean.Algebra.WordMultiplicity
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Polynomial coefficients grouped by ordered-word frequencies

A central polynomial variable records occurrences of a distinguished operator.
Complex scalar weights record the ordinary letters. Expanding a power into
ordered words and collecting their frequencies identifies its actual coefficient
with the corresponding monomial family. The operator factors remain in their
original order throughout the calculation.

The ordinary alphabet may be empty, and the exponent may be zero. Operator
coefficients may coincide or vanish. Selected sums of the coefficient operators
and local operator Schmidt-rank bounds are separate statements.

Source: AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 604–617 and 626–635.
-/

open scoped BigOperators

namespace Polynomial

private theorem list_monomial_factor
    {ι R : Type*} [Semiring R] [Algebra ℂ R]
    (H : ι → R) (T : R) (z : ι → ℂ) (L : List (Option ι)) :
    (L.map (fun a ↦ match a with
      | none => Polynomial.C T * Polynomial.X
      | some j => Polynomial.C (z j • H j))).prod =
      Polynomial.monomial
        ((L.map (fun a ↦ if a = none then 1 else 0)).sum)
        ((L.map (Option.elim' (1 : ℂ) z)).prod •
          (L.map (Option.elim' T H)).prod) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]
    cases a <;> simp only [Option.elim', reduceIte, Option.some_ne_none,
      Polynomial.X, ← Polynomial.monomial_zero_left,
      Polynomial.monomial_mul_monomial, zero_add, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

private theorem word_weight {ι : Type*} [Fintype ι] (z : ι → ℂ)
    {d : ℕ} (w : Fin d → Option ι) :
    (List.ofFn (fun p ↦ Option.elim' (1 : ℂ) z (w p))).prod =
      ∏ j, z j ^ WordMultiplicity.countsFinsupp w (some j) := by
  calc
    _ = ∏ p, Option.elim' (1 : ℂ) z (w p) := List.prod_ofFn
    _ = (WordMultiplicity.countsFinsupp w).prod
        (fun a n ↦ (Option.elim' (1 : ℂ) z a) ^ n) := by
      simpa only [WordMultiplicity.countsFinsupp, Finsupp.prod_single_index,
        pow_zero, pow_one] using
        (Finsupp.prod_finsetSum_index (s := Finset.univ)
          (g := fun p ↦ Finsupp.single (w p) 1)
          (h := fun a n ↦ (Option.elim' (1 : ℂ) z a) ^ n)
          (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _))
    _ = _ := by rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]; simp

private theorem word_polynomial {ι R : Type*} [Fintype ι] [Semiring R] [Algebra ℂ R]
    (H : ι → R) (T : R) (z : ι → ℂ) {d : ℕ} (w : Fin d → Option ι) :
    (List.ofFn (fun p ↦ match w p with
      | none => Polynomial.C T * Polynomial.X
      | some j => Polynomial.C (z j • H j))).prod =
      Polynomial.monomial (WordMultiplicity.countsFinsupp w none)
        ((∏ j, z j ^ WordMultiplicity.countsFinsupp w (some j)) •
          (List.ofFn (fun p ↦ Option.elim' T H (w p))).prod) := by
  have hd : (List.ofFn (fun p ↦ if w p = none then 1 else 0)).sum =
      WordMultiplicity.countsFinsupp w none := by
    simp [Fin.sum_ofFn, WordMultiplicity.countsFinsupp, Finsupp.finsetSum_apply,
      Finsupp.single_apply]
  simpa only [List.map_ofFn, Function.comp_def, hd, word_weight] using
    list_monomial_factor H T z (List.ofFn w)

open Classical in
/-- Fixed distinguished-letter coefficient, AKLV arXiv:1301.1162v1,
Lemma l:agsp, lines 604–617 and 626–635. No operator commutation is assumed. -/
theorem coeff_pow_sum_smul_add_C_mul_X_eq_sum_counts
    {ι R : Type*} [Fintype ι] [Semiring R] [Algebra ℂ R]
    (H : ι → R) (T : R) (z : ι → ℂ) (m k : ℕ) :
    let E := Finset.piAntidiag (Finset.univ : Finset ι) m
    let f : E → R := fun a ↦
      ∑ w ∈ (Finset.univ : Finset (Fin (m + k) → Option ι)).filter
          (fun w ↦ WordMultiplicity.countsFinsupp w none = k ∧
            ∀ j : ι, WordMultiplicity.countsFinsupp w (some j) = a.val j),
        (List.ofFn (fun p ↦ match w p with
          | none => T
          | some j => H j)).prod
    ((Polynomial.C (∑ j, z j • H j) + Polynomial.C T * Polynomial.X) ^
      (m + k)).coeff k =
      ∑ a : E, (∏ j, z j ^ a.val j) • f a := by
  have hbase : Polynomial.C (∑ j, z j • H j) + Polynomial.C T * Polynomial.X =
      ∑ a : Option ι, match a with
        | none => Polynomial.C T * Polynomial.X
        | some j => Polynomial.C (z j • H j) := by
    simp [Fintype.sum_option, add_comm]
  simp_rw [hbase, Fintype.sum_pow_eq_sum_ordered_words,
    Polynomial.finsetSum_coeff, word_polynomial, Polynomial.coeff_monomial]
  have hmem (w : Fin (m + k) → Option ι)
      (hw : WordMultiplicity.countsFinsupp w none = k) :
      (fun j : ι ↦ WordMultiplicity.countsFinsupp w (some j)) ∈
        Finset.piAntidiag Finset.univ m :=
    Finset.mem_piAntidiag.mpr ⟨by
      have hs := WordMultiplicity.sum_counts w
      simp only [Fintype.sum_option, hw] at hs
      omega, fun _ _ ↦ Finset.mem_univ _⟩
  rw [← Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun w : Fin (m + k) → Option ι ↦
      WordMultiplicity.countsFinsupp w none = k))
    (t := Finset.piAntidiag Finset.univ m)
    (g := fun (w : Fin (m + k) → Option ι) (j : ι) ↦
      WordMultiplicity.countsFinsupp w (some j))
    (fun w hw ↦ hmem w (Finset.mem_filter.mp hw).2)]
  rw [← Finset.sum_coe_sort (Finset.piAntidiag Finset.univ m)]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  simp only [Finset.filter_filter, funext_iff, Finset.smul_sum]
  exact Finset.sum_congr rfl fun w hw ↦ by
    simp only [(Finset.mem_filter.mp hw).2.2]
    exact congrArg (fun v : Fin (m + k) → R ↦
      (∏ j, z j ^ a.val j) • (List.ofFn v).prod)
      (funext fun p ↦ by cases w p <;> rfl)

end Polynomial
