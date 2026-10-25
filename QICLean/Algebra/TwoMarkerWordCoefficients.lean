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
# Two distinguished frequencies in the original coefficient family

The ordinary scalar variables omit two distinct labels of a finite alphabet.
Both marker coefficients are expressed through the full-frequency coefficients
of the original operator family, with every ordered-word multiplicity retained.

Source: AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 604–617 and 626–635;
ALVV, arXiv:1602.08828v2, prop:Cheby-AGSP-eff, lines 1324 and 1332.
-/

open scoped BigOperators

namespace Polynomial

private theorem nested_monomial_list
    {ι 𝓡 : Type*} [Semiring 𝓡] [Algebra ℂ 𝓡]
    (H : ι → 𝓡) (weight : ι → ℂ) (dx dy : ι → ℕ) (l : List ι) :
    (l.map (fun a ↦
      (monomial (dx a) (monomial (dy a) (weight a • H a)) :
        Polynomial (Polynomial 𝓡)))).prod =
      monomial ((l.map dx).sum)
        (monomial ((l.map dy).sum) ((l.map weight).prod • (l.map H).prod)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih,
      monomial_mul_monomial, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_comm]

private theorem scalar_weight_of_word
    {ι : Type*} [Fintype ι] (weight : ι → ℂ)
    {k : ℕ} (w : Fin k → ι) :
    (List.ofFn (fun p ↦ weight (w p))).prod =
      ∏ a, weight a ^ WordMultiplicity.countsFinsupp w a := by
  rw [List.prod_ofFn]
  have hp := Finsupp.prod_finsetSum_index (s := Finset.univ)
    (g := fun p : Fin k ↦ Finsupp.single (w p) (1 : ℕ))
    (h := fun a n ↦ weight a ^ n)
    (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)
  have hq := Finsupp.prod_fintype
    (∑ p : Fin k, Finsupp.single (w p) (1 : ℕ))
    (fun a n ↦ weight a ^ n) (fun _ ↦ pow_zero _)
  simpa only [Finsupp.prod_single_index, pow_zero, pow_one,
    WordMultiplicity.countsFinsupp] using hp.trans hq


open Classical in
/-- Two distinguished-letter coefficients, retaining the original full
frequency index and all ordered-word multiplicities. This is an auxiliary
algebraic identity for the cited generating-polynomial argument.
-/
theorem coeff_coeff_pow_two_markers_eq_sum_full_counts
    {ι 𝓡 : Type*} [Fintype ι] [Semiring 𝓡] [Algebra ℂ 𝓡]
    (H : ι → 𝓡) (u v : ι) (huv : u ≠ v)
    (z : ι → ℂ) (k i j : ℕ) :
    let O := ((Finset.univ : Finset ι).erase u).erase v
    let E := Finset.piAntidiag (Finset.univ : Finset ι) k
    let D := ∑ a ∈ O, z a • H a
    let F : Polynomial (Polynomial 𝓡) :=
      C (C D + C (H v) * X) + C (C (H u)) * X
    let coefficient : (ι → ℕ) → 𝓡 := fun a ↦
      ∑ w ∈ (Finset.univ : Finset (Fin k → ι)).filter
          (fun w ↦ (WordMultiplicity.countsFinsupp w : ι → ℕ) = a),
        (List.ofFn (fun p ↦ H (w p))).prod
    ((F ^ k).coeff i).coeff j =
      ∑ a ∈ E with a u = i ∧ a v = j,
        (∏ b ∈ O, z b ^ a b) • coefficient a := by
  classical
  intro O E D F coefficient
  let weight : ι → ℂ := fun a ↦ if a ∈ O then z a else 1
  let P : ι → Polynomial (Polynomial 𝓡) := fun a ↦
    monomial (if a = u then 1 else 0)
      (monomial (if a = v then 1 else 0) (weight a • H a))
  have hordinary : (∑ a ∈ O, P a) = C (C D) := by
    calc
      _ = ∑ a ∈ O, C (C (z a • H a)) := by
        refine Finset.sum_congr rfl fun a ha ↦ ?_
        have hav : a ≠ v := (Finset.mem_erase.mp ha).1
        have hau : a ≠ u :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
        simp only [P, weight, ite_eq_right hau, ite_eq_right hav, ite_eq_left ha,
          monomial_zero_left]
      _ = C (C D) := by simp only [D, map_sum]
  have hbase : (∑ a, P a) = F := by
    rw [← Finset.sum_erase_add Finset.univ P (Finset.mem_univ u),
      ← Finset.sum_erase_add (Finset.univ.erase u) P
        (by simp only [Finset.mem_erase, Finset.mem_univ, and_true]; exact huv.symm)]
    rw [hordinary]
    simp [P, weight, O, F, huv, huv.symm,
      ← C_mul_X_pow_eq_monomial, C_add, add_assoc]
  have hweight (a : ι → ℕ) :
      (∏ b, weight b ^ a b) = ∏ b ∈ O, z b ^ a b := by
    calc
      _ = ∏ b, if b ∈ O then z b ^ a b else 1 := by
        refine Finset.prod_congr rfl fun b _ ↦ ?_
        by_cases hb : b ∈ O <;> simp only [weight, hb, ite_true, ite_false, one_pow]
      _ = _ := Finset.prod_ite_mem_eq O (fun b ↦ z b ^ a b)
  have hdegree (w : Fin k → ι) (b : ι) :
      (List.ofFn (fun p ↦ if w p = b then 1 else 0)).sum =
        WordMultiplicity.countsFinsupp w b := by
    simp only [Fin.sum_ofFn, WordMultiplicity.countsFinsupp,
      Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hword (w : Fin k → ι) :
      (List.ofFn (fun p ↦ P (w p))).prod =
        monomial (WordMultiplicity.countsFinsupp w u)
          (monomial (WordMultiplicity.countsFinsupp w v)
            ((∏ b ∈ O, z b ^ WordMultiplicity.countsFinsupp w b) •
              (List.ofFn (fun p ↦ H (w p))).prod)) := by
    have hm := nested_monomial_list H weight
      (fun a ↦ if a = u then 1 else 0)
      (fun a ↦ if a = v then 1 else 0) (List.ofFn w)
    simpa only [P, List.map_ofFn, Function.comp_def, hdegree,
      scalar_weight_of_word, hweight] using hm
  let W : Finset (Fin k → ι) := Finset.univ.filter
    (fun w ↦ WordMultiplicity.countsFinsupp w u = i ∧
      WordMultiplicity.countsFinsupp w v = j)
  have hraw : ((F ^ k).coeff i).coeff j =
      ∑ w ∈ W,
        (∏ b ∈ O, z b ^ WordMultiplicity.countsFinsupp w b) •
          (List.ofFn (fun p ↦ H (w p))).prod := by
    calc
      _ = ∑ w : Fin k → ι, (((List.ofFn (fun p ↦ P (w p))).prod).coeff i).coeff j := by
        rw [← hbase, Fintype.sum_pow_eq_sum_ordered_words]
        simp only [finsetSum_coeff]
      _ = _ := by
        simp only [W, Finset.sum_filter]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        rw [hword]
        by_cases hi : WordMultiplicity.countsFinsupp w u = i <;>
          by_cases hj : WordMultiplicity.countsFinsupp w v = j <;>
            simp [coeff_monomial, hi, hj]
  have hmap : ∀ w ∈ W,
      (WordMultiplicity.countsFinsupp w : ι → ℕ) ∈
        E.filter (fun a ↦ a u = i ∧ a v = j) := by
    intro w hw
    refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hw).2⟩
    exact Finset.mem_piAntidiag.mpr
      ⟨WordMultiplicity.sum_counts w, fun _ _ ↦ Finset.mem_univ _⟩
  calc
    ((F ^ k).coeff i).coeff j =
        ∑ a ∈ E with a u = i ∧ a v = j,
          ∑ w ∈ W with (WordMultiplicity.countsFinsupp w : ι → ℕ) = a,
            (∏ b ∈ O, z b ^ WordMultiplicity.countsFinsupp w b) •
              (List.ofFn (fun p ↦ H (w p))).prod := by
      exact hraw.trans (Finset.sum_fiberwise_of_maps_to hmap
        (fun w ↦ (∏ b ∈ O, z b ^ WordMultiplicity.countsFinsupp w b) •
          (List.ofFn (fun p ↦ H (w p))).prod)).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun a ha ↦ ?_
      have hf : W.filter
          (fun w ↦ (WordMultiplicity.countsFinsupp w : ι → ℕ) = a) =
          Finset.univ.filter
            (fun w : Fin k → ι ↦ (WordMultiplicity.countsFinsupp w : ι → ℕ) = a) := by
        ext w
        simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h ↦ h.2
        · intro hw
          refine ⟨?_, hw⟩
          simpa only [hw] using (Finset.mem_filter.mp ha).2
      simp only [coefficient, Finset.smul_sum]
      rw [hf]
      refine Finset.sum_congr rfl fun w hw ↦ ?_
      simp only [(Finset.mem_filter.mp hw).2]

end Polynomial
