/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Sym.Card

/-!
# The span of commuting-gap forms

A distinguished-letter coefficient belongs to the span of ordered products whose
intervening gaps are powers of two commuting elements. Multiplicities are retained
by an additive-closure recurrence; no commutation with the distinguished element
is assumed.

Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 604–617 and
646–653. The number of indexed forms is computed by stars and bars.
The exact weighted coefficient identity and operator Schmidt-rank estimates
are separate assertions.
-/

open scoped BigOperators

private def commutingGapForm {R : Type*} [Semiring R] (A B T : R) :
    (k : ℕ) → (Fin (k + 1) → ℕ × ℕ) → R
  | 0, d => A ^ (d 0).1 * B ^ (d 0).2
  | k + 1, d => A ^ (d 0).1 * B ^ (d 0).2 * T *
      commutingGapForm A B T k (fun j ↦ d j.succ)

private def bumpFirst (b : Bool) {k : ℕ} (d : Fin (k + 1) → ℕ × ℕ) :
    Fin (k + 1) → ℕ × ℕ :=
  Fin.cons (if b then ((d 0).1, (d 0).2 + 1) else ((d 0).1 + 1, (d 0).2))
    (fun j ↦ d j.succ)

private theorem commutingGapForm_mul_left_B {R : Type*} [Semiring R]
    (A B T : R) (hAB : Commute A B) (k : ℕ) (d : Fin (k + 1) → ℕ × ℕ) :
    B * commutingGapForm A B T k d = commutingGapForm A B T k (bumpFirst true d) := by
  cases k <;> simp only [commutingGapForm, bumpFirst, ↓reduceIte,
    Fin.cons_zero, Fin.cons_succ, pow_succ', mul_assoc]
  all_goals exact (hAB.symm.pow_right (d 0).1).left_comm _

private theorem sum_bumpFirst (b : Bool) (k : ℕ) (d : Fin (k + 1) → ℕ × ℕ) :
    (Finset.univ.sum (fun j : Fin (k + 1) ↦ ((bumpFirst b d) j).1 + ((bumpFirst b d) j).2)) =
      (Finset.univ.sum (fun j : Fin (k + 1) ↦ (d j).1 + (d j).2)) + 1 := by
  simp only [Fin.sum_univ_succ, bumpFirst, Fin.cons_zero, Fin.cons_succ]
  cases b <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem commutingGapForm_mul_left_A {R : Type*} [Semiring R]
    (A B T : R) (k : ℕ) (d : Fin (k + 1) → ℕ × ℕ) :
    A * commutingGapForm A B T k d = commutingGapForm A B T k (bumpFirst false d) := by
  cases k <;> simp [commutingGapForm, bumpFirst, pow_succ', mul_assoc]

private def gapTotal {k : ℕ} (d : Fin (k + 1) → ℕ × ℕ) : ℕ :=
  Finset.univ.sum (fun j ↦ (d j).1 + (d j).2)

private def commutingGapClosure {R : Type*} [Semiring R] (A B T : R) (m k : ℕ) :
    AddSubmonoid R :=
  AddSubmonoid.closure {x | ∃ d : Fin (k + 1) → ℕ × ℕ,
    gapTotal d = m ∧ commutingGapForm A B T k d = x}

private theorem mul_mem_addClosure {R : Type*} [Semiring R] {s t : Set R} (r : R)
    (hf : ∀ x ∈ s, r * x ∈ AddSubmonoid.closure t) {x : R}
    (hx : x ∈ AddSubmonoid.closure s) : r * x ∈ AddSubmonoid.closure t := by
  exact (AddSubmonoid.closure_le.mpr hf :
    AddSubmonoid.closure s ≤ (AddSubmonoid.closure t).comap (AddMonoidHom.mulLeft r)) hx

private theorem commutingGapClosure_bump {R : Type*} [Semiring R]
    (A B T r : R) (b : Bool) (m k : ℕ)
    (hr : ∀ d : Fin (k + 1) → ℕ × ℕ,
      r * commutingGapForm A B T k d = commutingGapForm A B T k (bumpFirst b d))
    {x : R} (hx : x ∈ commutingGapClosure A B T m k) :
    r * x ∈ commutingGapClosure A B T (m + 1) k := by
  refine mul_mem_addClosure r ?_ hx
  exact fun _ ⟨d, hd, he⟩ ↦ AddSubmonoid.subset_closure
    ⟨bumpFirst b d, (sum_bumpFirst b k d).trans (congrArg (· + 1) hd),
      (hr d).symm.trans (congrArg (r * ·) he)⟩

private theorem commutingGapClosure_prepend {R : Type*} [Semiring R]
    (A B T : R) (m k : ℕ) {x : R} (hx : x ∈ commutingGapClosure A B T m k) :
    T * x ∈ commutingGapClosure A B T m (k + 1) := by
  refine mul_mem_addClosure T ?_ hx
  exact fun _ ⟨d, hd, he⟩ ↦ AddSubmonoid.subset_closure
    ⟨Fin.cons (0, 0) d, by simpa [gapTotal, Fin.sum_univ_succ] using hd,
      by simpa [commutingGapForm] using congrArg (T * ·) he⟩

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

private theorem commutingGapForm_zero {R : Type*} [Semiring R] (A B T : R) (k : ℕ) :
    commutingGapForm A B T k (fun _ ↦ (0, 0)) = T ^ k := by
  induction k with
  | zero => simp [commutingGapForm]
  | succ k ih => simpa [commutingGapForm, pow_succ'] using congrArg (T * ·) ih

private theorem coeff_mem_commutingGapClosure {R : Type*} [Semiring R]
    (A B T : R) (hAB : Commute A B) (m k : ℕ) :
    ((Polynomial.C (A + B) + Polynomial.C T * Polynomial.X) ^ (m + k)).coeff k ∈
      commutingGapClosure A B T m k := by
  induction m generalizing k with
  | zero =>
    simpa only [Nat.zero_add, gapCoeff_zero_left] using
      (show T ^ k ∈ commutingGapClosure A B T 0 k from
        AddSubmonoid.subset_closure ⟨(fun _ ↦ (0, 0)), by simp [gapTotal],
          commutingGapForm_zero A B T k⟩)
  | succ m ih =>
    induction k with
    | zero =>
      rw [Nat.add_zero, gapCoeff_zero_right, pow_succ', add_mul]
      simpa only [Nat.add_zero, gapCoeff_zero_right] using
        (add_mem
          (commutingGapClosure_bump A B T A false m 0
            (commutingGapForm_mul_left_A A B T 0) (ih 0))
          (commutingGapClosure_bump A B T B true m 0
            (commutingGapForm_mul_left_B A B T hAB 0) (ih 0)))
    | succ k ikh =>
      rw [gapCoeff_succ_succ, add_mul]
      exact add_mem (add_mem
        (commutingGapClosure_bump A B T A false m (k + 1)
          (commutingGapForm_mul_left_A A B T (k + 1)) (ih (k + 1)))
        (commutingGapClosure_bump A B T B true m (k + 1)
          (commutingGapForm_mul_left_B A B T hAB (k + 1)) (ih (k + 1))))
        (commutingGapClosure_prepend A B T (m + 1) k ikh)

private theorem commutingGapForm_eq_list {R : Type*} [Semiring R]
    (A B T : R) (k : ℕ) (d : Fin (k + 1) → ℕ × ℕ) :
    commutingGapForm A B T k d =
      (List.ofFn (fun j : Fin k ↦ A ^ (d j.castSucc).1 * B ^ (d j.castSucc).2 * T)).prod *
        (A ^ (d (Fin.last k)).1 * B ^ (d (Fin.last k)).2) := by
  induction k <;> simp_all [commutingGapForm, List.ofFn_succ, mul_assoc]

/-- The distinguished-letter coefficient lies in the span of ordered commuting-gap forms.
Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 604–617 and 646–653.
This assertion does not identify the selected interpolation sum Q or bound Schmidt rank. -/
theorem Polynomial.coeff_pow_C_add_C_mul_X_mem_span_commuting_gaps
    {𝕜 R : Type*} [Semiring 𝕜] [Semiring R] [Module 𝕜 R]
    (A B T : R) (hAB : Commute A B) (m k : ℕ) :
    let E := Finset.piAntidiag
      (Finset.univ : Finset (Fin (k + 1) × Bool)) m
    ((Polynomial.C (A + B) + Polynomial.C T * Polynomial.X) ^ (m + k)).coeff k ∈
      Submodule.span 𝕜 (Set.range (fun d : E ↦
        (List.ofFn (fun j : Fin k ↦
          A ^ d.val (j.castSucc, false) * B ^ d.val (j.castSucc, true) * T)).prod *
          (A ^ d.val (Fin.last k, false) * B ^ d.val (Fin.last k, true)))) := by
  intro E
  refine Submodule.closure_subset_span
    (AddSubmonoid.closure_mono ?_ (coeff_mem_commutingGapClosure A B T hAB m k))
  rintro _ ⟨d, hd, rfl⟩
  let f : Fin (k + 1) × Bool → ℕ := fun jb ↦
    if jb.2 then (d jb.1).2 else (d jb.1).1
  have hf : f ∈ E := by
    simpa [E, Finset.mem_piAntidiag, Fintype.sum_prod_type, Fintype.sum_bool, f,
      gapTotal, Nat.add_comm] using hd
  refine ⟨⟨f, hf⟩, ?_⟩
  simpa [f] using (commutingGapForm_eq_list A B T k d).symm

/-- Stars and bars for the indexed commuting-gap forms in AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 646–657.
**Local fix (count):** The source omits the additional `+1`. The corrected count
is recorded in `docs/paper-gaps/aklv13_interpolation_and_word_count.tex`:
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf. -/
theorem Finset.card_piAntidiag_univ_fin_prod_bool (m k : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin (k + 1) × Bool)) m).card =
      (m + 2 * k + 1).choose (2 * k + 1) := by
  rw [← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ,
    Finset.card_univ, Sym.card_sym_eq_choose]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  have h : (k + 1) * 2 + m - 1 = m + (2 * k + 1) := by omega
  simpa only [h, Nat.add_assoc] using (Nat.choose_symm_add (a := m) (b := 2 * k + 1))
