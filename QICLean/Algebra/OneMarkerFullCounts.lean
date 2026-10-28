/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OneMarkerWeightedSchmidtRank
import QICLean.Algebra.WordCoefficient
import Mathlib.Logic.Equiv.Option

/-!
# One distinguished frequency in the original word family

Removing one distinguished letter identifies the remaining alphabet with its complement.
The actual full-frequency coefficient is unchanged when words are rewritten using an
optional ordinary letter, with `none` denoting the distinguished interaction.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 604--635.
This identity retains every ordered-word multiplicity and imposes no independence
condition on the operator family.
-/

open scoped BigOperators

namespace WordMultiplicity

open Classical in
/-- The full frequency vector obtained by inserting the distinguished frequency.
AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 626--635. -/
noncomputable def insertMarkerFrequency {ι : Type*} (u : ι) (k : ℕ)
    (α : {a : ι // a ≠ u} → ℕ) (a : ι) : ℕ :=
  if h : a = u then k else α ⟨a, h⟩

open Classical in
/-- The inserted full frequency has the distinguished count plus the ordinary total.
AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 626--635. -/
theorem sum_insertMarkerFrequency {ι : Type*} [Fintype ι] (u : ι) [Fintype {a : ι // a ≠ u}] (k : ℕ)
    (α : {a : ι // a ≠ u} → ℕ) :
    (∑ a, insertMarkerFrequency u k α a) = k + ∑ a, α a := by
  rw [← (Equiv.optionSubtypeNe u).sum_comp, Fintype.sum_option]
  simp only [Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some]
  congr 1
  · simp [insertMarkerFrequency]
  · apply Finset.sum_congr rfl
    intro a _
    simp [insertMarkerFrequency, a.property]

open Classical in
/-- Rewriting the alphabet preserves the actual fixed-frequency coefficient.
AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 626--635. -/
theorem wordCoefficient_insertMarkerFrequency {ι R : Type*} [Fintype ι] [Semiring R]
    (H : ι → R) (u : ι) [Fintype {a : ι // a ≠ u}] (m k : ℕ) (α : {a : ι // a ≠ u} → ℕ) :
    wordCoefficient H (m + k) (insertMarkerFrequency u k α) =
      oneMarkerCoefficient (fun a : {a : ι // a ≠ u} ↦ H a.val) (H u) m k α := by
  classical
  let e := Equiv.optionSubtypeNe u
  let ew : (Fin (m + k) → Option {a : ι // a ≠ u}) ≃ (Fin (m + k) → ι) :=
    Equiv.piCongrRight (fun _ : Fin (m + k) ↦ e)
  have hew (w : Fin (m + k) → Option {a : ι // a ≠ u}) :
      ew w = fun p ↦ e (w p) := by
    ext p
    simp only [ew, Equiv.piCongrRight_apply, Pi.map_apply]
  have hnone (w : Fin (m + k) → Option {a : ι // a ≠ u}) :
      countsFinsupp (ew w) u = countsFinsupp w none := by
    simpa only [hew, e, Equiv.optionSubtypeNe_none] using countsFinsupp_equiv e w none
  have hsome (w : Fin (m + k) → Option {a : ι // a ≠ u}) (a : {a : ι // a ≠ u}) :
      countsFinsupp (ew w) a.val = countsFinsupp w (some a) := by
    simpa only [hew, e, Equiv.optionSubtypeNe_some] using countsFinsupp_equiv e w (some a)
  have hins : insertMarkerFrequency u k α u = k := by simp [insertMarkerFrequency]
  have hrest (a : {a : ι // a ≠ u}) : insertMarkerFrequency u k α a.val = α a := by
    simp [insertMarkerFrequency, a.property]
  have hfreq (w : Fin (m + k) → Option {a : ι // a ≠ u}) :
      (countsFinsupp (ew w) : ι → ℕ) = insertMarkerFrequency u k α ↔
        countsFinsupp w none = k ∧ ∀ a, countsFinsupp w (some a) = α a := by
    constructor
    · intro h
      exact ⟨(hnone w).symm.trans ((congrFun h u).trans hins),
        fun a ↦ (hsome w a).symm.trans ((congrFun h a.val).trans (hrest a))⟩
    · rintro ⟨hn, hs⟩
      funext a
      by_cases hau : a = u
      · subst a
        exact ((hnone w).trans hn).trans hins.symm
      · exact ((hsome w ⟨a, hau⟩).trans (hs ⟨a, hau⟩)).trans (hrest ⟨a, hau⟩).symm
  simp only [wordCoefficient, oneMarkerCoefficient, Finset.sum_filter]
  rw [← ew.sum_comp]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  simp only [hfreq]
  split_ifs
  · apply congrArg List.prod
    apply congrArg List.ofFn
    funext p
    rw [hew]
    dsimp only
    cases w p <;> rfl
  · rfl

open Classical in
/-- A weighted slice of the original full-frequency family is exactly the same weighted
one-marker family on the residual alphabet. AKLV, arXiv:1301.1162v1, Lemma 4.2,
lines 626--644. This equality retains all ordered-word multiplicities. -/
theorem sum_smul_wordCoefficient_marker_eq {ι R : Type*} [Fintype ι] [Semiring R]
    [Algebra ℂ R] (H : ι → R) (u : ι) [Fintype {a : ι // a ≠ u}] (m k : ℕ) (weight : (ι → ℕ) → ℂ) :
    let F := (Finset.piAntidiag (Finset.univ : Finset ι) (m + k)).filter (fun β ↦ β u = k)
    let I := {a : ι // a ≠ u}
    let E := @Finset.piAntidiag I ℕ (Classical.decEq I) _ _ _ Finset.univ m
    (∑ β ∈ F, weight β • wordCoefficient H (m + k) β) =
      ∑ α : E, weight (insertMarkerFrequency u k α.val) •
        oneMarkerCoefficient (fun a : I ↦ H a.val) (H u) m k α.val := by
  intro F I E
  let : DecidableEq I := Classical.decEq I
  let ins : E → F := fun α ↦ ⟨insertMarkerFrequency u k α.val, by
    refine Finset.mem_filter.mpr ⟨?_, by simp [insertMarkerFrequency]⟩
    apply Finset.mem_piAntidiag.mpr
    refine ⟨?_, fun _ _ ↦ Finset.mem_univ _⟩
    rw [sum_insertMarkerFrequency, (Finset.mem_piAntidiag.mp α.property).1]
    omega⟩
  have hinj : Function.Injective ins := by
    intro α β h
    apply Subtype.ext
    funext a
    have ha := congrArg (fun f : F ↦ f.val a.val) h
    simpa only [ins, insertMarkerFrequency, dite_eq_right a.property] using ha
  have hsurj : Function.Surjective ins := by
    intro β
    let α : I → ℕ := fun a ↦ β.val a.val
    have hβu : β.val u = k := (Finset.mem_filter.mp β.property).2
    have hβsum : (∑ a, β.val a) = m + k :=
      (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp β.property).1).1
    have hβeq : insertMarkerFrequency u k α = β.val := by
      funext a
      by_cases hau : a = u
      · subst a
        simpa only [insertMarkerFrequency, dite_eq_left] using hβu.symm
      · simp only [insertMarkerFrequency, dite_eq_right hau, α]
    have hsum := sum_insertMarkerFrequency u k α
    rw [hβeq, hβsum] at hsum
    have htotal := Nat.add_left_cancel ((Nat.add_comm k m).trans hsum)
    have hα : α ∈ E := by
      apply Finset.mem_piAntidiag.mpr
      refine ⟨?_, fun _ _ ↦ Finset.mem_univ _⟩
      refine (Finset.sum_congr ?_ (fun _ _ ↦ rfl)).trans htotal.symm
      ext a
      simp
    exact ⟨⟨α, hα⟩, Subtype.ext hβeq⟩
  let e : E ≃ F := Equiv.ofBijective ins ⟨hinj, hsurj⟩
  rw [← Finset.sum_coe_sort F (fun β ↦ weight β • wordCoefficient H (m + k) β)]
  symm
  refine Fintype.sum_equiv e _ _ fun α ↦ ?_
  change weight (insertMarkerFrequency u k α.val) •
      oneMarkerCoefficient (fun a : I ↦ H a.val) (H u) m k α.val =
    weight (insertMarkerFrequency u k α.val) •
      wordCoefficient H (m + k) (insertMarkerFrequency u k α.val)
  rw [wordCoefficient_insertMarkerFrequency]

end WordMultiplicity
