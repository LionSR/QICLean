/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceSampleOrFull

/-!
# A measurable success event for one actual Haar sample

For each fixed viable input space, a measurable event of Haar unitaries
satisfies the sampling conclusion. Its complement has the certified
failure measure. Retaining the whole input has failure measure zero.
This supports ALVV, arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558,
and the merge analysis, lines 1777–1817.

The event is constructed for a fixed input. No measurability of its choice
as the input space varies, or of an adaptive randomized tree, is asserted.

**Local fix (complex sphere net count):** The failure estimate retains the
corrected exponent `2 * dim(T)` and net scale, as documented in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

open scoped TensorProduct
open MeasureTheory

namespace Submodule

variable {M F : Type*}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- There is a genuine measurable Haar-success event for the actual
sample-or-full construction at a fixed input. Its failure measure obeys
the corrected sampling estimate, and every unitary in the event produces
the stated viable space. Supporting ALVV, arXiv:1602.08828v2,
Lemma `l:rs`, lines 530–558. This is not an adaptive measurability assertion. -/
lemma exists_measurable_randomSubspace_min_event {W : Submodule ℂ M} {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℂ W) (s : ℕ) {delta : ℝ}
    {T : Submodule ℂ (M ⊗[ℂ] F)} (hT : IsViable delta W T) (hdelta : delta ≤ 1) :
    let A := Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s q))
    let eta : ℝ := if q ≤ s then 0 else
      (1 + 2 / Real.sqrt ((1 - delta) * (s : ℝ) / (8 * q))) ^
        (2 * Module.finrank ℂ T) * q * Real.exp (-(s / 16 : ℝ))
    ∃ Good : Set (Matrix.unitaryGroup (Fin q) ℂ),
      MeasurableSet Good ∧
      Matrix.unitaryHaar (Fin q) Goodᶜ ≤ ENNReal.ofReal eta ∧
      1 - ENNReal.ofReal eta ≤ Matrix.unitaryHaar (Fin q) Good ∧
      ∀ U ∈ Good, IsViable (1 - (1 - delta) * (min s q : ℕ) / (8 * q))
        (randomSubspace b A U) T := by
  intro A eta
  have hcard : A.card = min s q := by simp [A]
  by_cases hfull : q ≤ s
  · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_, ?_⟩
    · simp [eta, hfull]
    · simp [eta, hfull]
    · intro U _
      exact hT.randomSubspace_min_of_le b s hdelta hfull U
  · let Bad : Set (Matrix.unitaryGroup (Fin q) ℂ) :=
      {U | ¬ IsViable (1 - (1 - delta) * (min s q : ℕ) / (8 * q))
        (randomSubspace b A U) T}
    let Good := (toMeasurable (Matrix.unitaryHaar (Fin q)) Bad)ᶜ
    have hGood : MeasurableSet Good := (measurableSet_toMeasurable _ _).compl
    have hBad : Matrix.unitaryHaar (Fin q) Bad ≤ ENNReal.ofReal eta := by
      have hbound := unitaryHaar_not_isViable_randomSubspace_le b A hT
      simpa only [Bad, eta, ite_eq_right hfull, hcard,
        Nat.min_eq_left (by omega : s ≤ q), Fintype.card_fin] using hbound
    have hcompl : Matrix.unitaryHaar (Fin q) Goodᶜ ≤ ENNReal.ofReal eta := by
      simpa only [Good, compl_compl, measure_toMeasurable] using hBad
    refine ⟨Good, hGood, hcompl, ?_, ?_⟩
    · have hmeasure : Matrix.unitaryHaar (Fin q) Good =
          1 - Matrix.unitaryHaar (Fin q) Goodᶜ := by
        simpa only [compl_compl, measure_univ] using
          measure_compl (μ := Matrix.unitaryHaar (Fin q)) hGood.compl (measure_ne_top _ _)
      rw [hmeasure]
      exact tsub_le_tsub_left hcompl 1
    · intro U hU
      change U ∉ toMeasurable (Matrix.unitaryHaar (Fin q)) Bad at hU
      by_contra hbad
      exact hU (subset_toMeasurable _ _ hbad)

end Submodule
