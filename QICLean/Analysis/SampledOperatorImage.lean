/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceSamplingEvent
import QICLean.Analysis.TensorOperatorPower

/-!
# Actual images of sampled spaces under operator words

A fixed finite family determines its ordered words before an input space
is sampled. The output is the actual sum of images of the actual Haar
sample, with its dimension derived from those two finite constructions.
This supports ALVV, arXiv:1602.08828v2, `l:er`, lines 597–622,
and the modified merge, lines 1662–1677.
The error-reduction implication is supplied explicitly to the probability
composition; a physical application must construct it before the sample.

**Local fix (complex sphere net count):** The probability statement uses
the corrected exponent `2 * dim(T)` and net scale documented in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

open scoped BigOperators TensorProduct
open MeasureTheory

namespace Submodule

variable {M iota : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  [FiniteDimensional ℂ M] [Fintype iota]

/-- The actual operator-word image of the sample-or-full subspace.
Supporting ALVV, arXiv:1602.08828v2, `l:er`, lines 597–622,
and the modified merge, lines 1662–1677. -/
noncomputable def sampledWordImage (F : iota → M →L[ℂ] M) (power s : ℕ)
    (W : Submodule ℂ M) (U : Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ) :
    Submodule ℂ M :=
  let A := sampleIndices s (Module.finrank ℂ W)
  let sample := randomSubspace (stdOrthonormalBasis ℂ W) A U
  ⨆ w : Fin power → iota, sample.map (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap

/-- The actual word-image dimension is bounded by the number of words times
the actual sample dimension. Supporting ALVV, arXiv:1602.08828v2,
`l:er`, lines 597–622, and Lemma `l:rs`, lines 530–558. -/
lemma finrank_sampledWordImage_le (F : iota → M →L[ℂ] M) (power s : ℕ)
    (W : Submodule ℂ M) (U : Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ) :
    Module.finrank ℂ (sampledWordImage F power s W U) ≤
      Fintype.card iota ^ power * min s (Module.finrank ℂ W) := by
  unfold sampledWordImage
  refine (finrank_iSup_le_sum _).trans ?_
  calc
    _ ≤ ∑ _w : Fin power → iota,
        Module.finrank ℂ
          (randomSubspace (stdOrthonormalBasis ℂ W) (sampleIndices s (Module.finrank ℂ W)) U) :=
      Finset.sum_le_sum fun _ _ ↦ finrank_map_le _ _
    _ = _ := by
      rw [finrank_randomSubspace]
      simp only [card_sampleIndices, Finset.card_univ, Fintype.card_fin, Finset.sum_const,
        Fintype.card_fun, smul_eq_mul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A measurable fixed-input Haar event certifies the actual word-image
subspace. The finite family and its error-reduction implication precede the
power and input space. This composition supports ALVV,
arXiv:1602.08828v2, `l:er`, lines 597–622, and the merge, lines 1662–1677.
No adaptive measurability or physical existence of the family is asserted. -/
lemma exists_measurable_sampledWordImage_event
    (F : iota → M →L[ℂ] M) (T : Submodule ℂ (M ⊗[ℂ] E)) (Delta : ℝ)
    (himprove : ∀ (a : ℕ) (S : Submodule ℂ M) (delta : ℝ), IsViable delta S T → delta < 1 →
      IsViable (Delta ^ a / (1 - delta) ^ 2)
        (⨆ w : Fin a → iota, S.map (List.ofFn (fun j ↦ F (w j))).prod.toLinearMap) T)
    (power s : ℕ) (hs : 1 ≤ s) (W : Submodule ℂ M) (hW : W ≠ ⊥)
    {delta : ℝ} (hviable : IsViable delta W T) (hdelta : delta < 1) :
    let q := Module.finrank ℂ W
    let c := (1 - delta) * (min s q : ℕ) / (8 * q)
    let eta : ℝ := if q ≤ s then 0 else
      (1 + 2 / Real.sqrt ((1 - delta) * (s : ℝ) / (8 * q))) ^
        (2 * Module.finrank ℂ T) * q * Real.exp (-(s / 16 : ℝ))
    ∃ Good : Set (Matrix.unitaryGroup (Fin q) ℂ),
      MeasurableSet Good ∧ Matrix.unitaryHaar (Fin q) Goodᶜ ≤ ENNReal.ofReal eta ∧
      1 - ENNReal.ofReal eta ≤ Matrix.unitaryHaar (Fin q) Good ∧
      ∀ U ∈ Good,
        Module.finrank ℂ (sampledWordImage F power s W U) ≤
          Fintype.card iota ^ power * min s q ∧
        IsViable (Delta ^ power / c ^ 2) (sampledWordImage F power s W U) T := by
  intro q c eta
  have hq : 1 ≤ q := Submodule.one_le_finrank_iff.mpr hW
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hnR : (0 : ℝ) < (min s q : ℕ) := by exact_mod_cast (by omega : 0 < min s q)
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨Good, hGood, hbad, hprob, hsample⟩ :=
    exists_measurable_randomSubspace_min_event (stdOrthonormalBasis ℂ W) s hviable hdelta.le
  refine ⟨Good, hGood, hbad, hprob, ?_⟩
  intro U hU
  refine ⟨finrank_sampledWordImage_le F power s W U, ?_⟩
  have hsample' := hsample U hU
  have hfiltered := himprove power _ (1 - c) hsample' (by linarith)
  simpa only [sampledWordImage, sub_sub_cancel] using hfiltered

end Submodule
