/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceBootstrap
import QICLean.Analysis.ViableSubspaceSamplingEvent
import QICLean.Analysis.ViableHalfSamplingParameters

/-!
# One half-dimensional Haar sample for a uniform improving family

A fixed original target determines one measurable sampling-success event.
On that event the same actual sample can be transferred to every nearby
improving target. One common finite family has the same literal image for
all these targets. This image has at most half the original dimension and
retains a fixed viability margin for collective trimming.

This supports ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-dg`,
lines 1065–1074, and the resampling description of modified merge,
lines 749–755.
**Local fix (bootstrap and sampling constants):** The overlap and failure
bound use the corrected constants recorded in
`docs/paper-gaps/alvv16_bootstrap_constants.tex` and
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
**Scope restriction (one fixed-input sampling step):** one
half-dimensional sample is drawn from a fixed input space and the success
event is chosen for that input, as in the proof of `prop:albootstrap-dg`,
lines 1065–1074; see `docs/paper-gaps/alvv16_bootstrap_constants.tex`.
-/

open MeasureTheory Module
open scoped TensorProduct InnerProductSpace

namespace Submodule

variable {M F X ι : Type*} [Fintype ι]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The actual half-dimensional sample and its common-family image have
unconditional dimension bounds, including zero input dimension and zero
family count. No target or viability premise is needed. Supporting ALVV,
arXiv:1602.08828v2, Proposition `prop:albootstrap-dg`, lines 1065–1074. -/
theorem finrank_half_sample_image_le {D q : ℕ} {W : Submodule ℂ M}
    (b : OrthonormalBasis (Fin q) ℂ W) (A : ι → M →L[ℂ] M)
    (hcard : Fintype.card ι ≤ D ^ 2) (U : Matrix.unitaryGroup (Fin q) ℂ) :
    let s : ℕ := q / (2 * D ^ 2)
    let Coord := Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s q))
    let sample := randomSubspace b Coord U
    let image := ⨆ i, sample.map (A i : M →ₗ[ℂ] M)
    sample ≤ W ∧ finrank ℂ sample = s ∧ finrank ℂ image ≤ q / 2 := by
  intro s Coord sample image
  have hs : s ≤ q := Nat.div_le_self q (2 * D ^ 2)
  have hSampleDim : finrank ℂ sample = s := by
    change finrank ℂ (randomSubspace b Coord U) = s
    rw [finrank_randomSubspace]
    simp only [Coord, Finset.card_map, Finset.card_univ, Fintype.card_fin,
      Nat.min_eq_left hs]
  refine ⟨randomSubspace_le b Coord U, hSampleDim, ?_⟩
  calc
    _ ≤ Fintype.card ι * finrank ℂ sample :=
      finrank_iSup_map_le_card_mul sample (fun i ↦ (A i).toLinearMap)
    _ = Fintype.card ι * s := by rw [hSampleDim]
    _ ≤ D ^ 2 * s := Nat.mul_le_mul_right s hcard
    _ ≤ q / 2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
      have hh := Nat.div_mul_le_self q (2 * D ^ 2)
      change s * (2 * D ^ 2) ≤ q at hh
      nlinarith only [hh]

/-- One fixed-original-target Haar event certifies the same actual sampled
image for every member of a uniformly nearby target family. The sample
and its image are retained literally, with their unconditional dimension
bounds. This is a conditional auxiliary to ALVV, arXiv:1602.08828v2,
Proposition `prop:albootstrap-dg`, lines 1065–1074. The target-family and
operator estimates are genuine intermediate data, not physical conclusions. -/
theorem exists_measurable_half_sample_uniform_image_event
    {D q : ℕ} {Delta epsilon : ℝ} {Graw : Submodule ℂ (M ⊗[ℂ] F)}
    (x0 : X) (T : X → Submodule ℂ (M ⊗[ℂ] F))
    (A : ι → M →L[ℂ] M) (hcard : Fintype.card ι ≤ D ^ 2)
    (hRawSoft : ∀ x, IsCloseTo epsilon Graw (T x))
    (hSoftRaw : ∀ x, IsCloseTo (1 / 200) (T x) Graw)
    (hA : ∀ x delta, delta < 1 → ∀ S : Submodule ℂ M,
      IsViable delta S (T x) →
      IsViable (Delta / (1 - delta) ^ 2) (⨆ i, S.map (A i : M →ₗ[ℂ] M)) (T x))
    (hD : 2 ≤ D) (hDelta : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (hepsilon : epsilon ≤ ((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2 / 100)
    {W : Submodule ℂ M} (b : OrthonormalBasis (Fin q) ℂ W)
    (hW : IsViable 0.04 W Graw) (hq : 4 * D ^ 2 ≤ q) :
    let s : ℕ := q / (2 * D ^ 2)
    let alpha : ℝ := (1 - 0.04) * (s : ℝ) / (8 * q)
    let Coord := Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s q))
    let sample := fun U : Matrix.unitaryGroup (Fin q) ℂ ↦ randomSubspace b Coord U
    let image := fun U : Matrix.unitaryGroup (Fin q) ℂ ↦
      ⨆ i, (sample U).map (A i : M →ₗ[ℂ] M)
    1 ≤ s ∧ 0 < alpha ∧ alpha ≤ 1 ∧
    (∀ U, sample U ≤ W ∧ finrank ℂ (sample U) = s ∧
      finrank ℂ (image U) ≤ q / 2) ∧
    ∃ Good : Set (Matrix.unitaryGroup (Fin q) ℂ),
      MeasurableSet Good ∧
      Matrix.unitaryHaar (Fin q) Goodᶜ ≤ ENNReal.ofReal (bootstrapFailure D q (finrank ℂ Graw)) ∧
      1 - ENNReal.ofReal (bootstrapFailure D q (finrank ℂ Graw)) ≤
        Matrix.unitaryHaar (Fin q) Good ∧
      (∀ U ∈ Good,
        IsViable (1 - alpha) (sample U) Graw ∧
        (∀ x, IsViable (1 - alpha / 2) (sample U) (T x) ∧
          IsViable (4 * Delta / alpha ^ 2) (image U) (T x)) ∧
        IsViable (27 / 2500) (image U) Graw) ∧
      Matrix.unitaryHaar (Fin q) {U | ¬ IsViable (27 / 2500) (image U) Graw} ≤
        ENNReal.ofReal (bootstrapFailure D q (finrank ℂ Graw)) := by
  intro s alpha Coord sample image
  have hq0 : 0 < q := lt_of_lt_of_le
    (by positivity : 0 < 4 * D ^ 2) hq
  have hs1 : 1 ≤ s :=
    (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * D ^ 2)).mpr (by nlinarith only [hq])
  have hslt : s < q := Nat.div_lt_self hq0 (by
    have : 0 < D ^ 2 := pow_pos (by omega) 2
    omega)
  have hfloor := bootstrap_sample_floor_lower_bound D q hD hq
  have halphaLower : (3 / 100 : ℝ) / (D : ℝ) ^ 2 ≤ alpha := by
    have hqs : (q : ℝ) ≤ (s : ℝ) * (4 * (D : ℝ) ^ 2) :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (D : ℝ) ^ 2)).mp hfloor
    dsimp only [alpha]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hqs]
  have halpha0 : 0 < alpha :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (3 / 100) / (D : ℝ) ^ 2) halphaLower
  have halpha1 : alpha ≤ 1 := by
    have hsR : (s : ℝ) ≤ q := by exact_mod_cast hslt.le
    have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq0
    dsimp only [alpha]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hsR, hqR.le]
  have hepsilonAlpha : epsilon ≤ alpha ^ 2 / 100 :=
    hepsilon.trans (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) halphaLower 2) (by norm_num))
  have hfilter : Delta / alpha ^ 2 ≤ 1 / 10000 :=
    Real.half_sampling_filter_error_le (by exact_mod_cast hD) hDelta halphaLower
  obtain ⟨Good, hGood, hBad, hSuccess, hSample⟩ :=
    exists_measurable_randomSubspace_min_event b s hW (by norm_num)
  have hBadRaw : Matrix.unitaryHaar (Fin q) Goodᶜ ≤
      ENNReal.ofReal (bootstrapFailure D q (finrank ℂ Graw)) := by
    simpa only [bootstrapFailure, ite_eq_right (not_le.mpr hslt), s] using hBad
  have hSuccessRaw : 1 - ENNReal.ofReal (bootstrapFailure D q (finrank ℂ Graw)) ≤
      Matrix.unitaryHaar (Fin q) Good := by
    simpa only [bootstrapFailure, ite_eq_right (not_le.mpr hslt), s] using hSuccess
  have hSampleRaw (U) (hU : U ∈ Good) : IsViable (1 - alpha) (sample U) Graw := by
    have hh := hSample U hU
    change IsViable (1 - (1 - 0.04) * (min s q : ℕ) / (8 * q)) (sample U) Graw at hh
    simpa only [Nat.min_eq_left hslt.le, alpha] using hh
  have hSampleSoft (U) (hU : U ∈ Good) (x : X) :
      IsViable (1 - alpha / 2) (sample U) (T x) :=
    (IsCloseTo.trans_weighted (hSampleRaw U hU) (hRawSoft x)
      (sub_nonneg.mpr halpha1) (by positivity : 0 < alpha / 4)).of_le
        (Real.half_sampling_transfer_error_le halpha0 hepsilonAlpha)
  have hImageSoft (U) (hU : U ∈ Good) (x : X) :
      IsViable (4 * Delta / alpha ^ 2) (image U) (T x) := by
    have hh := hA x (1 - alpha / 2) (by linarith) (sample U) (hSampleSoft U hU x)
    have heq : Delta / (alpha / 2) ^ 2 = 4 * Delta / alpha ^ 2 := by
      field_simp [ne_of_gt halpha0]
      ring
    simpa only [sub_sub_cancel, heq] using hh
  have hImageRaw (U) (hU : U ∈ Good) : IsViable (27 / 2500) (image U) Graw := by
    have hh : IsViable (1 / 2500) (image U) (T x0) :=
      (hImageSoft U hU x0).of_le (by
        calc
          4 * Delta / alpha ^ 2 = 4 * (Delta / alpha ^ 2) := by ring
          _ ≤ 4 * (1 / 10000 : ℝ) := mul_le_mul_of_nonneg_left hfilter (by norm_num)
          _ = 1 / 2500 := by norm_num)
    exact (IsCloseTo.trans hh (hSoftRaw x0) (by norm_num)).of_le (by norm_num)
  refine ⟨hs1, halpha0, halpha1,
    (fun U ↦ finrank_half_sample_image_le b A hcard U),
    Good, hGood, hBadRaw, hSuccessRaw,
    (fun U hU ↦ ⟨hSampleRaw U hU,
      (fun x ↦ ⟨hSampleSoft U hU x, hImageSoft U hU x⟩), hImageRaw U hU⟩), ?_⟩
  exact (measure_mono (μ := Matrix.unitaryHaar (Fin q))
    (show {U | ¬ IsViable (27 / 2500) (image U) Graw} ⊆ Goodᶜ from
      fun U hU hUGood ↦ hU (hImageRaw U hUGood))).trans hBadRaw

end Submodule
