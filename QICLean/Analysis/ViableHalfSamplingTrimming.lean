/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableHalfSampling
import QICLean.Analysis.ViableSubspaceReferenceTrimming
import QICLean.Analysis.ViableSubspaceTrimmingInvariance

/-!
# Original-target reference trimming after one half-dimensional sample

The actual common-family image of one Haar sample is transferred back to
the original target before collective trimming. The reference approximates
that original target, so no improving-target/reference comparison is used.
The same sampled space, operator image and trimming projections are retained.

This supports ALVV, arXiv:1602.08828v2, the resampling description at
lines 749–755, the bootstrap at lines 1065–1074, and the reference argument
at lines 1801–1813.
**Local fix (trimming constant):** The estimate retains the corrected
increment recorded in `docs/paper-gaps/alvv16_trimming_constant.tex`.
**Scope restriction (one fixed-input sampling step):** one
half-dimensional sample is drawn from a fixed input space and the success
event is chosen for that input, as in the proof of `prop:albootstrap-dg`,
lines 1065–1074; see `docs/paper-gaps/alvv16_bootstrap_constants.tex`.
-/

open MeasureTheory Module
open scoped TensorProduct InnerProductSpace

namespace Entropy

variable {V β X ι : Type*} [Fintype V] [DecidableEq V]
  [Fintype β] [Fintype ι] {n : V → ℕ}

/-- The same half-sample image is collectively trimmed relative to the
original target. A fixed-input measurable Haar event certifies all improving
targets, the original-target output, and the literal dimension decrease.
This is a conditional auxiliary to ALVV, arXiv:1602.08828v2,
lines 749–755, 1065–1074 and 1801–1813; it does not supply the physical
family/reference or claim a joint adaptive sampling law. -/
theorem exists_measurable_half_sample_reference_trim_event
    {D q m bRef : ℕ} {Delta epsilon epsilonRef xi : ℝ}
    {Graw R : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β))}
    (x0 : X) (T : X → Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β)))
    (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n))
    (hcard : Fintype.card ι ≤ D ^ 2)
    (hRawSoft : ∀ x, Submodule.IsCloseTo epsilon Graw (T x))
    (hSoftRaw : ∀ x, Submodule.IsCloseTo (1 / 200) (T x) Graw)
    (hA : ∀ x delta, delta < 1 →
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)),
      Submodule.IsCloseTo delta (Submodule.prodExt S β) (T x) →
      Submodule.IsCloseTo (Delta / (1 - delta) ^ 2)
        (Submodule.prodExt (⨆ i, S.map (A i : _ →ₗ[ℂ] _)) β) (T x))
    (hD : 2 ≤ D) (hDelta : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (hepsilon : epsilon ≤ ((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2 / 100)
    (C : ℕ → Finset V) (hC : Monotone C) (hxi : 0 < xi)
    (hepsilonRef0 : 0 ≤ epsilonRef) (hepsilonRef : epsilonRef ≤ 1 / 100000)
    (hRawRef : Submodule.IsCloseTo epsilonRef Graw R)
    (hRefRaw : Submodule.IsCloseTo epsilonRef R Graw)
    (hRank : ∀ t ∈ R, ∀ j < m,
      Matrix.schmidtRank (WithLp.ofLp (cutEnvVector (C j) t)) ≤ bRef)
    (hbudget : xi * Real.sqrt ((m : ℝ) * (bRef : ℝ)) ≤ 1 / 1000)
    {W : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))}
    (b : OrthonormalBasis (Fin q) ℂ W)
    (hW : Submodule.IsCloseTo 0.04 (Submodule.prodExt W β) Graw)
    (hq : 4 * D ^ 2 ≤ q) :
    let s : ℕ := q / (2 * D ^ 2)
    let alpha : ℝ := (1 - 0.04) * (s : ℝ) / (8 * q)
    let Coord := Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s q))
    let sample := fun U : Matrix.unitaryGroup (Fin q) ℂ ↦ Submodule.randomSubspace b Coord U
    let image : Matrix.unitaryGroup (Fin q) ℂ →
        Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) := fun U ↦
      ⨆ i, (sample U).map (A i : _ →ₗ[ℂ] _)
    let output : Matrix.unitaryGroup (Fin q) ℂ →
        Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) := fun U ↦
      trimSubspace C xi
        (fun i ↦ (stdOrthonormalBasis ℂ (image U) i : EuclideanSpace ℂ (SiteConfig n))) m
    1 ≤ s ∧ 0 < alpha ∧ alpha ≤ 1 ∧
    (∀ U, sample U ≤ W ∧ finrank ℂ (sample U) = s ∧
      finrank ℂ (image U) ≤ q / 2 ∧ finrank ℂ (output U) ≤ q / 2) ∧
    ∃ Good : Set (Matrix.unitaryGroup (Fin q) ℂ),
      MeasurableSet Good ∧
      Matrix.unitaryHaar (Fin q) Goodᶜ ≤
        ENNReal.ofReal (Submodule.bootstrapFailure D q (finrank ℂ Graw)) ∧
      1 - ENNReal.ofReal (Submodule.bootstrapFailure D q (finrank ℂ Graw)) ≤
        Matrix.unitaryHaar (Fin q) Good ∧
      (∀ U ∈ Good,
        (∀ x, Submodule.IsCloseTo (4 * Delta / alpha ^ 2)
          (Submodule.prodExt (image U) β) (T x)) ∧
        Submodule.IsCloseTo (27 / 2500) (Submodule.prodExt (image U) β) Graw ∧
        Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (output U) β) Graw) ∧
      Matrix.unitaryHaar (Fin q)
        {U | ¬ Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (output U) β) Graw} ≤
        ENNReal.ofReal (Submodule.bootstrapFailure D q (finrank ℂ Graw)) := by
  classical
  intro s alpha Coord sample image output
  let e := Submodule.euclideanTensorEquiv (SiteConfig n) β
  have hImprove (x) (delta) (hdelta : delta < 1)
      (S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)))
      (hS : Submodule.IsViable delta S ((T x).map e.toLinearEquiv.toLinearMap)) :
      Submodule.IsViable (Delta / (1 - delta) ^ 2)
        (⨆ i, S.map (A i : _ →ₗ[ℂ] _)) ((T x).map e.toLinearEquiv.toLinearMap) :=
    (Submodule.isCloseTo_prodExt_iff_isViable _ _).mp
      (hA x delta hdelta S ((Submodule.isCloseTo_prodExt_iff_isViable S (T x)).mpr hS))
  obtain ⟨hs1, ha0, ha1, hprofile, Good, hGood, hBad, hSuccess, hResult, _⟩ :=
    Submodule.exists_measurable_half_sample_uniform_image_event
      (Graw := Graw.map e.toLinearEquiv.toLinearMap)
      x0 (fun x ↦ (T x).map e.toLinearEquiv.toLinearMap) A hcard
      (fun x ↦ (Submodule.isCloseTo_map_iff e).mpr (hRawSoft x))
      (fun x ↦ (Submodule.isCloseTo_map_iff e).mpr (hSoftRaw x))
      hImprove hD hDelta hepsilon b
      ((Submodule.isCloseTo_prodExt_iff_isViable W Graw).mp hW) hq
  have hdim : finrank ℂ (Graw.map e.toLinearEquiv.toLinearMap) = finrank ℂ Graw :=
    LinearEquiv.finrank_map_eq e.toLinearEquiv Graw
  have hImageRaw (U) (hU : U ∈ Good) :
      Submodule.IsCloseTo (27 / 2500) (Submodule.prodExt (image U) β) Graw :=
    (Submodule.isCloseTo_prodExt_iff_isViable (image U) Graw).mpr
      ((hResult U hU).2.2)
  have hOutputRaw (U) (hU : U ∈ Good) :
      Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (output U) β) Graw := by
    have ht := isCloseTo_prodExt_trimSubspace_of_reference_weighted hC hxi
      (by norm_num : (0 : ℝ) ≤ 27 / 2500) hepsilonRef0
      (by norm_num : (0 : ℝ) < 1 / 20)
      (stdOrthonormalBasis ℂ (image U)) (hImageRaw U hU) hRawRef hRefRaw hRank
    exact ht.of_le (Real.half_sampling_trim_error_le le_rfl hepsilonRef hbudget)
  have hOutputDim (U) : finrank ℂ (output U) ≤ q / 2 := by
    change finrank ℂ (trimSubspace C xi
      (fun i ↦ (stdOrthonormalBasis ℂ (image U) i : EuclideanSpace ℂ (SiteConfig n))) m) ≤ _
    rw [trimSubspace_eq_map_of_orthonormalBasis]
    exact (Submodule.finrank_map_le _ _).trans (hprofile U).2.2
  refine ⟨hs1, ha0, ha1,
    (fun U ↦ ⟨(hprofile U).1, (hprofile U).2.1, (hprofile U).2.2, hOutputDim U⟩),
    Good, hGood, ?_, ?_, ?_, ?_⟩
  · simpa only [hdim] using hBad
  · simpa only [hdim] using hSuccess
  · intro U hU
    exact ⟨(fun x ↦ (Submodule.isCloseTo_prodExt_iff_isViable (image U) (T x)).mpr
      ((hResult U hU).2.1 x).2), hImageRaw U hU, hOutputRaw U hU⟩
  · exact (measure_mono (μ := Matrix.unitaryHaar (Fin q))
      (show {U | ¬ Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (output U) β) Graw}
          ⊆ Goodᶜ from fun U hU hUGood ↦ hU (hOutputRaw U hUGood))).trans
        (by simpa only [hdim] using hBad)

end Entropy
