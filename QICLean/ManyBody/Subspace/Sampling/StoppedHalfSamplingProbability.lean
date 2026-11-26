/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Subspace.Sampling.NativeFamilyImageCoordinates
import QICLean.ManyBody.Subspace.Sampling.CanonicalHalfSamplingDimension
import QICLean.Probability.Sampling.ViableSubspaceBootstrap
import QICLean.Probability.Measure.FiniteProductSectionProbability
import QICLean.Analysis.Subspace.ViableSubspace
import QICLean.Probability.Haar.RankUnitaryProductHaar
import QICLean.Probability.Sampling.ViableSubspaceSampleOrFull
import QICLean.ManyBody.Subspace.Trimming
import QICLean.ManyBody.Subspace.TrimmingInvariance
import QICLean.ManyBody.Subspace.Sampling.StoppedHalfSamplingSeed
import QICLean.Probability.Measurable.MatrixRangeProjectionMeasurable

/-!
# Joint original-target probability for stopped half-dimensional resampling

A finite product of the actual rank-unitary Haar laws supplies fresh seeds
for the existing stopped iteration. Guarded true failures depend on the
original target alone. This supports the repeated-resampling variant
associated with ALVV, arXiv:1602.08828v2, lines 749–755.
No measurable choice of auxiliary success events is used.

It also contains the following results.

* `Entropy.exists_measurable_half_sample_reference_trim_event`,
  `Entropy.exists_measurable_randomRangeSubspace_half_trim_event`: a product Haar law for the actual
  half-sample, image and reference trim.
* `Entropy.canonicalHalfSamplingRawGood`, `Entropy.measurableSet_canonicalHalfSamplingRawGood`:
  joint measurable original-target histories of stopped resampling.
-/

section RankUnitaryHalfSampling

/-!
## A product Haar law for the actual half-sample, image and reference trim

A fixed finite product supplies the unitary at the actual matrix rank.
Transporting the canonical orthonormal range basis to prescribed physical
coordinates identifies its existing random subspace with the literal
canonical sample. One fixed-original-target measurable event is then
pulled back by that rank evaluation, without choosing another measurable
hull or comparing two arbitrary bases.

This is an auxiliary for ALVV, arXiv:1602.08828v2, the resampling description
at lines 749–755, the bootstrap at lines 1065–1074, and the reference
argument at lines 1801–1813.

**Local fix (sampling and trimming constants):** The probability and trim
errors retain the corrected constants documented in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex` and
`docs/paper-gaps/alvv16_trimming_constant.tex`.
**Scope restriction (one fixed-input sampling step):** one
half-dimensional sample is drawn from a fixed input space and the success
event is chosen for that input, as in the proof of `prop:albootstrap-dg`,
lines 1065–1074; see `docs/paper-gaps/alvv16_bootstrap_constants.tex`.
No measurable choice of these events as the input matrix varies is
asserted.
-/

section ViableHalfSamplingTrimming

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
    {Graw R : Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β))}
    (x0 : X) (T : X → Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β)))
    (A : ι → EuclideanSpace ℂ (∀ v, Fin (n v)) →L[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v)))
    (hcard : Fintype.card ι ≤ D ^ 2)
    (hRawSoft : ∀ x, Submodule.IsCloseTo epsilon Graw (T x))
    (hSoftRaw : ∀ x, Submodule.IsCloseTo (1 / 200) (T x) Graw)
    (hA : ∀ x delta, delta < 1 →
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))),
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
    {W : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v)))}
    (b : OrthonormalBasis (Fin q) ℂ W)
    (hW : Submodule.IsCloseTo 0.04 (Submodule.prodExt W β) Graw)
    (hq : 4 * D ^ 2 ≤ q) :
    let s : ℕ := q / (2 * D ^ 2)
    let alpha : ℝ := (1 - 0.04) * (s : ℝ) / (8 * q)
    let Coord := Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s q))
    let sample := fun U : Matrix.unitaryGroup (Fin q) ℂ ↦ Submodule.randomSubspace b Coord U
    let image : Matrix.unitaryGroup (Fin q) ℂ →
        Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) := fun U ↦
      ⨆ i, (sample U).map (A i : _ →ₗ[ℂ] _)
    let output : Matrix.unitaryGroup (Fin q) ℂ →
        Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) := fun U ↦
      trimSubspace C xi
        (fun i ↦ (stdOrthonormalBasis ℂ (image U) i : EuclideanSpace ℂ (∀ v, Fin (n v)))) m
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
  let e := Submodule.euclideanTensorEquiv (∀ v, Fin (n v)) β
  have hImprove (x) (delta) (hdelta : delta < 1)
      (S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))))
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
      (fun i ↦ (stdOrthonormalBasis ℂ (image U) i : EuclideanSpace ℂ (∀ v, Fin (n v)))) m) ≤ _
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

end ViableHalfSamplingTrimming

open MeasureTheory Module
open scoped TensorProduct InnerProductSpace

namespace Submodule

private theorem randomSubspace_map_linearIsometryEquiv
    {M M' : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    [FiniteDimensional ℂ M] [NormedAddCommGroup M'] [InnerProductSpace ℂ M']
    [FiniteDimensional ℂ M'] {W : Submodule ℂ M} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ W) (I : M ≃ₗᵢ[ℂ] M')
    (A : Finset ι) (U : Matrix.unitaryGroup ι ℂ) :
    randomSubspace (b.map (LinearIsometryEquiv.submoduleMap W I)) A U =
      (randomSubspace b A U).map I.toLinearMap := by
  have hEmbedding :
      (basisEmbedding (b.map (LinearIsometryEquiv.submoduleMap W I))).toLinearMap =
        I.toLinearMap.comp (basisEmbedding b).toLinearMap := by
    ext x
    rfl
  simp only [randomSubspace, hEmbedding, Submodule.map_comp]

end Submodule

namespace Entropy

variable {V β X ι : Type*} [Fintype V] [DecidableEq V]
  [Fintype β] [Fintype ι] {n : V → ℕ} {d : ℕ}

/-- The actual matrix-range half-sample, common improving image and original-target
reference trim obey the fixed-input estimate under one product Haar law.
The same Borel event certifies every improving target, and all dimension
bounds hold for every seed. This is a conditional auxiliary to ALVV,
arXiv:1602.08828v2, lines 749–755, 1065–1074 and 1801–1813.
The physical family and reference remain explicit intermediate hypotheses;
no adaptive joint law or probability estimate is assumed. -/
theorem exists_measurable_randomRangeSubspace_half_trim_event
    (e : Fin d ≃ (∀ v, Fin (n v))) (P : Matrix (Fin d) (Fin d) ℂ)
    {D m bRef : ℕ} {Delta epsilon epsilonRef xi : ℝ}
    {Graw R : Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β))}
    (x0 : X) (T : X → Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β)))
    (A : ι → EuclideanSpace ℂ (∀ v, Fin (n v)) →L[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v)))
    (hcard : Fintype.card ι ≤ D ^ 2)
    (hRawSoft : ∀ x, Submodule.IsCloseTo epsilon Graw (T x))
    (hSoftRaw : ∀ x, Submodule.IsCloseTo (1 / 200) (T x) Graw)
    (hA : ∀ x delta, delta < 1 →
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))),
      Submodule.IsCloseTo delta (Submodule.prodExt S β) (T x) →
      Submodule.IsCloseTo (Delta / (1 - delta) ^ 2)
        (Submodule.prodExt (⨆ i, S.map (A i).toLinearMap) β) (T x))
    (hD : 2 ≤ D) (hDelta : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (hepsilon : epsilon ≤ ((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2 / 100)
    (C : ℕ → Finset V) (hC : Monotone C) (hxi : 0 < xi)
    (hepsilonRef0 : 0 ≤ epsilonRef) (hepsilonRef : epsilonRef ≤ 1 / 100000)
    (hRawRef : Submodule.IsCloseTo epsilonRef Graw R)
    (hRefRaw : Submodule.IsCloseTo epsilonRef R Graw)
    (hRank : ∀ t ∈ R, ∀ j < m,
      Matrix.schmidtRank (WithLp.ofLp (cutEnvVector (C j) t)) ≤ bRef)
    (hbudget : xi * Real.sqrt ((m : ℝ) * (bRef : ℝ)) ≤ 1 / 1000)
    (hW : Submodule.IsCloseTo 0.04
      (Submodule.prodExt ((Matrix.toEuclideanLin P).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw)
    (hq : 4 * D ^ 2 ≤ P.rank) :
    let I := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
    let W := (Matrix.toEuclideanLin P).range.map I.toLinearMap
    let q := P.rank
    let s : ℕ := q / (2 * D ^ 2)
    let alpha : ℝ := (1 - 0.04) * (s : ℝ) / (8 * q)
    let sample := fun U : Matrix.rankUnitaryProduct d ↦
      (Matrix.randomRangeSubspace P s U).map I.toLinearMap
    let image : Matrix.rankUnitaryProduct d →
        Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) := fun U ↦
      ⨆ i, (sample U).map (A i).toLinearMap
    let output : Matrix.rankUnitaryProduct d →
        Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) := fun U ↦
      trimSubspace C xi
        (fun i ↦ (stdOrthonormalBasis ℂ (image U) i : EuclideanSpace ℂ (∀ v, Fin (n v)))) m
    1 ≤ s ∧ 0 < alpha ∧ alpha ≤ 1 ∧
    (∀ U, sample U ≤ W ∧ finrank ℂ (sample U) = s ∧
      finrank ℂ (image U) ≤ q / 2 ∧ finrank ℂ (output U) ≤ q / 2) ∧
    ∃ Good : Set (Matrix.rankUnitaryProduct d),
      MeasurableSet Good ∧
      Matrix.rankUnitaryHaar d Goodᶜ ≤
        ENNReal.ofReal (Submodule.bootstrapFailure D q (finrank ℂ Graw)) ∧
      1 - ENNReal.ofReal (Submodule.bootstrapFailure D q (finrank ℂ Graw)) ≤
        Matrix.rankUnitaryHaar d Good ∧
      (∀ U ∈ Good,
        (∀ x, Submodule.IsCloseTo (4 * Delta / alpha ^ 2)
          (Submodule.prodExt (image U) β) (T x)) ∧
        Submodule.IsCloseTo (27 / 2500) (Submodule.prodExt (image U) β) Graw ∧
        Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (output U) β) Graw) ∧
      Matrix.rankUnitaryHaar d
        {U | ¬ Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (output U) β) Graw} ≤
        ENNReal.ofReal (Submodule.bootstrapFailure D q (finrank ℂ Graw)) := by
  intro I W q s alpha sample image output
  let b0 := Matrix.rangeOrthonormalBasis ⟨P, rfl⟩
  let b : OrthonormalBasis (Fin q) ℂ W :=
    b0.map (LinearIsometryEquiv.submoduleMap (Matrix.toEuclideanLin P).range I)
  let Coord := Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s q))
  let sample0 := fun U : Matrix.unitaryGroup (Fin q) ℂ ↦ Submodule.randomSubspace b Coord U
  let image0 : Matrix.unitaryGroup (Fin q) ℂ →
      Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) := fun U ↦
    ⨆ i, (sample0 U).map (A i).toLinearMap
  let output0 : Matrix.unitaryGroup (Fin q) ℂ →
      Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) := fun U ↦
    trimSubspace C xi
      (fun i ↦ (stdOrthonormalBasis ℂ (image0 U) i : EuclideanSpace ℂ (∀ v, Fin (n v)))) m
  let index : Fin (d + 1) := ⟨q, Nat.lt_succ_of_le P.rank_le_width⟩
  let eval := fun U : Matrix.rankUnitaryProduct d ↦ U index
  have hmp : MeasurePreserving eval (Matrix.rankUnitaryHaar d)
      (Matrix.unitaryHaar (Fin q)) := Matrix.measurePreserving_rankUnitary_eval d index
  have hsample (U : Matrix.rankUnitaryProduct d) : sample0 (eval U) = sample U := by
    change Submodule.randomSubspace
      (b0.map (LinearIsometryEquiv.submoduleMap (Matrix.toEuclideanLin P).range I))
      Coord (eval U) = (Submodule.randomSubspace b0 Coord (eval U)).map I.toLinearMap
    exact Submodule.randomSubspace_map_linearIsometryEquiv b0 I Coord (eval U)
  have himage (U : Matrix.rankUnitaryProduct d) : image0 (eval U) = image U :=
    congrArg (fun S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) ↦
      ⨆ i, S.map (A i).toLinearMap) (hsample U)
  have houtput (U : Matrix.rankUnitaryProduct d) : output0 (eval U) = output U :=
    congrArg (fun S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) ↦
      trimSubspace C xi
        (fun i ↦ (stdOrthonormalBasis ℂ S i : EuclideanSpace ℂ (∀ v, Fin (n v)))) m) (himage U)
  obtain ⟨hs, halpha, halpha1, hdim, Good0, hGood0, hBad0, hSuccess0, hEvent0, _hTrue0⟩ :=
    exists_measurable_half_sample_reference_trim_event x0 T A hcard hRawSoft hSoftRaw hA
      hD hDelta hepsilon C hC hxi hepsilonRef0 hepsilonRef hRawRef hRefRaw hRank hbudget b hW hq
  change (∀ U, sample0 U ≤ W ∧ finrank ℂ (sample0 U) = s ∧
    finrank ℂ (image0 U) ≤ q / 2 ∧ finrank ℂ (output0 U) ≤ q / 2) at hdim
  change (∀ U ∈ Good0,
    (∀ x, Submodule.IsCloseTo (4 * Delta / alpha ^ 2)
      (Submodule.prodExt (image0 U) β) (T x)) ∧
    Submodule.IsCloseTo (27 / 2500) (Submodule.prodExt (image0 U) β) Graw ∧
    Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (output0 U) β) Graw) at hEvent0
  let Good := eval ⁻¹' Good0
  have hGood : MeasurableSet Good := hGood0.preimage hmp.measurable
  have hBad : Matrix.rankUnitaryHaar d Goodᶜ ≤
      ENNReal.ofReal (Submodule.bootstrapFailure D q (finrank ℂ Graw)) := by
    calc
      Matrix.rankUnitaryHaar d Goodᶜ = Matrix.unitaryHaar (Fin q) Good0ᶜ := by
        change Matrix.rankUnitaryHaar d (eval ⁻¹' Good0)ᶜ = _
        rw [← Set.preimage_compl]
        exact hmp.measure_preimage hGood0.compl.nullMeasurableSet
      _ ≤ _ := hBad0
  have hSuccess : 1 - ENNReal.ofReal (Submodule.bootstrapFailure D q (finrank ℂ Graw)) ≤
      Matrix.rankUnitaryHaar d Good := by
    rw [show Matrix.rankUnitaryHaar d Good = Matrix.unitaryHaar (Fin q) Good0 from
      hmp.measure_preimage hGood0.nullMeasurableSet]
    exact hSuccess0
  have hEvent (U : Matrix.rankUnitaryProduct d) (hU : U ∈ Good) :
      (∀ x, Submodule.IsCloseTo (4 * Delta / alpha ^ 2)
        (Submodule.prodExt (image U) β) (T x)) ∧
      Submodule.IsCloseTo (27 / 2500) (Submodule.prodExt (image U) β) Graw ∧
      Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (output U) β) Graw := by
    simpa only [himage U, houtput U] using hEvent0 (eval U) hU
  refine ⟨hs, halpha, halpha1, ?_, Good, hGood, hBad, hSuccess, hEvent, ?_⟩
  · intro U
    obtain ⟨hsub, hsDim, hiDim, hoDim⟩ := hdim (eval U)
    have hsRank := congrArg
      (fun S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) ↦ finrank ℂ S) (hsample U)
    have hiRank := congrArg
      (fun S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) ↦ finrank ℂ S) (himage U)
    have hoRank := congrArg
      (fun S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) ↦ finrank ℂ S) (houtput U)
    exact ⟨by simpa only [hsample U] using hsub,
      hsRank.symm.trans hsDim, hiRank ▸ hiDim, hoRank ▸ hoDim⟩
  · exact (measure_mono (μ := Matrix.rankUnitaryHaar d)
      (show {U | ¬ Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (output U) β) Graw} ⊆
        Goodᶜ from fun U hbad hU ↦ hbad (hEvent U hU).2.2)).trans hBad

end Entropy

end RankUnitaryHalfSampling

section StoppedHalfSamplingEvents

/-!
## Joint measurable original-target histories of stopped resampling

The existing finite history event tests every actual stopped state against
one fixed original target. Its projection and rank tests are jointly
measurable in the initial matrix and the entire finite sequence. No
sampling-success, initial viability or positivity hypothesis is required
for measurability. Supporting ALVV, arXiv:1602.08828v2, lines 749–755.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section
namespace Entropy

variable {V ι β : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  [Fintype β] {n : V → ℕ} {d R : ℕ}

/-- The true fixed-original-target event for a finite stopped run: every
state is viable with error .04, and every active next state
has error .015. This supports the repeated-resampling variant for ALVV,
arXiv:1602.08828v2, lines 749–755; it is not an uncountable intersection
over improving spectral targets. -/
def canonicalHalfSamplingRawGood
    (e : Fin d ≃ (∀ v, Fin (n v))) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold : ℕ) (F : ι → Matrix (∀ v, Fin (n v)) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (Graw : Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β))) :
    Set (Fin R → Matrix.rankUnitaryProduct d) :=
  let state := fun U j ↦ canonicalHalfSampleTrimIterate e cuts xi k D threshold F P
    (halfSamplingSeedSequence U) j
  {U | (∀ j : Fin (R + 1), Submodule.IsCloseTo 0.04
      (Submodule.prodExt ((Matrix.toEuclideanLin (state U j.val)).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw) ∧
    ∀ i : Fin R, threshold ≤ (state U i.val).rank → Submodule.IsCloseTo (3 / 200)
      (Submodule.prodExt ((Matrix.toEuclideanLin (state U (i.val + 1))).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw}

/-- The literal original-target history event is jointly measurable in
its initial matrix and finite sequence. It makes no initial viability or
successful-sampling assumption. Supporting ALVV, arXiv:1602.08828v2,
lines 749–755. -/
theorem measurableSet_canonicalHalfSamplingRawGood
    (e : Fin d ≃ (∀ v, Fin (n v))) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold : ℕ) (F : ι → Matrix (∀ v, Fin (n v)) (Fin d) ℂ)
    (Graw : Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β))) :
    MeasurableSet {z : Matrix (Fin d) (Fin d) ℂ ×
        (Fin R → Matrix.rankUnitaryProduct d) |
      z.2 ∈ canonicalHalfSamplingRawGood e cuts xi k D threshold F z.1 Graw} := by
  let input := fun z : Matrix (Fin d) (Fin d) ℂ ×
      (Fin R → Matrix.rankUnitaryProduct d) ↦ (z.1, halfSamplingSeedSequence z.2)
  have hInput : Measurable input := measurable_fst.prodMk
    ((measurable_halfSamplingSeedSequence d R).comp measurable_snd)
  let state := fun z : Matrix (Fin d) (Fin d) ℂ ×
      (Fin R → Matrix.rankUnitaryProduct d) ↦ fun j ↦
    canonicalHalfSampleTrimIterate e cuts xi k D threshold F z.1
      (halfSamplingSeedSequence z.2) j
  have hstate (j : ℕ) : Measurable (fun z ↦ state z j) :=
    (measurable_canonicalHalfSampleTrimIterate e cuts xi k D threshold F j).comp
      (f := input) hInput
  let close := fun delta z j ↦ Submodule.IsCloseTo delta
    (Submodule.prodExt ((Matrix.toEuclideanLin (state z j)).range.map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw
  have hclose (delta : ℝ) (j : ℕ) : MeasurableSet {z | close delta z j} :=
    Submodule.measurableSet_isCloseTo_prodExt_map_range e (fun z ↦ state z j)
      (hstate j) delta Graw
  have hactive (j : ℕ) : MeasurableSet {z | threshold ≤ (state z j).rank} :=
    measurableSet_le measurable_const (Matrix.measurable_rank.comp (hstate j))
  change MeasurableSet {z | (∀ j : Fin (R + 1), close 0.04 z j.val) ∧
    ∀ i : Fin R, threshold ≤ (state z i.val).rank → close (3 / 200) z (i.val + 1)}
  have h0 : MeasurableSet {z | ∀ j : Fin (R + 1), close 0.04 z j.val} := by
    have he : {z | ∀ j : Fin (R + 1), close 0.04 z j.val} =
        ⋂ j : Fin (R + 1), {z | close 0.04 z j.val} := by ext z; simp
    exact Eq.mpr (congrArg MeasurableSet he)
      (MeasurableSet.iInter (fun j : Fin (R + 1) ↦ hclose 0.04 j.val))
  have h1 : MeasurableSet {z | ∀ i : Fin R, threshold ≤ (state z i.val).rank →
      close (3 / 200) z (i.val + 1)} := by
    have he : {z | ∀ i : Fin R, threshold ≤ (state z i.val).rank →
        close (3 / 200) z (i.val + 1)} = ⋂ i : Fin R,
        {z | threshold ≤ (state z i.val).rank → close (3 / 200) z (i.val + 1)} := by
      ext z; simp
    exact Eq.mpr (congrArg MeasurableSet he)
      (MeasurableSet.iInter (fun i : Fin R ↦
        (hactive i.val).imp (hclose (3 / 200) (i.val + 1))))
  exact h0.inter h1

end Entropy

end

end StoppedHalfSamplingEvents

section StoppedHalfSamplingProbability

open MeasureTheory
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section
namespace Entropy
variable {V ι β : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  [Fintype β] {n : V → ℕ} {d R : ℕ}

private theorem joint_failure_le_of_step
    (e : Fin d ≃ (∀ v, Fin (n v))) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold : ℕ) (F : ι → Matrix (∀ v, Fin (n v)) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (Graw : Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β))) (beta : ℝ≥0∞)
    (hInitial : Submodule.IsCloseTo 0.04
      (Submodule.prodExt ((Matrix.toEuclideanLin P).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw)
    (hStep : ∀ Q : Matrix (Fin d) (Fin d) ℂ,
      Submodule.IsCloseTo 0.04
        (Submodule.prodExt ((Matrix.toEuclideanLin Q).range.map
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw →
      threshold ≤ Q.rank →
      Matrix.rankUnitaryHaar d {u | ¬ Submodule.IsCloseTo (3 / 200)
        (Submodule.prodExt ((Matrix.toEuclideanLin
          (canonicalHalfSampleTrimMatrix e cuts xi k D threshold F Q u)).range.map
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw} ≤ beta) :
    let state := fun (U : Fin R → Matrix.rankUnitaryProduct d) j ↦
      canonicalHalfSampleTrimIterate e cuts xi k D threshold F P (halfSamplingSeedSequence U) j
    let good := {U | (∀ j : Fin (R + 1), Submodule.IsCloseTo 0.04
      (Submodule.prodExt ((Matrix.toEuclideanLin (state U j.val)).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw) ∧
      ∀ i : Fin R, threshold ≤ (state U i.val).rank → Submodule.IsCloseTo (3 / 200)
        (Submodule.prodExt ((Matrix.toEuclideanLin (state U (i.val + 1))).range.map
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw}
    MeasurableSet good ∧
      Measure.pi (fun _ : Fin R ↦ Matrix.rankUnitaryHaar d) goodᶜ ≤ (R : ℝ≥0∞) * beta := by
  intro state good
  let close := fun delta U j ↦ Submodule.IsCloseTo delta
    (Submodule.prodExt ((Matrix.toEuclideanLin (state U j)).range.map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw
  have hclose (delta : ℝ) (j : ℕ) : MeasurableSet {U | close delta U j} :=
    Submodule.measurableSet_isCloseTo_prodExt_map_range e (fun U ↦ state U j)
      (measurable_canonicalHalfSampleTrimIterate_finite_seed e cuts xi k D threshold F P j)
      delta Graw
  have hactive (j : ℕ) : MeasurableSet {U | threshold ≤ (state U j).rank} :=
    measurableSet_le measurable_const (Matrix.measurable_rank.comp
      (measurable_canonicalHalfSampleTrimIterate_finite_seed e cuts xi k D threshold F P j))
  have hgood : MeasurableSet good := by
    let input := fun U : Fin R → Matrix.rankUnitaryProduct d ↦ (P, U)
    have hInput : Measurable input := measurable_const.prodMk measurable_id
    exact (measurableSet_canonicalHalfSamplingRawGood (R := R)
      e cuts xi k D threshold F Graw).preimage (f := input) hInput
  let bad := fun i : Fin R ↦ {U | close 0.04 U i.val ∧
    threshold ≤ (state U i.val).rank ∧ ¬ close (3 / 200) U (i.val + 1)}
  have hbad (i : Fin R) : MeasurableSet (bad i) :=
    (hclose 0.04 i.val).inter ((hactive i.val).inter (hclose (3 / 200) (i.val + 1)).compl)
  have hinput (U : Fin R → Matrix.rankUnitaryProduct d) (i : Fin R)
      (u : Matrix.rankUnitaryProduct d) : state (Function.update U i u) i.val = state U i.val :=
    canonicalHalfSampleTrimIterate_update_input e cuts xi k D threshold F P U i u
  have hnext (U : Fin R → Matrix.rankUnitaryProduct d) (i : Fin R)
      (u : Matrix.rankUnitaryProduct d) :
      state (Function.update U i u) (i.val + 1) =
        canonicalHalfSampleTrimMatrix e cuts xi k D threshold F (state U i.val) u :=
    canonicalHalfSampleTrimIterate_update_next e cuts xi k D threshold F P U i u
  have hsection (i : Fin R) (U : Fin R → Matrix.rankUnitaryProduct d) :
      Matrix.rankUnitaryHaar d {u | Function.update U i u ∈ bad i} ≤ beta := by
    have hmem (u : Matrix.rankUnitaryProduct d)
        (hu : Function.update U i u ∈ bad i) :
        close 0.04 U i.val ∧ threshold ≤ (state U i.val).rank ∧
        ¬ Submodule.IsCloseTo (3 / 200)
          (Submodule.prodExt ((Matrix.toEuclideanLin
            (canonicalHalfSampleTrimMatrix e cuts xi k D threshold F (state U i.val) u)).range.map
            (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw := by
      simpa only [bad, Set.mem_ofPred_eq, close, hinput, hnext] using hu
    by_cases hp : close 0.04 U i.val ∧ threshold ≤ (state U i.val).rank
    · exact (measure_mono (fun u hu ↦ (hmem u hu).2.2)).trans
        (hStep (state U i.val) hp.1 hp.2)
    · have he : {u | Function.update U i u ∈ bad i} = ∅ := by
        ext u
        exact ⟨fun hu ↦ hp ⟨(hmem u hu).1, (hmem u hu).2.1⟩, False.elim⟩
      rw [he, measure_empty]
      exact bot_le
  have hunion := Measure.pi_biUnion_list_le_of_update_sections
    (fun _ : Fin R ↦ Matrix.rankUnitaryHaar d) (List.finRange R) id bad beta
    (fun i _ ↦ hbad i) (fun i _ U ↦ hsection i U)
  have hinclusion : goodᶜ ⊆ ⋃ i ∈ List.finRange R, bad i := by
    intro U hU
    by_contra hnotUnion
    have hnot (i : Fin R) : U ∉ bad i := by
      intro hi
      apply hnotUnion
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨by simp, hi⟩⟩
    have hall (j : ℕ) : j ≤ R → close 0.04 U j := by
      induction j with
      | zero => intro _; exact hInitial
      | succ j ih =>
        intro hj
        have hjR : j < R := by omega
        have hprevious := ih (by omega)
        by_cases ha : threshold ≤ (state U j).rank
        · have hnew : close (3 / 200) U (j + 1) := by
            by_contra hn
            exact hnot ⟨j, hjR⟩ ⟨hprevious, ha, hn⟩
          exact hnew.of_le (by norm_num)
        · have he : state U (j + 1) = state U j := by
            change canonicalHalfSampleTrimMatrix e cuts xi k D threshold F
              (state U j) (halfSamplingSeedSequence U j) = state U j
            simp only [canonicalHalfSampleTrimMatrix, ite_eq_right ha]
          change Submodule.IsCloseTo 0.04
            (Submodule.prodExt ((Matrix.toEuclideanLin (state U (j + 1))).range.map
              (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw
          rw [he]
          exact hprevious
    apply hU
    refine ⟨fun j ↦ hall j.val (Nat.le_of_lt_succ j.isLt), ?_⟩
    intro i ha
    by_contra hn
    exact hnot i ⟨hall i.val (Nat.le_of_lt i.isLt), ha, hn⟩
  refine ⟨hgood, (measure_mono hinclusion).trans ?_⟩
  simpa only [List.length_finRange] using hunion

private theorem active_native_half_trim_eq
    (e : Fin d ≃ (∀ v, Fin (n v))) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold : ℕ)
    (A : ι → EuclideanSpace ℂ (∀ v, Fin (n v)) →L[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v)))
    (P : Matrix (Fin d) (Fin d) ℂ) (U : Matrix.rankUnitaryProduct d)
    (hactive : threshold ≤ P.rank) :
    let sample := (Matrix.randomRangeSubspace P (P.rank / (2 * D ^ 2)) U).map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap
    let image : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) :=
      ⨆ i, sample.map (A i).toLinearMap
    (Matrix.toEuclideanLin
      (canonicalHalfSampleTrimMatrix e cuts xi k D threshold
        (nativeFamilyMatrix e A) P U)).range.map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap =
    trimSubspace cuts xi
      (fun i ↦ (stdOrthonormalBasis ℂ image i : EuclideanSpace ℂ (∀ v, Fin (n v)))) k := by
  intro sample image
  let S := Matrix.randomRangeSubspace P (P.rank / (2 * D ^ 2)) U
  let Q := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm S.starProjection
  have hRange : (Matrix.toEuclideanLin Q).range = S := by
    change ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
      ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm S.starProjection)).toLinearMap.range = S
    rw [StarAlgEquiv.apply_symm_apply, Submodule.range_starProjection]
  have ht := nativeFamilyTrimSpace_eq_trimSubspace e cuts xi k A Q
  have hs := map_range_canonicalHalfSampleTrimMatrix_of_active e cuts xi k D threshold
    (nativeFamilyMatrix e A) P U hactive
  have himage : (⨆ i, ((Matrix.toEuclideanLin Q).range.map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap).map (A i).toLinearMap) = image :=
    congrArg (fun W : Submodule ℂ (EuclideanSpace ℂ (Fin d)) ↦
      ⨆ i, (W.map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap).map
        (A i).toLinearMap) hRange
  exact hs.trans (ht.trans (congrArg
    (fun W : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) ↦ trimSubspace cuts xi
      (fun i ↦ (stdOrthonormalBasis ℂ W i : EuclideanSpace ℂ (∀ v, Fin (n v)))) k) himage))

/-- The actual stopped-run probability for a fixed coefficient satisfying
only the explicit scalar sampling threshold. Consequently a physical caller
may choose this coefficient before its chain-dependent carrier types.
There is no one-step success or section-bound premise. Supporting the
repeated-resampling variant for ALVV, arXiv:1602.08828v2, lines 749–755. -/
theorem canonicalHalfSampleTrimIterate_joint_probability_of_threshold
    {X : Type*} (D a K : ℕ) (hD : 2 ≤ D) (eta : ℝ) (hK : 1 ≤ K)
    (hThreshold : ∀ r N Q : ℕ, K * (r + 1) * (N + 2) ^ 2 ≤ Q →
      4 * D ^ 2 ≤ Q ∧ Submodule.bootstrapFailure D Q r ≤ eta / ((N : ℝ) + 2) ^ a) :
    ∀ (N r d rounds : ℕ) (e : Fin d ≃ (∀ v, Fin (n v)))
      (k bRef : ℕ) (Delta epsilon epsilonRef xi : ℝ)
      (Graw Rref : Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β)))
      (_x0 : X) (T : X → Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β)))
      (A : ι → EuclideanSpace ℂ (∀ v, Fin (n v)) →L[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v)))
      (P : Matrix (Fin d) (Fin d) ℂ),
      Fintype.card ι ≤ D ^ 2 →
      (∀ x, Submodule.IsCloseTo epsilon Graw (T x)) →
      (∀ x, Submodule.IsCloseTo (1 / 200) (T x) Graw) →
      (∀ x delta, delta < 1 → ∀ S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))),
        Submodule.IsCloseTo delta (Submodule.prodExt S β) (T x) →
        Submodule.IsCloseTo (Delta / (1 - delta) ^ 2)
          (Submodule.prodExt (⨆ i, S.map (A i).toLinearMap) β) (T x)) →
      (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 →
      epsilon ≤ ((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2 / 100 →
      ∀ cuts : ℕ → Finset V, Monotone cuts → 0 < xi →
      0 ≤ epsilonRef → epsilonRef ≤ 1 / 100000 →
      Submodule.IsCloseTo epsilonRef Graw Rref →
      Submodule.IsCloseTo epsilonRef Rref Graw →
      (∀ t ∈ Rref, ∀ j < k,
        Matrix.schmidtRank (WithLp.ofLp (cutEnvVector (cuts j) t)) ≤ bRef) →
      xi * Real.sqrt ((k : ℝ) * (bRef : ℝ)) ≤ 1 / 1000 →
      Module.finrank ℂ Graw ≤ r → d ≤ 2 ^ rounds →
      Submodule.IsCloseTo 0.04
        (Submodule.prodExt ((Matrix.toEuclideanLin P).range.map
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw →
      let threshold := K * (r + 1) * (N + 2) ^ 2
      let F := nativeFamilyMatrix e A
      let good := canonicalHalfSamplingRawGood (R := rounds) e cuts xi k D threshold F P Graw
      let state := fun U j ↦ canonicalHalfSampleTrimIterate e cuts xi k D threshold F P
        (halfSamplingSeedSequence (R := rounds) U) j
      MeasurableSet good ∧
      Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar d) goodᶜ ≤
        (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((N : ℝ) + 2) ^ a) ∧
      (∀ U j, (state U j).rank ≤ P.rank) ∧
      ∀ U, (state U rounds).rank < threshold := by
  intro N r d rounds e k bRef Delta epsilon epsilonRef xi Graw Rref x0 T A P
    hcard hRawSoft hSoftRaw hA hDelta hepsilon cuts hcuts hxi hepsilonRef0 hepsilonRef
    hRawRef hRefRaw hRank hbudget hdim hrounds hInitial threshold F good state
  have hStep (Q : Matrix (Fin d) (Fin d) ℂ)
      (hQ : Submodule.IsCloseTo 0.04
        (Submodule.prodExt ((Matrix.toEuclideanLin Q).range.map
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw)
      (hactive : threshold ≤ Q.rank) :
      Matrix.rankUnitaryHaar d {u | ¬ Submodule.IsCloseTo (3 / 200)
        (Submodule.prodExt ((Matrix.toEuclideanLin
          (canonicalHalfSampleTrimMatrix e cuts xi k D threshold F Q u)).range.map
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw} ≤
        ENNReal.ofReal (eta / ((N : ℝ) + 2) ^ a) := by
    have hcap : K * (Module.finrank ℂ Graw + 1) * (N + 2) ^ 2 ≤ Q.rank :=
      (Nat.mul_le_mul_right ((N + 2) ^ 2)
        (Nat.mul_le_mul_left K (Nat.add_le_add_right hdim 1))).trans hactive
    obtain ⟨hq, hfailure⟩ := hThreshold (Module.finrank ℂ Graw) N Q.rank hcap
    obtain ⟨_, _, _, _, Good, hGood, hBad, hSuccess, hResult, hTrue⟩ :=
      exists_measurable_randomRangeSubspace_half_trim_event e Q x0 T A hcard
        hRawSoft hSoftRaw hA hD hDelta hepsilon cuts hcuts hxi hepsilonRef0 hepsilonRef
        hRawRef hRefRaw hRank hbudget hQ hq
    have hOutput (u : Matrix.rankUnitaryProduct d) :=
      active_native_half_trim_eq e cuts xi k D threshold A Q u hactive
    have hmeasure := hTrue.trans (ENNReal.ofReal_le_ofReal hfailure)
    simpa only [F, hOutput] using hmeasure
  obtain ⟨hgood, hfailure⟩ := joint_failure_le_of_step (R := rounds)
    e cuts xi k D threshold F P Graw (ENNReal.ofReal (eta / ((N : ℝ) + 2) ^ a))
      hInitial hStep
  have hthreshold : 2 ≤ threshold := by
    have hr : 1 ≤ r + 1 := by omega
    have hp : 1 ≤ K * (r + 1) := Nat.mul_le_mul hK hr
    have hN2 : 2 ≤ N + 2 := by omega
    have hN : 2 ≤ (N + 2) ^ 2 := hN2.trans (le_self_pow₀ (by omega) (by decide))
    exact Nat.mul_le_mul hp hN
  refine ⟨hgood, hfailure, ?_, ?_⟩
  · intro U j
    exact rank_canonicalHalfSampleTrimIterate_le e cuts xi k D threshold F hcard P
      (halfSamplingSeedSequence U) j
  · intro U
    exact rank_canonicalHalfSampleTrimIterate_lt e cuts xi k D threshold F hcard P
      (halfSamplingSeedSequence U) rounds hthreshold (P.rank_le_width.trans hrounds)


/-- One polynomial stopping coefficient, chosen before length, target
rank and ambient dimension, controls the true original-target failures of
the actual stopped half-resampling run. The family and reference hypotheses
are those of the proved fixed-input sampling theorem; no success or
section estimate is assumed. This is a repeated-resampling
auxiliary for ALVV, arXiv:1602.08828v2, lines 749–755, not the printed
sample-once loop or a running-time assertion. -/
theorem exists_canonicalHalfSampleTrimIterate_joint_probability
    {X : Type*} (D a : ℕ) (hD : 2 ≤ D) (eta : ℝ) (heta : 0 < eta) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (N r d rounds : ℕ) (e : Fin d ≃ (∀ v, Fin (n v)))
      (k bRef : ℕ) (Delta epsilon epsilonRef xi : ℝ)
      (Graw Rref : Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β)))
      (_x0 : X) (T : X → Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β)))
      (A : ι → EuclideanSpace ℂ (∀ v, Fin (n v)) →L[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v)))
      (P : Matrix (Fin d) (Fin d) ℂ),
      Fintype.card ι ≤ D ^ 2 →
      (∀ x, Submodule.IsCloseTo epsilon Graw (T x)) →
      (∀ x, Submodule.IsCloseTo (1 / 200) (T x) Graw) →
      (∀ x delta, delta < 1 → ∀ S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))),
        Submodule.IsCloseTo delta (Submodule.prodExt S β) (T x) →
        Submodule.IsCloseTo (Delta / (1 - delta) ^ 2)
          (Submodule.prodExt (⨆ i, S.map (A i).toLinearMap) β) (T x)) →
      (D : ℝ) ^ 12 * Delta ≤ 1 / 100000 →
      epsilon ≤ ((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2 / 100 →
      ∀ cuts : ℕ → Finset V, Monotone cuts → 0 < xi →
      0 ≤ epsilonRef → epsilonRef ≤ 1 / 100000 →
      Submodule.IsCloseTo epsilonRef Graw Rref →
      Submodule.IsCloseTo epsilonRef Rref Graw →
      (∀ t ∈ Rref, ∀ j < k,
        Matrix.schmidtRank (WithLp.ofLp (cutEnvVector (cuts j) t)) ≤ bRef) →
      xi * Real.sqrt ((k : ℝ) * (bRef : ℝ)) ≤ 1 / 1000 →
      Module.finrank ℂ Graw ≤ r → d ≤ 2 ^ rounds →
      Submodule.IsCloseTo 0.04
        (Submodule.prodExt ((Matrix.toEuclideanLin P).range.map
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw →
      let threshold := K * (r + 1) * (N + 2) ^ 2
      let F := nativeFamilyMatrix e A
      let good := canonicalHalfSamplingRawGood (R := rounds) e cuts xi k D threshold F P Graw
      let state := fun U j ↦ canonicalHalfSampleTrimIterate e cuts xi k D threshold F P
        (halfSamplingSeedSequence (R := rounds) U) j
      MeasurableSet good ∧
      Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar d) goodᶜ ≤
        (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((N : ℝ) + 2) ^ a) ∧
      (∀ U j, (state U j).rank ≤ P.rank) ∧
      ∀ U, (state U rounds).rank < threshold  := by
  obtain ⟨K, hK, hThreshold⟩ :=
    Submodule.exists_bootstrapFailure_polynomial_threshold D a hD eta heta
  exact ⟨K, hK,
    canonicalHalfSampleTrimIterate_joint_probability_of_threshold D a K hD eta hK hThreshold⟩

end Entropy

end

end StoppedHalfSamplingProbability
