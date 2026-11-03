/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.RankUnitaryProductHaar
import QICLean.Analysis.ViableHalfSamplingTrimming

/-!
# A product Haar law for the actual half-sample, image and reference trim

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
**Scope restriction (one fixed input):** This is a half-dimensional
resampling step, not an identification with the sample-once loop or an
adaptive joint law; see `docs/paper-gaps/alvv16_bootstrap_constants.tex`.
The event is chosen at one fixed input matrix; no measurable choice of
these events as that matrix varies is asserted.
-/

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
    (e : Fin d ≃ SiteConfig n) (P : Matrix (Fin d) (Fin d) ℂ)
    {D m bRef : ℕ} {Delta epsilon epsilonRef xi : ℝ}
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
        Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) := fun U ↦
      ⨆ i, (sample U).map (A i).toLinearMap
    let output : Matrix.rankUnitaryProduct d →
        Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) := fun U ↦
      trimSubspace C xi
        (fun i ↦ (stdOrthonormalBasis ℂ (image U) i : EuclideanSpace ℂ (SiteConfig n))) m
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
      Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) := fun U ↦
    ⨆ i, (sample0 U).map (A i).toLinearMap
  let output0 : Matrix.unitaryGroup (Fin q) ℂ →
      Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) := fun U ↦
    trimSubspace C xi
      (fun i ↦ (stdOrthonormalBasis ℂ (image0 U) i : EuclideanSpace ℂ (SiteConfig n))) m
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
    congrArg (fun S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) ↦
      ⨆ i, S.map (A i).toLinearMap) (hsample U)
  have houtput (U : Matrix.rankUnitaryProduct d) : output0 (eval U) = output U :=
    congrArg (fun S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) ↦
      trimSubspace C xi
        (fun i ↦ (stdOrthonormalBasis ℂ S i : EuclideanSpace ℂ (SiteConfig n))) m) (himage U)
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
      (fun S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) ↦ finrank ℂ S) (hsample U)
    have hiRank := congrArg
      (fun S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) ↦ finrank ℂ S) (himage U)
    have hoRank := congrArg
      (fun S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) ↦ finrank ℂ S) (houtput U)
    exact ⟨by simpa only [hsample U] using hsub,
      hsRank.symm.trans hsDim, hiRank ▸ hiDim, hoRank ▸ hoDim⟩
  · exact (measure_mono (μ := Matrix.rankUnitaryHaar d)
      (show {U | ¬ Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (output U) β) Graw} ⊆
        Goodᶜ from fun U hbad hU ↦ hbad (hEvent U hU).2.2)).trans hBad

end Entropy
