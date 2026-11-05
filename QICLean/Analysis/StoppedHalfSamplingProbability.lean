/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.RankUnitaryHalfSampling
import QICLean.Analysis.NativeFamilyImageCoordinates
import QICLean.Analysis.StoppedHalfSamplingRank
import QICLean.Analysis.BootstrapFailureParameters
import QICLean.Analysis.StoppedHalfSamplingEvents
import QICLean.Analysis.FiniteProductUnionProbability
import QICLean.Analysis.ViableSubspaceOrder

/-!
# Joint original-target probability for stopped half-dimensional resampling

A finite product of the actual rank-unitary Haar laws supplies fresh seeds
for the existing stopped iteration. Guarded true failures depend on the
original target alone. This supports the repeated-resampling variant
associated with ALVV, arXiv:1602.08828v2, lines 749–755.
No measurable choice of auxiliary success events is used.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section
namespace Entropy
variable {V ι β : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  [Fintype β] {n : V → ℕ} {d R : ℕ}

private theorem joint_failure_le_of_step
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold : ℕ) (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (Graw : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β))) (beta : ℝ≥0∞)
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
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold : ℕ)
    (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n))
    (P : Matrix (Fin d) (Fin d) ℂ) (U : Matrix.rankUnitaryProduct d)
    (hactive : threshold ≤ P.rank) :
    let sample := (Matrix.randomRangeSubspace P (P.rank / (2 * D ^ 2)) U).map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap
    let image : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) :=
      ⨆ i, sample.map (A i).toLinearMap
    (Matrix.toEuclideanLin
      (canonicalHalfSampleTrimMatrix e cuts xi k D threshold
        (nativeFamilyMatrix e A) P U)).range.map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap =
    trimSubspace cuts xi
      (fun i ↦ (stdOrthonormalBasis ℂ image i : EuclideanSpace ℂ (SiteConfig n))) k := by
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
    (fun W : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) ↦ trimSubspace cuts xi
      (fun i ↦ (stdOrthonormalBasis ℂ W i : EuclideanSpace ℂ (SiteConfig n))) k) himage))

/-- The actual stopped-run probability for a fixed coefficient satisfying
only the explicit scalar sampling threshold. Consequently a physical caller
may choose this coefficient before its chain-dependent carrier types.
There is no one-step success or section-bound premise. Supporting the
repeated-resampling variant for ALVV, arXiv:1602.08828v2, lines 749–755. -/
theorem canonicalHalfSampleTrimIterate_joint_probability_of_threshold
    {X : Type*} (D a K : ℕ) (hD : 2 ≤ D) (eta : ℝ) (hK : 1 ≤ K)
    (hThreshold : ∀ r N Q : ℕ, K * (r + 1) * (N + 2) ^ 2 ≤ Q →
      4 * D ^ 2 ≤ Q ∧ Submodule.bootstrapFailure D Q r ≤ eta / ((N : ℝ) + 2) ^ a) :
    ∀ (N r d rounds : ℕ) (e : Fin d ≃ SiteConfig n)
      (k bRef : ℕ) (Delta epsilon epsilonRef xi : ℝ)
      (Graw Rref : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β)))
      (_x0 : X) (T : X → Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β)))
      (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n))
      (P : Matrix (Fin d) (Fin d) ℂ),
      Fintype.card ι ≤ D ^ 2 →
      (∀ x, Submodule.IsCloseTo epsilon Graw (T x)) →
      (∀ x, Submodule.IsCloseTo (1 / 200) (T x) Graw) →
      (∀ x delta, delta < 1 → ∀ S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)),
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
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (N r d rounds : ℕ) (e : Fin d ≃ SiteConfig n)
      (k bRef : ℕ) (Delta epsilon epsilonRef xi : ℝ)
      (Graw Rref : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β)))
      (_x0 : X) (T : X → Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β)))
      (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n))
      (P : Matrix (Fin d) (Fin d) ℂ),
      Fintype.card ι ≤ D ^ 2 →
      (∀ x, Submodule.IsCloseTo epsilon Graw (T x)) →
      (∀ x, Submodule.IsCloseTo (1 / 200) (T x) Graw) →
      (∀ x delta, delta < 1 → ∀ S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)),
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
