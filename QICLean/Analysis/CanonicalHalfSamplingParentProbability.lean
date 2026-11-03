/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CanonicalHalfSamplingParentProperties
import QICLean.Analysis.StoppedHalfSamplingProbability

/-!
# True probability for the complete stopped-resampling native parent

The same finite product Haar law drives the existing stopped iteration.
Its true original-target event supplies terminal viability for the same
complete native parent. The last untrimmed full-family image retains its
quantitative error for every improving target on that one event.

Supporting ALVV, arXiv:1602.08828v2, the resampling description at
lines 749–755 and reference trimming at lines 1801–1813.
**Local fix (repeated sampling and terminal amplification):** The operation
is the corrected repeated-resampling parent, not the sample-once Figure
`fig:merge-prime`, lines 1664–1673; see
`docs/paper-gaps/alvv16_bootstrap_constants.tex`. No runtime estimate is
asserted. The stopping coefficient is supplied with its explicit numerical
threshold bound; the scalar choice can therefore precede chain-carrier types.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section
namespace Entropy

variable {V ι β : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  [Fintype β] {n : V → ℕ} {d : ℕ}

/-- The actual complete parent has the stated true original-target failure
bound. One fixed original-target event also certifies every improving target
for its same last untrimmed image. The numerical threshold premise is
independent of the carrier and supplied by the scalar sampling theorem;
there is no section or successful-sampling premise. This is a corrected
resampling auxiliary for ALVV, arXiv:1602.08828v2, lines 749–755. -/
theorem canonicalHalfSamplingParent_joint_probability_of_threshold
    {X : Type*} (D a K : ℕ) (hD : 2 ≤ D) (eta : ℝ) (hK : 1 ≤ K)
    (hThreshold : ∀ r N Q : ℕ, K * (r + 1) * (N + 2) ^ 2 ≤ Q →
      4 * D ^ 2 ≤ Q ∧
      Submodule.bootstrapFailure D Q r ≤ eta / ((N : ℝ) + 2) ^ a) :
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
      let parent := fun U : Fin rounds → Matrix.rankUnitaryProduct d ↦
        canonicalHalfSamplingParent e cuts xi k D threshold rounds A P (halfSamplingSeedSequence U)
      let image := fun U : Fin rounds → Matrix.rankUnitaryProduct d ↦
        (Matrix.toEuclideanLin (Matrix.familySupportProj
          (fun i ↦ F i * state U rounds))).range
      MeasurableSet good ∧
      Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar d) goodᶜ ≤
        (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((N : ℝ) + 2) ^ a) ∧
      MeasurableSet {U | Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (parent U) β) Graw} ∧
      Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar d)
        {U | ¬ Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (parent U) β) Graw} ≤
        (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((N : ℝ) + 2) ^ a) ∧
      (∀ U ∈ good,
        (∀ x, Submodule.IsCloseTo (Delta / (91 / 100 : ℝ) ^ 2)
          (Submodule.prodExt (image U) β) (T x)) ∧
        Submodule.IsCloseTo (27 / 2500) (Submodule.prodExt (image U) β) Graw ∧
        Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (parent U) β) Graw) ∧
      (∀ U j, (state U j).rank ≤ P.rank) ∧
      ∀ U, (state U rounds).rank < threshold ∧
        Module.finrank ℂ (image U) ≤ Fintype.card ι * (state U rounds).rank ∧
        Module.finrank ℂ (parent U) ≤ Fintype.card ι * (state U rounds).rank := by
  intro N r d rounds e k bRef Delta epsilon epsilonRef xi Graw Rref x0 T A P
    hcard hRawSoft hSoftRaw hA hDelta hepsilon cuts hcuts hxi hepsilonRef0 hepsilonRef
    hRawRef hRefRaw hRank hbudget hdim hrounds hInitial threshold F good state parent image
  obtain ⟨hGood, hFailure, hRankInitial, hStop⟩ :=
    canonicalHalfSampleTrimIterate_joint_probability_of_threshold
      (X := X) D a K hD eta hK hThreshold N r d rounds e k bRef
      Delta epsilon epsilonRef xi Graw Rref x0 T A P hcard hRawSoft hSoftRaw hA hDelta
      hepsilon cuts hcuts hxi hepsilonRef0 hepsilonRef hRawRef hRefRaw hRank hbudget
      hdim hrounds hInitial
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hDsq : (4 : ℝ) ≤ (D : ℝ) ^ 2 := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (D : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hDreal 2
  have hfrac0 : (0 : ℝ) ≤ (3 / 100) / (D : ℝ) ^ 2 := by positivity
  have hfrac : (3 / 100 : ℝ) / (D : ℝ) ^ 2 ≤ 1 / 2 :=
    (div_le_iff₀ (by linarith only [hDsq] : (0 : ℝ) < (D : ℝ) ^ 2)).mpr
      (by nlinarith only [hDsq])
  have hepsilonSmall : epsilon ≤ 1 / 200 := by
    calc
      epsilon ≤ ((3 / 100 : ℝ) / (D : ℝ) ^ 2) ^ 2 / 100 := hepsilon
      _ ≤ (1 / 2 : ℝ) ^ 2 / 100 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hfrac0 hfrac 2) (by norm_num)
      _ ≤ 1 / 200 := by norm_num
  have hRawSoftSmall (x) : Submodule.IsCloseTo (1 / 200) Graw (T x) :=
    (hRawSoft x).of_le hepsilonSmall
  have hOnGood (U) (hU : U ∈ good) :
      (∀ x, Submodule.IsCloseTo (Delta / (91 / 100 : ℝ) ^ 2)
        (Submodule.prodExt (image U) β) (T x)) ∧
      Submodule.IsCloseTo (27 / 2500) (Submodule.prodExt (image U) β) Graw ∧
      Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (parent U) β) Graw := by
    have hQ : Submodule.IsCloseTo 0.04
        (Submodule.prodExt ((Matrix.toEuclideanLin (state U rounds)).range.map
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw :=
      hU.1 ⟨rounds, Nat.lt_succ_self rounds⟩
    exact isCloseTo_nativeFamilyTrimSpace x0 T A hcard hRawSoftSmall hSoftRaw hA hD hDelta
      cuts hcuts hxi hepsilonRef0 hepsilonRef hRawRef hRefRaw hRank hbudget e (state U rounds) hQ
  have hParentMeas : MeasurableSet
      {U | Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (parent U) β) Graw} := by
    let input := fun U : Fin rounds → Matrix.rankUnitaryProduct d ↦
      (P, halfSamplingSeedSequence U)
    have hInput : Measurable input :=
      measurable_const.prodMk (measurable_halfSamplingSeedSequence d rounds)
    exact (measurableSet_isCloseTo_prodExt_canonicalHalfSamplingParent
      (V := V) (β := β) (ι := ι) (n := n) (d := d)
      e cuts xi k D threshold rounds A (3 / 200) Graw).preimage (f := input) hInput
  have hBad : Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar d)
      {U | ¬ Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (parent U) β) Graw} ≤
      (rounds : ℝ≥0∞) * ENNReal.ofReal (eta / ((N : ℝ) + 2) ^ a) :=
    (measure_mono (μ := Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar d))
      (show {U | ¬ Submodule.IsCloseTo (3 / 200) (Submodule.prodExt (parent U) β) Graw}
          ⊆ goodᶜ from fun U hU hUGood ↦ hU (hOnGood U hUGood).2.2)).trans hFailure
  refine ⟨hGood, hFailure, hParentMeas, hBad, hOnGood, hRankInitial, ?_⟩
  intro U
  have hdim := finrank_nativeFamily_image_trim_le e cuts xi k A (state U rounds)
  exact ⟨hStop U, hdim.1, hdim.2⟩

end Entropy
