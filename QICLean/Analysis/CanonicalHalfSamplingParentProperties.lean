/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CanonicalHalfSamplingParent
import QICLean.Analysis.TerminalFamilyReferenceTrimming
import QICLean.Analysis.StoppedHalfSamplingRank

/-!
# Dimensions and terminal improvement for the same native parent

The actual last untrimmed family image and the actual native parent output
are retained. Dimension statements hold for every seed, independently of
viability. The terminal improvement will use the original target and its
same reference; the stopped-loop success event is a separate input to the
later probability application.

This supports ALVV, arXiv:1602.08828v2, the resampling description at
lines 749–755 and the reference argument at lines 1801–1813.
This module treats a repeated-resampling variant of the merge procedure
sketched at arXiv:1602.08828v2, lines 711–755; Figure `fig:merge-prime` and
Theorem `t:alg1` are not formalized here. See
`docs/paper-gaps/alvv16_bootstrap_constants.tex`.
-/

open Module
open scoped Matrix.Norms.L2Operator

namespace Entropy

variable {V β X ι : Type*} [Fintype V] [DecidableEq V]
  [Fintype β] [Fintype ι] {n : V → ℕ} {d : ℕ}

/-- The last full image and its same actual native trim have unconditional
cardinality-times-rank bounds for an arbitrary coordinate matrix. Supporting
ALVV, arXiv:1602.08828v2, Lemma `l:er`, lines 597–622. -/
theorem finrank_nativeFamily_image_trim_le
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ) (k : ℕ)
    (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n))
    (Q : Matrix (Fin d) (Fin d) ℂ) :
    let Y := (Matrix.toEuclideanLin (Matrix.familySupportProj
      (fun i ↦ nativeFamilyMatrix e A i * Q))).range
    finrank ℂ Y ≤ Fintype.card ι * Q.rank ∧
      finrank ℂ (nativeFamilyTrimSpace e cuts xi k A Q) ≤ Fintype.card ι * Q.rank := by
  intro Y
  let I := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  let W := (Matrix.toEuclideanLin Q).range.map I.toLinearMap
  have hWrank : finrank ℂ W = Q.rank := by
    rw [I.toLinearEquiv.finrank_map_eq]
    simpa only [Fintype.card_fin] using
      Module.finrank_eq_card_basis (Matrix.rangeOrthonormalBasis ⟨Q, rfl⟩).toBasis
  have hRange : Y = ⨆ i, W.map (A i).toLinearMap :=
    Matrix.range_familySupportProj_comp_linearIsometryEquiv I A Q
  obtain ⟨hImage, hOutput⟩ := finrank_family_image_trim_le cuts xi k A W
  constructor
  · rw [hRange]
    simpa only [hWrank] using hImage
  · rw [nativeFamilyTrimSpace_eq_trimSubspace]
    simpa only [hWrank] using hOutput

/-- A predetermined stopping count bounds both the last untrimmed image
and the actual complete parent for every seed sequence. No successful-sample
or viability hypothesis is used. Supporting ALVV,
arXiv:1602.08828v2, the resampling description, lines 749–755. -/
theorem finrank_canonicalHalfSamplingParent_le_threshold
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold rounds : ℕ)
    (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n))
    (hcard : Fintype.card ι ≤ D ^ 2) (hthreshold : 2 ≤ threshold)
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.rank ≤ 2 ^ rounds)
    (U : ℕ → Matrix.rankUnitaryProduct d) :
    let Q := canonicalHalfSampleTrimIterate e cuts xi k D threshold (nativeFamilyMatrix e A)
      P U rounds
    let Y := (Matrix.toEuclideanLin (Matrix.familySupportProj
      (fun i ↦ nativeFamilyMatrix e A i * Q))).range
    Q.rank < threshold ∧ finrank ℂ Y ≤ Fintype.card ι * threshold ∧
      finrank ℂ (canonicalHalfSamplingParent e cuts xi k D threshold rounds A P U) ≤
        Fintype.card ι * threshold := by
  intro Q Y
  have hsmall : Q.rank < threshold :=
    rank_canonicalHalfSampleTrimIterate_lt e cuts xi k D threshold (nativeFamilyMatrix e A)
      hcard P U rounds hthreshold hP
  have hdim := finrank_nativeFamily_image_trim_le e cuts xi k A Q
  have hmul := Nat.mul_le_mul_left (Fintype.card ι) hsmall.le
  exact ⟨hsmall, hdim.1.trans hmul, hdim.2.trans hmul⟩

/-- The initial-rank ceiling bounds the last full image and complete native
parent on every seed sequence, without a stopping or viability premise.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755. -/
theorem finrank_canonicalHalfSamplingParent_le_initial
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold rounds : ℕ)
    (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n))
    (hcard : Fintype.card ι ≤ D ^ 2)
    (P : Matrix (Fin d) (Fin d) ℂ) (U : ℕ → Matrix.rankUnitaryProduct d) :
    let Q := canonicalHalfSampleTrimIterate e cuts xi k D threshold (nativeFamilyMatrix e A)
      P U rounds
    let Y := (Matrix.toEuclideanLin (Matrix.familySupportProj
      (fun i ↦ nativeFamilyMatrix e A i * Q))).range
    finrank ℂ Y ≤ Fintype.card ι * P.rank ∧
      finrank ℂ (canonicalHalfSamplingParent e cuts xi k D threshold rounds A P U) ≤
        Fintype.card ι * P.rank := by
  intro Q Y
  have hdim := finrank_nativeFamily_image_trim_le e cuts xi k A Q
  have hsmall : Q.rank ≤ P.rank :=
    rank_canonicalHalfSampleTrimIterate_le e cuts xi k D threshold (nativeFamilyMatrix e A)
      hcard P U rounds
  have hmul := Nat.mul_le_mul_left (Fintype.card ι) hsmall
  exact ⟨hdim.1.trans hmul, hdim.2.trans hmul⟩

/-- The actual terminal native trim restores original-target error while
retaining the last untrimmed image's exact improving-target error. The
current matrix need not be a projection. All family and reference data
precede that matrix. This is a deterministic auxiliary for ALVV,
arXiv:1602.08828v2, lines 749–755 and 1801–1813; the stopped-loop success
event is discharged separately in the probability application. -/
theorem isCloseTo_nativeFamilyTrimSpace
    {D m bRef : ℕ} {Delta epsilonRef xi : ℝ}
    {Graw R : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β))}
    (x0 : X) (T : X → Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β)))
    (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n))
    (hcard : Fintype.card ι ≤ D ^ 2)
    (hRawSoft : ∀ x, Submodule.IsCloseTo (1 / 200) Graw (T x))
    (hSoftRaw : ∀ x, Submodule.IsCloseTo (1 / 200) (T x) Graw)
    (hA : ∀ x delta, delta < 1 →
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)),
      Submodule.IsCloseTo delta (Submodule.prodExt S β) (T x) →
      Submodule.IsCloseTo (Delta / (1 - delta) ^ 2)
        (Submodule.prodExt (⨆ i, S.map (A i : _ →ₗ[ℂ] _)) β) (T x))
    (hD : 2 ≤ D) (hDelta : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (C : ℕ → Finset V) (hC : Monotone C) (hxi : 0 < xi)
    (hepsilonRef0 : 0 ≤ epsilonRef) (hepsilonRef : epsilonRef ≤ 1 / 100000)
    (hRawRef : Submodule.IsCloseTo epsilonRef Graw R)
    (hRefRaw : Submodule.IsCloseTo epsilonRef R Graw)
    (hRank : ∀ t ∈ R, ∀ j < m,
      Matrix.schmidtRank (WithLp.ofLp (cutEnvVector (C j) t)) ≤ bRef)
    (hbudget : xi * Real.sqrt ((m : ℝ) * (bRef : ℝ)) ≤ 1 / 1000)
    (e : Fin d ≃ SiteConfig n) (Q : Matrix (Fin d) (Fin d) ℂ)
    (hQ : Submodule.IsCloseTo 0.04
      (Submodule.prodExt ((Matrix.toEuclideanLin Q).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) β) Graw) :
    let Y := (Matrix.toEuclideanLin (Matrix.familySupportProj
      (fun i ↦ nativeFamilyMatrix e A i * Q))).range
    (∀ x, Submodule.IsCloseTo (Delta / (91 / 100 : ℝ) ^ 2)
      (Submodule.prodExt Y β) (T x)) ∧
    Submodule.IsCloseTo (27 / 2500) (Submodule.prodExt Y β) Graw ∧
    Submodule.IsCloseTo (3 / 200)
      (Submodule.prodExt (nativeFamilyTrimSpace e C xi m A Q) β) Graw := by
  intro Y
  let I := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  let W := (Matrix.toEuclideanLin Q).range.map I.toLinearMap
  obtain ⟨hTarget, hRawImage, hRawOutput, _, _⟩ :=
    isCloseTo_terminal_family_reference_trim x0 T A hcard hRawSoft hSoftRaw hA hD hDelta
      C hC hxi hepsilonRef0 hepsilonRef hRawRef hRefRaw hRank hbudget W hQ
  have hRange : Y = ⨆ i, W.map (A i).toLinearMap :=
    Matrix.range_familySupportProj_comp_linearIsometryEquiv I A Q
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [hRange]
    exact hTarget x
  · rw [hRange]
    exact hRawImage
  · rw [nativeFamilyTrimSpace_eq_trimSubspace]
    exact hRawOutput

end Entropy
