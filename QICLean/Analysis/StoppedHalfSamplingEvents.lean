/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.StoppedHalfSamplingSeed
import QICLean.Analysis.MatrixRangeProjectionMeasurable

/-!
# Joint measurable original-target histories of stopped resampling

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
has error .015. This supports corrected repeated resampling for ALVV,
arXiv:1602.08828v2, lines 749–755; it is not an uncountable intersection
over improving spectral targets. -/
def canonicalHalfSamplingRawGood
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold : ℕ) (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (Graw : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β))) :
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
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold : ℕ) (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (Graw : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β))) :
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
