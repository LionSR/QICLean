/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CanonicalSamplingTrimmingMeasurable
import QICLean.Analysis.ViableSubspaceTensorProjectionMeasurable

/-!
# The true regional viability event for actual sampling and trimming

The actual canonical sample, fixed-family image and collective trim have
a Borel viability event for an arbitrary fixed target in the whole local
space tensored with its exterior. No comparison target or jointly selected
measurable hull is supplied. Source: ALVV, arXiv:1602.08828v2,
Definition `d:vs`, lines 433–440, and the interleaved merge, lines 1668–1670.
This auxiliary does not assert an adaptive probability bound.
-/

open MeasureTheory
open scoped TensorProduct Matrix.Norms.L2Operator

namespace Entropy

/-- Requested sample size may depend on the actual input rank. The true
original-target viability event of the same sampled image and trim is Borel.
The entire exterior tensor factor is retained. Auxiliary to ALVV,
arXiv:1602.08828v2, Definition d:vs, lines 433–440. -/
theorem measurableSet_isViable_trim_sample_family_image_rank_size
    {V β ι : Type*} [Fintype V] [DecidableEq V] [Fintype β] [Fintype ι]
    {n : V → ℕ} {d a : ℕ}
    (e : Fin d ≃ SiteConfig n) (D : ℕ → Finset V) (xi : ℝ) (k : ℕ) (s : ℕ → ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin a) ℂ) (delta : ℝ)
    (T : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n) ⊗[ℂ] EuclideanSpace ℂ β)) :
    let S := fun p : Matrix (Fin a) (Fin a) ℂ × Matrix.rankUnitaryProduct a ↦
      trimMatrixRange e D xi k (Matrix.familySupportProj (fun i ↦ F i *
        (Matrix.toEuclideanCLM (n := Fin a) (𝕜 := ℂ)).symm
          (Matrix.randomRangeSubspace p.1 (s p.1.rank) p.2).starProjection))
    MeasurableSet {p | Submodule.IsViable delta (S p) T} := by
  intro S
  exact Submodule.measurableSet_isViable_of_measurable_projectionMatrix S
    (measurable_projectionMatrix_trim_sample_family_image_rank_size e D xi k s F) delta T

/-- The original viability event for the exact sampled, improved and
collectively trimmed output is Borel, with its original fixed target and
the entire exterior tensor factor. Its failure event is Borel as well. -/
theorem measurableSet_isViable_trim_sample_family_image
    {V β ι : Type*} [Fintype V] [DecidableEq V] [Fintype β] [Fintype ι]
    {n : V → ℕ} {d a : ℕ}
    (e : Fin d ≃ SiteConfig n) (D : ℕ → Finset V) (xi : ℝ) (k s : ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin a) ℂ) (delta : ℝ)
    (T : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n) ⊗[ℂ] EuclideanSpace ℂ β)) :
    let S := fun p : Matrix (Fin a) (Fin a) ℂ × Matrix.rankUnitaryProduct a ↦
      trimMatrixRange e D xi k (Matrix.familySupportProj (fun i ↦ F i *
        (Matrix.toEuclideanCLM (n := Fin a) (𝕜 := ℂ)).symm
          (Matrix.randomRangeSubspace p.1 s p.2).starProjection))
    MeasurableSet {p | Submodule.IsViable delta (S p) T} :=
  measurableSet_isViable_trim_sample_family_image_rank_size e D xi k (fun _ ↦ s) F delta T

end Entropy
