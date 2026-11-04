/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.NativeFamilyImageCoordinates
import QICLean.Analysis.CanonicalHalfSamplingDimension
import QICLean.Analysis.ViableSubspaceTensorProjectionMeasurable

/-!
# The native stopped-resampling parent with its terminal full-family trim

The operation is the existing stopped matrix iteration, followed by one
full image of its terminal range under the same native family and the same
collective trim. Its actual output projection and original-target viability
event are Borel; no success event is supplied as a measurability premise.

This supports ALVV, arXiv:1602.08828v2, the resampling description at
lines 749–755 and the reference argument at lines 1801–1813.
This module treats a repeated-resampling variant of the merge procedure
sketched at arXiv:1602.08828v2, lines 711–755; Figure `fig:merge-prime` and
Theorem `t:alg1` are not formalized here. See
`docs/paper-gaps/alvv16_bootstrap_constants.tex`.
The operation uses fresh samples at active rounds and a deterministic
terminal image and trim.
No running-time conclusion is asserted.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Entropy

variable {V β ι : Type*} [Fintype V] [DecidableEq V] [Fintype β] [Fintype ι]
  {n : V → ℕ} {d : ℕ}

/-- The actual stopped iteration followed by the same full-family native
terminal trim, with all family and cut data fixed before the initial matrix
and seed sequence. Supporting ALVV, arXiv:1602.08828v2, lines 749–755. -/
def canonicalHalfSamplingParent (e : Fin d ≃ SiteConfig n)
    (cuts : ℕ → Finset V) (xi : ℝ) (k D threshold rounds : ℕ)
    (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n))
    (P : Matrix (Fin d) (Fin d) ℂ) (U : ℕ → Matrix.rankUnitaryProduct d) :
    Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) :=
  nativeFamilyTrimSpace e cuts xi k A
    (canonicalHalfSampleTrimIterate e cuts xi k D threshold
      (nativeFamilyMatrix e A) P U rounds)

/-- The complete native parent has a jointly Borel actual output projection.
No assertion about a varying arbitrary basis or a sampling-success event
is used. Auxiliary for ALVV, arXiv:1602.08828v2, lines 749–755. -/
theorem measurable_projectionMatrix_canonicalHalfSamplingParent
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold rounds : ℕ)
    (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n)) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℂ ×
        (ℕ → Matrix.rankUnitaryProduct d) ↦
      (Matrix.toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ)).symm
        (canonicalHalfSamplingParent e cuts xi k D threshold rounds A p.1 p.2).starProjection) :=
  (measurable_projectionMatrix_nativeFamilyTrimSpace e cuts xi k A).comp
    (measurable_canonicalHalfSampleTrimIterate e cuts xi k D threshold
      (nativeFamilyMatrix e A) rounds)

/-- The actual parent output is viable for a fixed original target on a
Borel event in the initial matrix and the whole seed sequence. The target
retains the entire exterior factor. Auxiliary for ALVV,
arXiv:1602.08828v2, Definition `d:vs`, lines 433–440. -/
theorem measurableSet_isCloseTo_prodExt_canonicalHalfSamplingParent
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold rounds : ℕ)
    (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n))
    (delta : ℝ) (Graw : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β))) :
    MeasurableSet {p : Matrix (Fin d) (Fin d) ℂ × (ℕ → Matrix.rankUnitaryProduct d) |
      Submodule.IsCloseTo delta
        (Submodule.prodExt (canonicalHalfSamplingParent e cuts xi k D threshold rounds A
          p.1 p.2) β) Graw} := by
  classical
  let S := fun p : Matrix (Fin d) (Fin d) ℂ × (ℕ → Matrix.rankUnitaryProduct d) ↦
    canonicalHalfSamplingParent e cuts xi k D threshold rounds A p.1 p.2
  have h := Submodule.measurableSet_isViable_of_measurable_projectionMatrix S
    (measurable_projectionMatrix_canonicalHalfSamplingParent e cuts xi k D threshold rounds A)
    delta (Graw.map (Submodule.euclideanTensorEquiv (SiteConfig n) β).toLinearEquiv.toLinearMap)
  convert h using 1
  ext p
  exact Submodule.isCloseTo_prodExt_iff_isViable (S p) Graw

end Entropy
