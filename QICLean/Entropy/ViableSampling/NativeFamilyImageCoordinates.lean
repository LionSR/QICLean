/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.ViableSampling.CanonicalSamplingTrimmingMeasurable
import QICLean.Analysis.FiniteFamilyImageProjection
import QICLean.Analysis.FiniteFamilyImageCoordinates

/-!
# Native family images of arbitrary coordinate matrix ranges

A native operator family is represented in a fixed input coordinate chart.
The existing joint column support then describes its actual full image,
including for input matrices that are not projections. The subsequent
canonical collective trim is the same basis-independent trim of that image.

This supports ALVV, arXiv:1602.08828v2, Lemma `l:er`, lines 597–622, and
collective trimming, Definition `def:trimming`, lines 648–655. No target,
viability or successful-sampling hypothesis is used.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Entropy

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  {n : V → ℕ} {d : ℕ}

/-- The actual rectangular matrix of a native operator after the fixed
input-coordinate isometry. Used for ALVV, arXiv:1602.08828v2,
Lemma `l:er`, lines 597–622. -/
def nativeFamilyMatrix (e : Fin d ≃ (∀ v, Fin (n v)))
    (A : ι → EuclideanSpace ℂ (∀ v, Fin (n v)) →L[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v))) :
    ι → Matrix (∀ v, Fin (n v)) (Fin d) ℂ := fun i ↦
  (Matrix.toEuclideanLin (m := (∀ v, Fin (n v))) (n := Fin d) (𝕜 := ℂ)).symm
    ((A i).toLinearMap.comp (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap)

/-- The literal terminal native trim of the full fixed-family image of
an arbitrary coordinate matrix range. Supporting ALVV,
arXiv:1602.08828v2, the resampling description, lines 749–755. -/
def nativeFamilyTrimSpace (e : Fin d ≃ (∀ v, Fin (n v)))
    (cuts : ℕ → Finset V) (xi : ℝ) (k : ℕ)
    (A : ι → EuclideanSpace ℂ (∀ v, Fin (n v)) →L[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v)))
    (Q : Matrix (Fin d) (Fin d) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) :=
  trimMatrixRange e cuts xi k
    (Matrix.familySupportProj (fun i ↦ nativeFamilyMatrix e A i * Q))

/-- The terminal native output has a Borel actual projection on arbitrary
input matrices, without a supplied measurable basis or projection premise.
Auxiliary for ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem measurable_projectionMatrix_nativeFamilyTrimSpace
    (e : Fin d ≃ (∀ v, Fin (n v))) (cuts : ℕ → Finset V) (xi : ℝ) (k : ℕ)
    (A : ι → EuclideanSpace ℂ (∀ v, Fin (n v)) →L[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v))) :
    Measurable (fun Q : Matrix (Fin d) (Fin d) ℂ ↦
      (Matrix.toEuclideanCLM (n := (∀ v, Fin (n v))) (𝕜 := ℂ)).symm
        (nativeFamilyTrimSpace e cuts xi k A Q).starProjection) :=
  (measurable_projectionMatrix_trimMatrixRange e cuts xi k).comp
    (Matrix.measurable_familySupportProj_mul (nativeFamilyMatrix e A))

/-- The terminal map is exactly the existing collective trim of the
standard orthonormal basis of the full native family image. This includes
arbitrary input matrices and zero ranges. Supporting ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem nativeFamilyTrimSpace_eq_trimSubspace
    (e : Fin d ≃ (∀ v, Fin (n v))) (cuts : ℕ → Finset V) (xi : ℝ) (k : ℕ)
    (A : ι → EuclideanSpace ℂ (∀ v, Fin (n v)) →L[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v)))
    (Q : Matrix (Fin d) (Fin d) ℂ) :
    let W := (Matrix.toEuclideanLin Q).range.map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap
    let image : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) :=
      ⨆ i, W.map (A i).toLinearMap
    nativeFamilyTrimSpace e cuts xi k A Q =
      trimSubspace cuts xi
        (fun i ↦ (stdOrthonormalBasis ℂ image i : EuclideanSpace ℂ (∀ v, Fin (n v)))) k := by
  intro W image
  let Y := Matrix.familySupportProj (fun i ↦ nativeFamilyMatrix e A i * Q)
  have hRange : (Matrix.toEuclideanLin Y).range = image :=
    Matrix.range_familySupportProj_comp_linearIsometryEquiv
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e) A Q
  change trimMatrixRange e cuts xi k Y = _
  have hAny (S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))))
      (hS : (Matrix.toEuclideanLin Y).range = S)
      (bS : OrthonormalBasis (Fin (Module.finrank ℂ S)) ℂ S) :
      trimMatrixRange e cuts xi k Y =
        trimSubspace cuts xi (fun i ↦ (bS i : EuclideanSpace ℂ (∀ v, Fin (n v)))) k := by
    subst S
    exact trimMatrixRange_eq_of_orthonormalBasis e cuts xi k Y bS
  exact hAny image hRange (stdOrthonormalBasis ℂ image)

end Entropy
