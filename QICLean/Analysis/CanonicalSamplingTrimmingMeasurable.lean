/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FiniteCoordinateRangeFrame
import QICLean.Analysis.VariableRankSampleProjection
import QICLean.Analysis.ViableSubspaceTrimmingProjectionMeasurable
import QICLean.Analysis.ViableSubspaceProjectionEvent

/-!
# Borel composition of actual sampling, operator images and collective trimming

The canonical orthonormal range frame is inserted into the existing
collective-trimming construction. Its actual ambient projection is Borel
across rank changes. Composing this map with the existing canonical Haar
sample and fixed-family image gives a Borel map for the same physical
operations, without a supplied measurable basis or comparison subspace.

Source: ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655,
and the interleaved merge construction, lines 1668–1670. This is a
measurability auxiliary, not an adaptive probability or running-time theorem.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {d r : ℕ}

/-- The existing collective trim of the actual matrix range, using the
canonical orthonormal range frame in the prescribed physical coordinates. -/
def trimMatrixRange (e : Fin d ≃ SiteConfig n) (D : ℕ → Finset V)
    (xi : ℝ) (k : ℕ) (P : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) :=
  trimSubspace D xi (Matrix.rangeOrthonormalFrameInCoordinates e ⟨P, rfl⟩) k

/-- The range trim is literally the existing collective trim of the
canonical orthonormal frame on every rank stratum. -/
theorem trimMatrixRange_eq_on_rank (e : Fin d ≃ SiteConfig n)
    (D : ℕ → Finset V) (xi : ℝ) (k : ℕ)
    (P : {P : Matrix (SiteConfig n) (SiteConfig n) ℂ // P.rank = r}) :
    trimMatrixRange e D xi k P.val =
      trimSubspace D xi (Matrix.rangeOrthonormalFrameInCoordinates e P) k := by
  rcases P with ⟨P, hP⟩
  subst r
  rfl

/-- The canonical range trim is the same actual collective trim obtained
from any orthonormal basis of that range. Thus it does not introduce a
basis-dependent substitute for the original subspace operation. -/
theorem trimMatrixRange_eq_of_orthonormalBasis {t : ℕ}
    (e : Fin d ≃ SiteConfig n) (D : ℕ → Finset V) (xi : ℝ) (k : ℕ)
    (P : Matrix (SiteConfig n) (SiteConfig n) ℂ)
    (c : OrthonormalBasis (Fin t) ℂ (Matrix.toEuclideanLin P).range) :
    trimMatrixRange e D xi k P =
      trimSubspace D xi (fun i ↦ (c i : EuclideanSpace ℂ (SiteConfig n))) k := by
  let W := (Matrix.toEuclideanLin P).range
  let u := Matrix.rangeOrthonormalFrameInCoordinates e ⟨P, rfl⟩
  have hspan : Submodule.span ℂ (Set.range u) = W :=
    Matrix.span_rangeOrthonormalFrameInCoordinates e ⟨P, rfl⟩
  have hmem (i : Fin P.rank) : u i ∈ W := by
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  let b : OrthonormalBasis (Fin P.rank) ℂ W :=
    OrthonormalBasis.mk
      ((Matrix.orthonormal_rangeOrthonormalFrameInCoordinates e ⟨P, rfl⟩).codRestrict W hmem)
      ((Submodule.span_range_subtype_eq_top_iff W hmem).mpr hspan).ge
  have hb : (fun i ↦ (b i : EuclideanSpace ℂ (SiteConfig n))) = u := by
    exact congrArg (fun f : Fin P.rank → W ↦
      fun i ↦ (f i : EuclideanSpace ℂ (SiteConfig n))) (OrthonormalBasis.coe_mk _ _)
  change trimSubspace D xi u k = _
  rw [← hb]
  exact trimSubspace_eq_of_orthonormalBasis D xi b c k

/-- The actual ambient orthogonal projection of this collective trim is
Borel on all matrices, including zero rank and rank changes. -/
theorem measurable_projectionMatrix_trimMatrixRange
    (e : Fin d ≃ SiteConfig n) (D : ℕ → Finset V) (xi : ℝ) (k : ℕ) :
    Measurable (fun P : Matrix (SiteConfig n) (SiteConfig n) ℂ ↦
      (Matrix.toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ)).symm
        (trimMatrixRange e D xi k P).starProjection) := by
  apply measurable_of_matrix_rank_strata (P := id) measurable_id
  intro r
  change Measurable (fun P : {P : Matrix (SiteConfig n) (SiteConfig n) ℂ // P.rank = r} ↦
    (Matrix.toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ)).symm
      (trimMatrixRange e D xi k P.val).starProjection)
  have h := (measurable_projectionMatrix_trimSubspace (n := n) (s := r) D xi k).comp
    (Matrix.measurable_rangeOrthonormalFrameInCoordinates e)
  convert h using 1
  funext P
  rw [trimMatrixRange_eq_on_rank e D xi k P]
  rfl

/-- A deterministic fixed-family image followed by the same actual
collective trim has a Borel ambient projection. This applies at every
subsequent round of the interleaved merge. -/
theorem measurable_projectionMatrix_trim_family_image
    {ι : Type*} [Fintype ι]
    (e : Fin d ≃ SiteConfig n) (D : ℕ → Finset V) (xi : ℝ) (k : ℕ)
    (F : ι → Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    Measurable (fun P : Matrix (SiteConfig n) (SiteConfig n) ℂ ↦
      (Matrix.toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ)).symm
        (trimMatrixRange e D xi k (Matrix.familySupportProj
          (fun i ↦ F i * P))).starProjection) :=
  (measurable_projectionMatrix_trimMatrixRange e D xi k).comp
    (Matrix.measurable_familySupportProj_mul F)

/-- The sample size may depend on the actual input rank. The same
fixed-family image and actual collective trim have a jointly Borel
projection. Auxiliary to ALVV, arXiv:1602.08828v2, the merge process,
lines 711–736, and Figure fig:merge-prime, lines 1668–1670. -/
theorem measurable_projectionMatrix_trim_sample_family_image_rank_size
    {ι : Type*} [Fintype ι] {a : ℕ}
    (e : Fin d ≃ SiteConfig n) (D : ℕ → Finset V) (xi : ℝ) (k : ℕ) (s : ℕ → ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin a) ℂ) :
    Measurable (fun p : Matrix (Fin a) (Fin a) ℂ × Matrix.rankUnitaryProduct a ↦
      (Matrix.toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ)).symm
        (trimMatrixRange e D xi k (Matrix.familySupportProj (fun i ↦ F i *
          (Matrix.toEuclideanCLM (n := Fin a) (𝕜 := ℂ)).symm
            (Matrix.randomRangeSubspace p.1 (s p.1.rank) p.2).starProjection))).starProjection) :=
  (measurable_projectionMatrix_trimMatrixRange e D xi k).comp
    (Matrix.measurable_familySupportProj_randomRangeSubspace_rank_size F s)

/-- Sampling from the actual matrix range, applying the fixed operator
family, and collectively trimming its actual image has a jointly Borel
ambient projection on one fixed finite product of unitary groups. -/
theorem measurable_projectionMatrix_trim_sample_family_image
    {ι : Type*} [Fintype ι] {a : ℕ}
    (e : Fin d ≃ SiteConfig n) (D : ℕ → Finset V) (xi : ℝ) (k s : ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin a) ℂ) :
    Measurable (fun p : Matrix (Fin a) (Fin a) ℂ × Matrix.rankUnitaryProduct a ↦
      (Matrix.toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ)).symm
        (trimMatrixRange e D xi k (Matrix.familySupportProj (fun i ↦ F i *
          (Matrix.toEuclideanCLM (n := Fin a) (𝕜 := ℂ)).symm
            (Matrix.randomRangeSubspace p.1 s p.2).starProjection))).starProjection) :=
  measurable_projectionMatrix_trim_sample_family_image_rank_size e D xi k (fun _ ↦ s) F

/-- The true closeness event for the actual sampled, improved and
collectively trimmed output is Borel. Its complement is therefore Borel;
no jointly chosen measurable hull is needed. -/
theorem measurableSet_isCloseTo_trim_sample_family_image
    {ι : Type*} [Fintype ι] {a : ℕ}
    (e : Fin d ≃ SiteConfig n) (D : ℕ → Finset V) (xi : ℝ) (k s : ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin a) ℂ) (delta : ℝ)
    (T : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))) :
    let S := fun p : Matrix (Fin a) (Fin a) ℂ × Matrix.rankUnitaryProduct a ↦
      trimMatrixRange e D xi k (Matrix.familySupportProj (fun i ↦ F i *
        (Matrix.toEuclideanCLM (n := Fin a) (𝕜 := ℂ)).symm
          (Matrix.randomRangeSubspace p.1 s p.2).starProjection))
    MeasurableSet {p | Submodule.IsCloseTo delta (S p) T} := by
  intro S
  exact Submodule.measurableSet_isCloseTo_of_measurable_projectionMatrix S
    (measurable_projectionMatrix_trim_sample_family_image e D xi k s F) delta T

end Entropy
