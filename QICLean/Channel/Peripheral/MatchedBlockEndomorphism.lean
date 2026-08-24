/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.DirectSumFacePermutation

/-!
# Endomorphisms on matched full-matrix blocks

Wolf's pure-state-face argument in the proof of Theorem 6.16 matches a source
full-matrix block with a target block of the same dimension.  This module
uses that dimension equality only to reindex the matched forward block map to
an endomorphism of the source matrix algebra.  The matched inverse block map
is transported in the opposite direction.

The resulting two endomorphisms are positive, trace preserving, and mutually
inverse.  A separate bridge records that an ordinary Schwarz inequality for
the raw matched block map becomes `IsSchwarzMap` after reindexing.  Establishing
that raw inequality from Wolf's weighted density-block coordinates is not done
here.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines
1641--1663.
-/

open scoped Matrix MatrixOrder ComplexOrder

noncomputable section

namespace Matrix

variable {ι κ : Type*}
variable [DecidableEq ι] [DecidableEq κ]
variable {d : ι → ℕ} {e : κ → ℕ}

/-- The forward map on a matched full-matrix block, transported back along
the dimension equality so that it is literally an endomorphism of the source
matrix algebra.

This is the map denoted `T_k` at Wolf Theorem 6.16, proof line 1663. -/
noncomputable def DirectSumFacePermutation.matchedBlockEndomorphism
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι) :
    Module.End ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  (Matrix.reindexAlgEquiv ℂ ℂ
      (finCongr (F.dimension_eq i))).symm.toLinearMap.comp
    (directSumBlockMap T i (F.blockEquiv i))

/-- The matched inverse block map, transported to an endomorphism of the same
source matrix algebra. -/
noncomputable def DirectSumFacePermutation.matchedBlockInverseEndomorphism
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι) :
    Module.End ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  (directSumBlockMap S (F.blockEquiv i) i).comp
    (Matrix.reindexAlgEquiv ℂ ℂ
      (finCongr (F.dimension_eq i))).toLinearMap

@[simp]
theorem DirectSumFacePermutation.matchedBlockEndomorphism_apply
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι)
    (X : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    F.matchedBlockEndomorphism i X =
      Matrix.reindex (finCongr (F.dimension_eq i)).symm
        (finCongr (F.dimension_eq i)).symm
        (directSumBlockMap T i (F.blockEquiv i) X) := by
  rfl

@[simp]
theorem DirectSumFacePermutation.matchedBlockInverseEndomorphism_apply
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι)
    (X : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    F.matchedBlockInverseEndomorphism i X =
      directSumBlockMap S (F.blockEquiv i) i
        (Matrix.reindex (finCongr (F.dimension_eq i))
          (finCongr (F.dimension_eq i)) X) := by
  rfl

/-- The transported forward block map is positive. -/
theorem DirectSumFacePermutation.matchedBlockEndomorphism_isPositiveMap
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι) :
    IsPositiveMap (F.matchedBlockEndomorphism i) := by
  intro X hX
  rw [F.matchedBlockEndomorphism_apply]
  exact (F.blockMap_pos i X hX).submatrix
    (finCongr (F.dimension_eq i))

/-- The transported matched inverse block map is positive. -/
theorem DirectSumFacePermutation.matchedBlockInverseEndomorphism_isPositiveMap
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι) :
    IsPositiveMap (F.matchedBlockInverseEndomorphism i) := by
  intro X hX
  rw [F.matchedBlockInverseEndomorphism_apply]
  have hReindex :
      (Matrix.reindex (finCongr (F.dimension_eq i))
        (finCongr (F.dimension_eq i)) X).PosSemidef :=
    hX.submatrix (finCongr (F.dimension_eq i)).symm
  have h := F.inverseBlockMap_pos (F.blockEquiv i) _ hReindex
  rw [F.blockEquiv.symm_apply_apply] at h
  exact h

/-- The transported forward block map preserves the ordinary matrix trace. -/
theorem DirectSumFacePermutation.matchedBlockEndomorphism_isTracePreservingMap
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι) :
    IsTracePreservingMap (F.matchedBlockEndomorphism i) := by
  intro X
  rw [F.matchedBlockEndomorphism_apply, Matrix.trace_reindex,
    F.blockMap_trace]

/-- The transported matched inverse block map also preserves the ordinary
matrix trace. -/
theorem DirectSumFacePermutation.matchedBlockInverseEndomorphism_isTracePreservingMap
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι) :
    IsTracePreservingMap (F.matchedBlockInverseEndomorphism i) := by
  intro X
  rw [F.matchedBlockInverseEndomorphism_apply]
  have h := F.inverseBlockMap_trace (F.blockEquiv i)
    (Matrix.reindex (finCongr (F.dimension_eq i))
      (finCongr (F.dimension_eq i)) X)
  rw [F.blockEquiv.symm_apply_apply] at h
  exact h.trans (Matrix.trace_reindex (finCongr (F.dimension_eq i)) X)

/-- The transported inverse block map is a left inverse of the transported
forward block map. -/
theorem DirectSumFacePermutation.matchedBlockEndomorphism_leftInverse
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι) :
    Function.LeftInverse (F.matchedBlockInverseEndomorphism i)
      (F.matchedBlockEndomorphism i) := by
  intro X
  rw [F.matchedBlockInverseEndomorphism_apply,
    F.matchedBlockEndomorphism_apply]
  let q := finCongr (F.dimension_eq i)
  have hReindex (Y : Matrix (Fin (e (F.blockEquiv i)))
      (Fin (e (F.blockEquiv i))) ℂ) :
      Matrix.reindex q q (Matrix.reindex q.symm q.symm Y) = Y := by
    exact (Matrix.reindexLinearEquiv ℂ ℂ q q).apply_symm_apply Y
  rw [hReindex]
  exact F.blockMap_leftInverse i X

/-- The transported inverse block map is also a right inverse of the
transported forward block map. -/
theorem DirectSumFacePermutation.matchedBlockEndomorphism_rightInverse
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι) :
    Function.RightInverse (F.matchedBlockInverseEndomorphism i)
      (F.matchedBlockEndomorphism i) := by
  intro X
  rw [F.matchedBlockEndomorphism_apply,
    F.matchedBlockInverseEndomorphism_apply,
    F.blockMap_rightInverse]
  let q := finCongr (F.dimension_eq i)
  exact (Matrix.reindexLinearEquiv ℂ ℂ q q).symm_apply_apply X

/-- The transported inverse composed after the transported forward block map
is the identity. -/
theorem DirectSumFacePermutation.matchedBlockInverseEndomorphism_comp
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι) :
    (F.matchedBlockInverseEndomorphism i).comp
      (F.matchedBlockEndomorphism i) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  exact F.matchedBlockEndomorphism_leftInverse i X

/-- The transported forward block map composed after its transported inverse
is the identity. -/
theorem DirectSumFacePermutation.matchedBlockEndomorphism_comp_inverse
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι) :
    (F.matchedBlockEndomorphism i).comp
      (F.matchedBlockInverseEndomorphism i) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  exact F.matchedBlockEndomorphism_rightInverse i X

/-- The transported forward block map is bijective. -/
theorem DirectSumFacePermutation.matchedBlockEndomorphism_bijective
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι) :
    Function.Bijective (F.matchedBlockEndomorphism i) :=
  ⟨(F.matchedBlockEndomorphism_leftInverse i).injective,
    (F.matchedBlockEndomorphism_rightInverse i).surjective⟩

/-- The transported matched inverse is the canonical inverse linear map of
the transported forward block map.  This consumer-independent form unfolds
directly to the inverse used by the positive-invertible-map classification. -/
theorem DirectSumFacePermutation.matchedBlockInverseEndomorphism_eq_canonicalInverse
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι)
    (hBij : Function.Bijective (F.matchedBlockEndomorphism i)) :
    F.matchedBlockInverseEndomorphism i =
      (LinearEquiv.ofBijective (F.matchedBlockEndomorphism i) hBij).symm.toLinearMap := by
  apply LinearMap.ext
  intro X
  apply hBij.1
  calc
    F.matchedBlockEndomorphism i
        (F.matchedBlockInverseEndomorphism i X) = X :=
      F.matchedBlockEndomorphism_rightInverse i X
    _ = F.matchedBlockEndomorphism i
        ((LinearEquiv.ofBijective
          (F.matchedBlockEndomorphism i) hBij).symm X) :=
      (LinearEquiv.ofBijective
        (F.matchedBlockEndomorphism i) hBij).apply_symm_apply X |>.symm

/-- The canonical inverse of the transported forward block map is positive. -/
theorem DirectSumFacePermutation.matchedBlockCanonicalInverse_isPositiveMap
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι)
    (hBij : Function.Bijective (F.matchedBlockEndomorphism i)) :
    IsPositiveMap
      (LinearEquiv.ofBijective (F.matchedBlockEndomorphism i) hBij).symm.toLinearMap := by
  rw [← F.matchedBlockInverseEndomorphism_eq_canonicalInverse i hBij]
  exact F.matchedBlockInverseEndomorphism_isPositiveMap i

/-- An ordinary Schwarz inequality for the raw matched block map becomes the
ordinary Schwarz inequality for its transported endomorphism.

This is only a change-of-index bridge.  In the application to Wolf Theorem
6.16, the premise must be proved separately by compressing the ambient
Schwarz defect in the weighted density-block coordinates; it is not obtained
by treating those coordinates as an ordinary algebra embedding.  The premise
is the block Schwarz inequality asserted at proof line 1663. -/
theorem DirectSumFacePermutation.matchedBlockEndomorphism_isSchwarzMap_of_raw
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S) (i : ι)
    (hSchwarz : ∀ X : Matrix (Fin (d i)) (Fin (d i)) ℂ,
      (directSumBlockMap T i (F.blockEquiv i) (Xᴴ * X) -
        directSumBlockMap T i (F.blockEquiv i) Xᴴ *
          directSumBlockMap T i (F.blockEquiv i) X).PosSemidef) :
    IsSchwarzMap (F.matchedBlockEndomorphism i) := by
  intro X
  let q := finCongr (F.dimension_eq i)
  have hTransport :
      ((Matrix.reindexAlgEquiv ℂ ℂ q).symm
        (directSumBlockMap T i (F.blockEquiv i) (Xᴴ * X) -
          directSumBlockMap T i (F.blockEquiv i) Xᴴ *
            directSumBlockMap T i (F.blockEquiv i) X)).PosSemidef := by
    exact (hSchwarz X).submatrix q
  simp only [F.matchedBlockEndomorphism_apply]
  simpa only [q, map_sub, map_mul, Matrix.symm_reindexAlgEquiv,
    Matrix.coe_reindexAlgEquiv] using hTransport

end Matrix
