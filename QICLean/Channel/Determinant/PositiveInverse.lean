/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Determinant.Composition
import QICLean.Channel.TransferMatrix

/-!
# Positive inverses of matrix maps

This file develops the inverse-map interface needed for Wolf's corollary on
positive invertible maps.  In particular, the inverse of a bijective
trace-preserving map is trace preserving, and positivity of that inverse is
equivalent to the original positive map carrying the positive-semidefinite
cone onto itself.

The final classification is kept on Wolf's determinant route: determinant
bounds for a map and its inverse force determinant modulus one, after which
Wolf Theorem 6.1 supplies unitary conjugation or unitary conjugation after
ordinary matrix transposition.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.1.1][Wolf2012QChannels]

## Tags

positive map, inverse, trace preserving, determinant
-/

open scoped Matrix ComplexOrder MatrixOrder

variable {d : ℕ}

namespace ChannelDeterminant.Internal

local notation "MatrixAlg" => ChannelDeterminant.Internal.MatrixAlg
local notation "MatrixEnd" => ChannelDeterminant.Internal.MatrixEnd

/-- The inverse linear map of a bijective endomorphism of the matrix algebra. -/
noncomputable def inverseOfBijective (T : MatrixEnd d)
    (hT : Function.Bijective T) : MatrixEnd d :=
  (LinearEquiv.ofBijective T hT).symm.toLinearMap

@[simp]
theorem apply_inverseOfBijective (T : MatrixEnd d)
    (hT : Function.Bijective T) (X : MatrixAlg d) :
    T (inverseOfBijective T hT X) = X := by
  exact (LinearEquiv.ofBijective T hT).apply_symm_apply X

@[simp]
theorem inverseOfBijective_apply (T : MatrixEnd d)
    (hT : Function.Bijective T) (X : MatrixAlg d) :
    inverseOfBijective T hT (T X) = X := by
  exact (LinearEquiv.ofBijective T hT).symm_apply_apply X

@[simp]
theorem comp_inverseOfBijective (T : MatrixEnd d)
    (hT : Function.Bijective T) :
    T.comp (inverseOfBijective T hT) = 1 := by
  apply LinearMap.ext
  intro X
  exact apply_inverseOfBijective T hT X

@[simp]
theorem inverseOfBijective_comp (T : MatrixEnd d)
    (hT : Function.Bijective T) :
    (inverseOfBijective T hT).comp T = 1 := by
  apply LinearMap.ext
  intro X
  exact inverseOfBijective_apply T hT X

/-- The inverse of a bijective trace-preserving linear map is trace
preserving.  This is the observation immediately following Wolf's positive
invertible-map corollary. -/
theorem inverseOfBijective_isTracePreservingMap
    {T : MatrixEnd d} (hT : Function.Bijective T)
    (hTP : IsTracePreservingMap T) :
    IsTracePreservingMap (inverseOfBijective T hT) := by
  intro X
  have htrace := hTP (inverseOfBijective T hT X)
  rw [apply_inverseOfBijective] at htrace
  exact htrace.symm

/-- A positive bijection with positive inverse maps the positive-semidefinite
cone onto itself. -/
theorem mapsPSDConeOnto_of_inverseOfBijective_isPositiveMap
    {T : MatrixEnd d} (hT : Function.Bijective T)
    (hPos : IsPositiveMap T)
    (hInvPos : IsPositiveMap (inverseOfBijective T hT)) :
    MapsPSDConeOnto T := by
  refine ⟨hPos, ?_⟩
  intro A hA
  exact ⟨inverseOfBijective T hT A, hInvPos A hA,
    apply_inverseOfBijective T hT A⟩

/-- If a bijective linear map carries the positive-semidefinite cone onto
itself, then its inverse is positive. -/
theorem inverseOfBijective_isPositiveMap_of_mapsPSDConeOnto
    {T : MatrixEnd d} (hT : Function.Bijective T)
    (hCone : MapsPSDConeOnto T) :
    IsPositiveMap (inverseOfBijective T hT) := by
  intro A hA
  obtain ⟨X, hX, hTX⟩ := hCone.2 A hA
  have hInv : inverseOfBijective T hT A = X := by
    apply hT.1
    rw [apply_inverseOfBijective, hTX]
  rwa [hInv]

/-- For a positive bijection, positivity of the inverse is exactly
surjectivity on the positive-semidefinite cone. -/
theorem inverseOfBijective_isPositiveMap_iff_mapsPSDConeOnto
    {T : MatrixEnd d} (hT : Function.Bijective T)
    (hPos : IsPositiveMap T) :
    IsPositiveMap (inverseOfBijective T hT) ↔ MapsPSDConeOnto T :=
  ⟨mapsPSDConeOnto_of_inverseOfBijective_isPositiveMap hT hPos,
    inverseOfBijective_isPositiveMap_of_mapsPSDConeOnto hT⟩

/-- The determinant-bounds step in Wolf's positive-invertible-map
corollary.  If a positive trace-preserving bijection has positive inverse,
then both determinant moduli are at most one, while multiplicativity says
their product is one. -/
theorem channelDet_norm_eq_one_of_inverseOfBijective_isPositiveMap
    {T : MatrixEnd d} (hT : Function.Bijective T)
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hInvPos : IsPositiveMap (inverseOfBijective T hT)) :
    ‖channelDet T‖ = 1 := by
  have hInvTP : IsTracePreservingMap (inverseOfBijective T hT) :=
    inverseOfBijective_isTracePreservingMap hT hTP
  have hdetMul :
      channelDet T * channelDet (inverseOfBijective T hT) = 1 := by
    rw [← channelDet_comp, comp_inverseOfBijective, channelDet_id]
  have hnormMul :
      ‖channelDet T‖ * ‖channelDet (inverseOfBijective T hT)‖ = 1 := by
    rw [← norm_mul, hdetMul, norm_one]
  have hTle : ‖channelDet T‖ ≤ 1 :=
    channelDet_norm_le_one_of_positive_tracePreserving hPos hTP
  have hInvLe : ‖channelDet (inverseOfBijective T hT)‖ ≤ 1 :=
    channelDet_norm_le_one_of_positive_tracePreserving hInvPos hInvTP
  nlinarith [norm_nonneg (channelDet T),
    norm_nonneg (channelDet (inverseOfBijective T hT))]

/-- The inverse of a unitary conjugation is positive.  The proof uses the
explicit cone-surjectivity witness for congruence by an invertible matrix. -/
theorem inverseOfBijective_unitaryChannel_isPositiveMap
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (hU : Function.Bijective (unitaryChannel U)) :
    IsPositiveMap (inverseOfBijective (unitaryChannel U) hU) := by
  apply inverseOfBijective_isPositiveMap_of_mapsPSDConeOnto hU
  simpa only [unitaryChannel, unitaryConjLM] using
    unitaryConjLM_mapsPSDConeOnto (U : MatrixAlg d)
      (Matrix.UnitaryGroup.det_isUnit U)

/-- The inverse of unitary conjugation after ordinary transposition is
positive.  This is Wolf's transpose branch, which must not be removed by
strengthening the statement to complete positivity. -/
theorem inverseOfBijective_unitaryChannel_comp_transpose_isPositiveMap
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (hU : Function.Bijective ((unitaryChannel U).comp
      (Matrix.transposeLinearMapComplex (Fin d)))) :
    IsPositiveMap (inverseOfBijective
      ((unitaryChannel U).comp (Matrix.transposeLinearMapComplex (Fin d))) hU) := by
  apply inverseOfBijective_isPositiveMap_of_mapsPSDConeOnto hU
  simpa only [unitaryChannel, unitaryConjLM] using
    unitaryConjLM_comp_transpose_mapsPSDConeOnto
      (U : MatrixAlg d) (Matrix.UnitaryGroup.det_isUnit U)

end ChannelDeterminant.Internal
