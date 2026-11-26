/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Matrix.MatrixAux
import QICLean.Channel.Determinant.ChoiBound
import QICLean.Channel.Determinant.Composition
import QICLean.Channel.Determinant.UnitaryCharacterization
import QICLean.Channel.Schwarz.AbstractMultiplicativeDomain
import QICLean.Channel.TransferMatrix
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Determinants of positive trace-preserving maps and of transposition

This file formalizes the parts of Wolf Theorem 6.1 for positive
trace-preserving maps that need only the determinant: the determinant of a
Hermiticity-preserving map is real, so that of a positive trace-preserving map
lies in `[-1, 1]`; ordinary transposition has determinant
`(-1)^(d(d-1)/2)`, of modulus one; and the transpose-conjugation branch
saturates the determinant bound.

It also develops the inverse-map interface needed for Wolf's corollary on
positive invertible maps.  The inverse of a bijective trace-preserving map is
trace preserving, positivity of that inverse is equivalent to the original
positive map carrying the positive-semidefinite cone onto itself, and the
determinant bounds for a map and its positive inverse force determinant
modulus one.  Ordinary transposition, even after an outer unitary
conjugation, is not a Schwarz map in matrix dimension at least two; in
dimension one it is the identity.

The determinant-saturation classification (Wolf Theorem 6.1(2) and (3)) and
the positive-invertible-map corollary need the recurrence of the peripheral
projection and Wolf Proposition 3.6; they are in
`QICLean.Channel.Determinant.PositiveInverse`.

## Main results

* `ChannelDeterminant.Internal.channelDet_transposeLinearMapComplex`: the
  determinant of ordinary transposition.
* `ChannelDeterminant.Internal.channelDet_transposeLinearMapComplex_eq_neg_one_iff`:
  transposition has determinant `-1` exactly when `⌊d/2⌋` is odd.
* `ChannelDeterminant.Internal.channelDet_star_eq_of_map_conjTranspose`: the
  determinant of a Hermiticity-preserving map is real.
* `ChannelDeterminant.Internal.exists_real_channelDet_mem_Icc_of_positive_tracePreserving`:
  Wolf Theorem 6.1(1).
* `ChannelDeterminant.Internal.channelDet_norm_eq_one_of_unitaryChannel_comp_transpose`:
  the transpose branch saturates the determinant bound.
* `ChannelDeterminant.Internal.inverseOfBijective_isPositiveMap_iff_mapsPSDConeOnto`:
  positivity of the inverse is surjectivity on the positive-semidefinite cone.
* `ChannelDeterminant.Internal.channelDet_norm_eq_one_of_inverseOfBijective_isPositiveMap`:
  a positive inverse forces determinant modulus one.
* `ChannelDeterminant.Internal.unitaryChannel_comp_transpose_not_isSchwarzMap`:
  the transpose branch is not Schwarz in matrix dimension at least two.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.1.1][Wolf2012QChannels]

## Tags

quantum channel, positive map, determinant, transposition, inverse
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

variable {d : ℕ}

local notation "MatrixAlg" => ChannelDeterminant.Internal.MatrixAlg
local notation "MatrixEnd" => ChannelDeterminant.Internal.MatrixEnd

namespace ChannelDeterminant

namespace Internal

/-- The matrix-unit index involution induced by ordinary transposition. -/
def matrixBasisTransposePerm (d : ℕ) : Equiv.Perm (MatrixBasisIndex d) where
  toFun := fun ⟨i, j, u⟩ ↦ ⟨j, i, u⟩
  invFun := fun ⟨i, j, u⟩ ↦ ⟨j, i, u⟩
  left_inv := by rintro ⟨i, j, u⟩; rfl
  right_inv := by rintro ⟨i, j, u⟩; rfl

@[simp] theorem matrixBasisTransposePerm_apply (i j : Fin d) (u : Unit) :
    matrixBasisTransposePerm d (i, j, u) = (j, i, u) := rfl

/-- In the standard matrix-unit basis, ordinary transposition is the
pair-swap permutation matrix. -/
theorem channelMatrix_transposeLinearMapComplex :
    channelMatrix (Matrix.transposeLinearMapComplex (Fin d)) =
      (matrixBasisTransposePerm d).permMatrix ℂ := by
  ext ⟨i, j, u⟩ ⟨k, l, v⟩
  simp [channelMatrix_apply, Matrix.transposeLinearMapComplex,
    Matrix.transposeLinearEquiv_apply,
    Matrix.transpose_apply, Matrix.single_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    matrixBasisTransposePerm, eq_comm]

private theorem card_fixedPoints_matrixBasisTransposePerm :
    Fintype.card (Function.fixedPoints (matrixBasisTransposePerm d)) = d := by
  classical
  let e : Fin d ≃ Function.fixedPoints (matrixBasisTransposePerm d) :=
    { toFun := fun i ↦ ⟨(i, i, ()), by rfl⟩
      invFun := fun x ↦ x.1.1
      left_inv := fun i ↦ rfl
      right_inv := by
        rintro ⟨⟨i, j, u⟩, h⟩
        have hji : j = i := congrArg Prod.fst h
        subst j
        cases u
        rfl }
  simpa using (Fintype.card_congr e).symm

private theorem matrixBasisTransposePerm_sq :
    matrixBasisTransposePerm d ^ 2 = 1 := by
  apply Equiv.ext
  rintro ⟨i, j, u⟩
  rfl

/-- The determinant of ordinary transposition.  The pair-swap fixes the `d`
diagonal matrix units and exchanges the remaining `d²-d` units in pairs, so
its sign is `(-1)^(d(d-1)/2)`, exactly the count in Wolf Theorem 6.1(3).

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 395--406. -/
theorem channelDet_transposeLinearMapComplex :
    channelDet (Matrix.transposeLinearMapComplex (Fin d)) =
      (-1 : ℂ) ^ (d * (d - 1) / 2) := by
  change (channelMatrix (Matrix.transposeLinearMapComplex (Fin d))).det = _
  rw [channelMatrix_transposeLinearMapComplex, Matrix.det_permutation,
    Equiv.Perm.sign_of_pow_two_eq_one matrixBasisTransposePerm_sq]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_unit,
    mul_one, card_fixedPoints_matrixBasisTransposePerm, Units.val_pow_eq_pow_val,
    Units.coe_neg_one, Int.cast_pow, Int.cast_neg, Int.cast_one]
  congr 1
  rw [Nat.mul_sub_left_distrib, mul_one]

/-- Wolf's parity rewrite: the number `d(d-1)/2` of antisymmetric
off-diagonal Hermitian basis elements is odd exactly when `⌊d/2⌋` is odd. -/
theorem odd_mul_pred_div_two_iff_odd_div_two :
    Odd (d * (d - 1) / 2) ↔ Odd (d / 2) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' d
  · subst d
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hpred : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
      rw [hpred]
      have hcalc :
          2 * k * (2 * (k - 1) + 1) / 2 = k * (2 * (k - 1) + 1) := by
        rw [show 2 * k * (2 * (k - 1) + 1) =
            2 * (k * (2 * (k - 1) + 1)) by ring,
          Nat.mul_div_cancel_left _ zero_lt_two]
      rw [hcalc, Nat.mul_div_cancel_left k zero_lt_two, Nat.odd_mul]
      simp only [odd_two_mul_add_one, and_true]
  · subst d
    have hpred : 2 * k + 1 - 1 = 2 * k := by omega
    rw [hpred]
    have hcalc : (2 * k + 1) * (2 * k) / 2 = (2 * k + 1) * k := by
      rw [show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring,
        Nat.mul_div_cancel_left _ zero_lt_two]
    have hdiv : (2 * k + 1) / 2 = k := by omega
    rw [hcalc, hdiv, Nat.odd_mul]
    simp only [odd_two_mul_add_one, true_and]

/-- Ordinary transposition has determinant `-1` exactly in Wolf's dimensions:
those for which `⌊d/2⌋` is odd. -/
theorem channelDet_transposeLinearMapComplex_eq_neg_one_iff :
    channelDet (Matrix.transposeLinearMapComplex (Fin d)) = -1 ↔
      Odd (d / 2) := by
  rw [channelDet_transposeLinearMapComplex,
    neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℂ) ≠ 1),
    odd_mul_pred_div_two_iff_odd_div_two]

private theorem channelMatrix_entrywiseConjTransport
    (T : MatrixEnd d) :
    channelMatrix (entrywiseConjTransport T) =
      (channelMatrix T).map (starRingEnd ℂ) := by
  ext ⟨i, j, u⟩ ⟨k, l, v⟩
  simp only [channelMatrix_apply, entrywiseConjTransport_apply, Matrix.map_apply,
    starRingEnd_apply]
  change star (T ((Matrix.single k l (1 : ℂ)).map (starRingEnd ℂ)) i j) = _
  simp only [Matrix.map_single, map_one]

/-- Anti-linear conjugation of a matrix endomorphism conjugates its channel
determinant. -/
private theorem channelDet_entrywiseConjTransport (T : MatrixEnd d) :
    channelDet (entrywiseConjTransport T) = star (channelDet T) := by
  change (channelMatrix (entrywiseConjTransport T)).det = star (channelMatrix T).det
  rw [channelMatrix_entrywiseConjTransport]
  simpa only [RingHom.mapMatrix_apply, starRingEnd_apply] using
    (RingHom.map_det (starRingEnd ℂ) (channelMatrix T)).symm

private theorem entrywiseConjTransport_eq_transpose_comp_of_map_conjTranspose
    (T : MatrixEnd d) (hHP : ∀ X, T Xᴴ = (T X)ᴴ) :
    entrywiseConjTransport T =
      (Matrix.transposeLinearMapComplex (Fin d)).comp
        (T.comp (Matrix.transposeLinearMapComplex (Fin d))) := by
  apply LinearMap.ext
  intro X
  ext i j
  change star (T (X.map (starRingEnd ℂ)) i j) = T Xᵀ j i
  have hX : (X.map (starRingEnd ℂ))ᴴ = Xᵀ := by
    ext k l
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, starRingEnd_apply,
      star_star, Matrix.transpose_apply]
  have h := congrFun (congrFun (hHP (X.map (starRingEnd ℂ))) j) i
  rw [hX] at h
  simpa only [Matrix.conjTranspose_apply] using h.symm

private theorem transpose_comp_self :
    (Matrix.transposeLinearMapComplex (Fin d)).comp
        (Matrix.transposeLinearMapComplex (Fin d)) = (1 : MatrixEnd d) := by
  apply LinearMap.ext
  intro X
  change Xᵀᵀ = X
  exact Matrix.transpose_transpose X

/-- The channel determinant of a Hermiticity-preserving complex-linear map is
real.  Positive maps are Hermiticity-preserving, so this is Wolf's
conjugate-paired-spectrum step in Theorem 6.1(1), stated at its natural
linearity boundary.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 364--367. -/
theorem channelDet_star_eq_of_map_conjTranspose
    {T : MatrixEnd d} (hHP : ∀ X, T Xᴴ = (T X)ᴴ) :
    star (channelDet T) = channelDet T := by
  let R : MatrixEnd d := Matrix.transposeLinearMapComplex (Fin d)
  have hRdet : channelDet R * channelDet R = 1 := by
    rw [← channelDet_comp, show R.comp R = 1 from transpose_comp_self,
      channelDet_id]
  calc
    star (channelDet T) = channelDet (entrywiseConjTransport T) :=
      (channelDet_entrywiseConjTransport T).symm
    _ = channelDet (R.comp (T.comp R)) := by
      rw [entrywiseConjTransport_eq_transpose_comp_of_map_conjTranspose T hHP]
    _ = channelDet R * (channelDet T * channelDet R) := by
      rw [channelDet_comp, channelDet_comp]
    _ = channelDet T * (channelDet R * channelDet R) := by ring
    _ = channelDet T := by rw [hRdet, mul_one]

/-- Positive maps have real channel determinant. -/
theorem channelDet_star_eq_of_isPositiveMap {T : MatrixEnd d}
    (hPos : IsPositiveMap T) :
    star (channelDet T) = channelDet T :=
  channelDet_star_eq_of_map_conjTranspose hPos.map_conjTranspose

/-- **Wolf Theorem 6.1(1).**  The determinant of a positive trace-preserving
map is a real number in `[-1, 1]`.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 351--367. -/
theorem exists_real_channelDet_mem_Icc_of_positive_tracePreserving
    {T : MatrixEnd d} (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ∃ r : ℝ, r ∈ Set.Icc (-1) 1 ∧ channelDet T = r := by
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp (by
    simpa only [Complex.star_def] using channelDet_star_eq_of_isPositiveMap hPos)
  have habs : |r| ≤ 1 := by
    simpa only [hr, Complex.norm_real, Real.norm_eq_abs] using
      channelDet_norm_le_one_of_positive_tracePreserving hPos hTP
  exact ⟨r, (abs_le.mp habs), hr⟩

/-- Ordinary matrix transposition has determinant of modulus one.  This is the
modulus-only consequence of its being a linear involution; the exact sign is
the separate parity computation in Wolf Theorem 6.1(3). -/
theorem channelDet_transpose_norm_eq_one :
    ‖channelDet (Matrix.transposeLinearMapComplex (Fin d))‖ = 1 := by
  let R : MatrixEnd d := Matrix.transposeLinearMapComplex (Fin d)
  have hcomp : R.comp R = 1 := by
    apply LinearMap.ext
    intro X
    change Xᵀᵀ = X
    exact Matrix.transpose_transpose X
  have hmul : channelDet R * channelDet R = 1 := by
    rw [← channelDet_comp, hcomp, channelDet_id]
  have hnorm : ‖channelDet R‖ * ‖channelDet R‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  change ‖channelDet R‖ = 1
  nlinarith [norm_nonneg (channelDet R)]

/-- The transpose-conjugation branch in Wolf Theorem 6.1(2) saturates the
determinant-modulus bound. -/
theorem channelDet_norm_eq_one_of_unitaryChannel_comp_transpose
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖channelDet ((unitaryChannel U).comp
      (Matrix.transposeLinearMapComplex (Fin d)))‖ = 1 := by
  rw [channelDet_comp, channelDet_unitary_eq_one, one_mul,
    channelDet_transpose_norm_eq_one]

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
invertible-map corollary.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 423--426. -/
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

private theorem unitaryChannel_comp_inv
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (unitaryChannel U).comp (unitaryChannel U⁻¹) = 1 := by
  have hUUInv : (U : MatrixAlg d) * (U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) = 1 :=
    congrArg Subtype.val (mul_inv_cancel U)
  have hUInvStarUStar :
      ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : MatrixAlg d)ᴴ *
          (U : MatrixAlg d)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hUUInv, Matrix.conjTranspose_one]
  apply LinearMap.ext
  intro X
  change (U : MatrixAlg d) *
      (((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : MatrixAlg d) * X *
        ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : MatrixAlg d)ᴴ) *
      (U : MatrixAlg d)ᴴ = X
  rw [show (U : MatrixAlg d) *
      (((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : MatrixAlg d) * X *
        ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : MatrixAlg d)ᴴ) *
      (U : MatrixAlg d)ᴴ =
        ((U : MatrixAlg d) *
          ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : MatrixAlg d)) * X *
          (((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : MatrixAlg d)ᴴ *
            (U : MatrixAlg d)ᴴ) by simp only [Matrix.mul_assoc],
    hUUInv, hUInvStarUStar, Matrix.one_mul, Matrix.mul_one]

/-- The inverse of unitary conjugation is conjugation by the inverse unitary. -/
theorem inverseOfBijective_unitaryChannel
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (hU : Function.Bijective (unitaryChannel U)) :
    inverseOfBijective (unitaryChannel U) hU = unitaryChannel U⁻¹ := by
  apply LinearMap.ext
  intro X
  apply hU.1
  rw [apply_inverseOfBijective]
  symm
  simpa only [LinearMap.comp_apply, Module.End.one_apply] using
    LinearMap.congr_fun (unitaryChannel_comp_inv U) X

/-- The inverse of `Ad U` after ordinary transposition is ordinary
transposition after `Ad U⁻¹`; the reversed composition order is essential. -/
theorem inverseOfBijective_unitaryChannel_comp_transpose
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (hU : Function.Bijective ((unitaryChannel U).comp
      (Matrix.transposeLinearMapComplex (Fin d)))) :
    inverseOfBijective
        ((unitaryChannel U).comp (Matrix.transposeLinearMapComplex (Fin d))) hU =
      (Matrix.transposeLinearMapComplex (Fin d)).comp (unitaryChannel U⁻¹) := by
  apply LinearMap.ext
  intro X
  apply hU.1
  rw [apply_inverseOfBijective]
  have hInv := LinearMap.congr_fun (unitaryChannel_comp_inv U) X
  symm
  change unitaryChannel U
    (((unitaryChannel U⁻¹ X)ᵀ)ᵀ) = X
  simpa only [Matrix.transpose_transpose, LinearMap.comp_apply,
    Module.End.one_apply] using hInv

/-- The inverse of a unitary conjugation is positive.  The proof uses the
explicit inverse standard form. -/
theorem inverseOfBijective_unitaryChannel_isPositiveMap
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (hU : Function.Bijective (unitaryChannel U)) :
    IsPositiveMap (inverseOfBijective (unitaryChannel U) hU) := by
  rw [inverseOfBijective_unitaryChannel U hU]
  exact unitaryChannel_isPositiveMap U⁻¹

/-- The inverse of unitary conjugation after ordinary transposition is
positive.  This is Wolf's transpose branch, which must not be removed by
strengthening the statement to complete positivity. -/
theorem inverseOfBijective_unitaryChannel_comp_transpose_isPositiveMap
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (hU : Function.Bijective ((unitaryChannel U).comp
      (Matrix.transposeLinearMapComplex (Fin d)))) :
    IsPositiveMap (inverseOfBijective
      ((unitaryChannel U).comp (Matrix.transposeLinearMapComplex (Fin d))) hU) := by
  rw [inverseOfBijective_unitaryChannel_comp_transpose U hU]
  intro X hX
  exact Matrix.transposeLinearMapComplex_isPositiveMap _
    (unitaryChannel_isPositiveMap U⁻¹ X hX)

/-- Ordinary matrix transposition is not a Schwarz map in matrix dimension at
least two.

For the matrix unit \(A=E_{01}\), the Schwarz defect of transposition is
\(E_{11}-E_{00}\), whose \(00\)-entry is negative.

Source: Wolf Theorem 6.16, proof line 1663 of
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`. -/
theorem transposeLinearMapComplex_not_isSchwarzMap (hd : 2 ≤ d) :
    ¬ IsSchwarzMap (Matrix.transposeLinearMapComplex (Fin d)) := by
  classical
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  intro hSchwarz
  have hDefect := hSchwarz (Matrix.single i j 1)
  have hDiag := hDefect.diag_nonneg (i := i)
  norm_num [Matrix.transposeLinearMapComplex, Matrix.single,
    Matrix.conjTranspose, Matrix.mul_apply, i, j] at hDiag

/-- Removing an outer unitary conjugation from a Schwarz map preserves the
Schwarz property of the inner map.

The proof conjugates the Schwarz defect back by \(U^\dagger\); this is the
order-automorphism step used to show that unitary conjugation cannot repair
the transpose defect in Wolf Theorem 6.16. -/
theorem isSchwarzMap_of_unitaryChannel_comp
    (U : Matrix.unitaryGroup (Fin d) ℂ) {E : MatrixEnd d}
    (hE : IsSchwarzMap ((unitaryChannel U).comp E)) :
    IsSchwarzMap E := by
  have hStarU : (U : MatrixAlg d)ᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.UnitaryGroup.star_mul_self U
  have hCancel (X : MatrixAlg d) :
      (U : MatrixAlg d)ᴴ * ((U : MatrixAlg d) * X) = X := by
    rw [← Matrix.mul_assoc, hStarU, Matrix.one_mul]
  intro A
  have hDefect := hE A
  have hBack := hDefect.conjTranspose_mul_mul_same (U : MatrixAlg d)
  have hEq :
      (U : MatrixAlg d)ᴴ *
          (((unitaryChannel U).comp E) (Aᴴ * A) -
            ((unitaryChannel U).comp E) Aᴴ *
              ((unitaryChannel U).comp E) A) *
          (U : MatrixAlg d) =
        E (Aᴴ * A) - E Aᴴ * E A := by
    simp only [LinearMap.comp_apply, unitaryChannel, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      hCancel, hStarU, Matrix.mul_one]
  rw [hEq] at hBack
  exact hBack

/-- Unitary conjugation after ordinary transposition is not a Schwarz map in
matrix dimension at least two.

This is the standard-form branch excluded at Wolf Theorem 6.16, proof
line 1663. -/
theorem unitaryChannel_comp_transpose_not_isSchwarzMap (hd : 2 ≤ d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ¬ IsSchwarzMap ((unitaryChannel U).comp
      (Matrix.transposeLinearMapComplex (Fin d))) := by
  intro hSchwarz
  exact transposeLinearMapComplex_not_isSchwarzMap hd
    (isSchwarzMap_of_unitaryChannel_comp U hSchwarz)

/-- In matrix dimension one, ordinary transposition is the identity, so
unitary conjugation after transposition collapses to the unitary branch.

This packages the one-dimensional case tacitly included in Wolf Theorem 6.16,
proof lines 1660--1663. -/
theorem unitaryChannel_comp_transpose_fin_one
    (U : Matrix.unitaryGroup (Fin 1) ℂ) :
    (unitaryChannel U).comp (Matrix.transposeLinearMapComplex (Fin 1)) =
      unitaryChannel U := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply]
  congr 1
  ext i j
  rw [show i = j from Subsingleton.elim i j]
  simp [Matrix.transposeLinearMapComplex]

end Internal

end ChannelDeterminant
