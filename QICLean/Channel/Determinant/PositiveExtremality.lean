/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixTracePairing
import QICLean.Channel.Determinant.ChoiBound
import QICLean.Channel.Determinant.Composition
import QICLean.Channel.Determinant.HilbertSchmidt
import QICLean.Channel.Determinant.UnitaryCharacterization
import QICLean.Channel.Peripheral.CesaroRecurrence
import QICLean.Channel.Peripheral.AntilinearConjugation
import QICLean.Channel.PSDConeAutomorphism.RankPreservation
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Determinant extremality for positive trace-preserving maps

This file formalizes the saturation step in Wolf Theorem 6.1 for positive
trace-preserving maps.  If `‖det T‖ = 1`, all eigenvalues are peripheral, so
Wolf's Dirichlet recurrent powers converge to the identity.  Surjectivity of
`T` then shows that its inverse is positive, equivalently that `T` maps the
positive-semidefinite cone onto itself.  Wolf Proposition 3.6 and its existing
Wigner-theorem proof classify such cone automorphisms; trace preservation
normalizes the implementing matrix to a unitary.

The determinant sign of ordinary transposition, and hence the parity clause in
Wolf Theorem 6.1(3), are kept separate from this modulus-one classification.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.1.1][Wolf2012QChannels]

## Tags

quantum channel, positive map, determinant, recurrence, Wigner theorem
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

variable {d : ℕ}

local notation "MatrixAlg" => ChannelDeterminant.Internal.MatrixAlg
local notation "MatrixEnd" => ChannelDeterminant.Internal.MatrixEnd

namespace Module.End

/-- If every eigenvalue of a finite-dimensional complex endomorphism has
modulus one, its peripheral spectral subspace is the whole space. -/
theorem peripheralSubspace_eq_top_of_all_eigenvalues_norm_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V)
    (h : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ = 1) :
    T.peripheralSubspace = ⊤ := by
  have hset : peripheralEigenvalues T = {μ | T.HasEigenvalue μ} := by
    ext μ
    constructor
    · exact fun hμ ↦ hμ.1
    · exact fun hμ ↦ ⟨hμ, h μ hμ⟩
  rw [peripheralSubspace, hset, T.iSup_maxGenEigenspace_hasEigenvalue_eq_top]

/-- Under the same phase-spectrum hypothesis, the peripheral spectral
projection is the identity. -/
theorem peripheralProjection_eq_one_of_all_eigenvalues_norm_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V)
    (h : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ = 1) :
    T.peripheralProjection = 1 := by
  apply LinearMap.ext
  intro X
  simpa only [Module.End.one_apply] using T.peripheralProjection_apply_of_mem
    (show X ∈ T.peripheralSubspace by
      rw [T.peripheralSubspace_eq_top_of_all_eigenvalues_norm_one h]
      exact Submodule.mem_top)

end Module.End

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

private theorem pow_posSemidef_of_isPositiveMap
    {T : MatrixEnd d} (hPos : IsPositiveMap T)
    {X : MatrixAlg d} (hX : X.PosSemidef) (m : ℕ) :
    ((T ^ m) X).PosSemidef := by
  induction m with
  | zero => simpa using hX
  | succ m ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
      exact hPos _ ih

/-- The recurrent-power/positive-inverse step in Wolf Theorem 6.1(2).

For a positive trace-preserving `T` with determinant of modulus one, every
eigenvalue is peripheral.  The recurrent powers therefore converge to the
identity.  Applying the positive maps `T ^ (n_i - 1)` to a positive target and
passing to the closed positive-semidefinite cone shows that its unique
preimage under `T` is positive.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 369--380. -/
theorem mapsPSDConeOnto_of_channelDet_norm_eq_one [NeZero d]
    {T : MatrixEnd d} (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hdet : ‖channelDet T‖ = 1) :
    MapsPSDConeOnto T := by
  have hdet0 : channelDet T ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet
    exact zero_ne_one hdet
  have hbij : Function.Bijective T :=
    (channelDet_ne_zero_iff_bijective T).mp hdet0
  have hall : ∀ μ : ℂ, Module.End.HasEigenvalue T μ → ‖μ‖ = 1 :=
    channel_all_eigenvalues_norm_one_of_positive_tracePreserving hPos hTP hdet
  have hprojection : Module.End.peripheralProjection T = 1 :=
    Module.End.peripheralProjection_eq_one_of_all_eigenvalues_norm_one T hall
  refine ⟨hPos, ?_⟩
  intro A hA
  obtain ⟨X, hTX⟩ := hbij.2 A
  refine ⟨X, ?_, hTX⟩
  obtain ⟨n, hnmono, hn0, hn⟩ :=
    hPos.exists_strictMono_tendsto_pow_peripheralProjection hTP
  have hlim : Filter.Tendsto (fun i : ℕ ↦ (T ^ n i) X) Filter.atTop (nhds X) := by
    simpa only [hprojection, Module.End.one_apply] using hn X
  exact Matrix.posSemidef_is_closed.mem_of_tendsto hlim
    (Filter.Eventually.of_forall fun i ↦ by
      have hni : 0 < n i := lt_of_lt_of_le hn0 (hnmono.monotone (Nat.zero_le i))
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hni.ne'
      rw [hk, pow_succ, Module.End.mul_apply, hTX]
      exact pow_posSemidef_of_isPositiveMap hPos hA k)

private theorem conjTranspose_mul_self_eq_one_of_tracePreserving_conj
    {T : MatrixEnd d} (hTP : IsTracePreservingMap T) {Y : MatrixAlg d}
    (hconj : ∀ X, T X = Y * X * Yᴴ) :
    Yᴴ * Y = 1 := by
  refine sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff
    (M := Yᴴ * Y - 1)).1 ?_)
  intro X
  rw [Matrix.sub_mul, Matrix.trace_sub, one_mul]
  apply sub_eq_zero.mpr
  calc
    Matrix.trace ((Yᴴ * Y) * X) = Matrix.trace (Y * X * Yᴴ) := by
      simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle Y X Yᴴ).symm
    _ = Matrix.trace (T X) := congrArg Matrix.trace (hconj X).symm
    _ = Matrix.trace X := hTP X

private theorem conjTranspose_mul_self_eq_one_of_tracePreserving_transposeConj
    {T : MatrixEnd d} (hTP : IsTracePreservingMap T) {Y : MatrixAlg d}
    (htranspose : ∀ X, T X = Y * Xᵀ * Yᴴ) :
    Yᴴ * Y = 1 := by
  refine sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff
    (M := Yᴴ * Y - 1)).1 ?_)
  intro X
  rw [Matrix.sub_mul, Matrix.trace_sub, one_mul]
  apply sub_eq_zero.mpr
  calc
    Matrix.trace ((Yᴴ * Y) * X) = Matrix.trace (Y * X * Yᴴ) := by
      simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle Y X Yᴴ).symm
    _ = Matrix.trace (T Xᵀ) := by
      simpa only [Matrix.transpose_transpose] using
        congrArg Matrix.trace (htranspose Xᵀ).symm
    _ = Matrix.trace Xᵀ := hTP Xᵀ
    _ = Matrix.trace X := Matrix.trace_transpose X

/-- **Wolf Theorem 6.1(2), positive trace-preserving forward direction.**

Determinant saturation makes `T` a positive-cone automorphism by the recurrent
power argument.  The existing formalization of Wolf Proposition 3.6 (whose
classification step uses the project's Wigner theorem) gives conjugation or
transpose-conjugation by an invertible matrix.  Trace preservation makes that
matrix unitary. -/
theorem exists_unitary_or_transpose_of_channelDet_norm_eq_one [NeZero d]
    {T : MatrixEnd d} (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hdet : ‖channelDet T‖ = 1) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      T = unitaryChannel U ∨
      T = (unitaryChannel U).comp (Matrix.transposeLinearMapComplex (Fin d)) := by
  have hcone : MapsPSDConeOnto T :=
    mapsPSDConeOnto_of_channelDet_norm_eq_one hPos hTP hdet
  obtain ⟨Y, _hY, hconj | htranspose⟩ :=
    hPos.exists_isUnit_det_conj_or_transpose_of_preserves_hermitian_rank
      (fun H hH ↦ hcone.rank_eq_of_isHermitian hH)
  · have hYY : Yᴴ * Y = 1 :=
      conjTranspose_mul_self_eq_one_of_tracePreserving_conj hTP hconj
    let U : Matrix.unitaryGroup (Fin d) ℂ :=
      ⟨Y, Matrix.mem_unitaryGroup_iff'.2 (by
        simpa only [Matrix.star_eq_conjTranspose] using hYY)⟩
    refine ⟨U, Or.inl (LinearMap.ext fun X ↦ ?_)⟩
    simpa only [unitaryChannel, LinearMap.coe_mk, AddHom.coe_mk, U] using hconj X
  · have hYY : Yᴴ * Y = 1 :=
      conjTranspose_mul_self_eq_one_of_tracePreserving_transposeConj hTP htranspose
    let U : Matrix.unitaryGroup (Fin d) ℂ :=
      ⟨Y, Matrix.mem_unitaryGroup_iff'.2 (by
        simpa only [Matrix.star_eq_conjTranspose] using hYY)⟩
    refine ⟨U, Or.inr (LinearMap.ext fun X ↦ ?_)⟩
    change T X = Y * Xᵀ * Yᴴ
    exact htranspose X

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

/-- **Wolf Theorem 6.1(2), positive trace-preserving form.**

For `d > 0`, a positive trace-preserving map has determinant of modulus one
exactly when it is unitary conjugation or unitary conjugation after ordinary
matrix transposition.  The `NeZero d` assumption is the explicit Lean form of
Wolf's positive matrix-dimension convention.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 351--400. -/
theorem channelDet_norm_eq_one_iff_exists_unitary_or_transpose_of_positive_tracePreserving
    [NeZero d] {T : MatrixEnd d}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ‖channelDet T‖ = 1 ↔
      ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
        T = unitaryChannel U ∨
        T = (unitaryChannel U).comp (Matrix.transposeLinearMapComplex (Fin d)) := by
  constructor
  · exact exists_unitary_or_transpose_of_channelDet_norm_eq_one hPos hTP
  · rintro ⟨U, rfl | rfl⟩
    · exact channelDet_norm_eq_one_of_unitaryChannel U
    · exact channelDet_norm_eq_one_of_unitaryChannel_comp_transpose U

/-- **Wolf Theorem 6.1(3).**  For a positive trace-preserving map in positive
matrix dimension, determinant `-1` occurs exactly for a unitary conjugation
after ordinary transposition in a dimension for which `⌊d/2⌋` is odd.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 358--406. -/
theorem channelDet_eq_neg_one_iff_exists_unitary_transpose_of_positive_tracePreserving
    [NeZero d] {T : MatrixEnd d}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    channelDet T = -1 ↔
      Odd (d / 2) ∧ ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
        T = (unitaryChannel U).comp (Matrix.transposeLinearMapComplex (Fin d)) := by
  constructor
  · intro hdet
    have hnorm : ‖channelDet T‖ = 1 := by rw [hdet, norm_neg, norm_one]
    obtain ⟨U, hunitary | htranspose⟩ :=
      exists_unitary_or_transpose_of_channelDet_norm_eq_one hPos hTP hnorm
    · have hone : channelDet T = 1 := by
        rw [hunitary, channelDet_unitary_eq_one]
      rw [hdet] at hone
      exact (by norm_num at hone)
    · have htransposeDet :
          channelDet (Matrix.transposeLinearMapComplex (Fin d)) = -1 := by
        rw [htranspose, channelDet_comp, channelDet_unitary_eq_one, one_mul] at hdet
        exact hdet
      exact ⟨channelDet_transposeLinearMapComplex_eq_neg_one_iff.mp htransposeDet,
        U, htranspose⟩
  · rintro ⟨hodd, U, rfl⟩
    rw [channelDet_comp, channelDet_unitary_eq_one, one_mul,
      channelDet_transposeLinearMapComplex_eq_neg_one_iff.mpr hodd]

/-- **Wolf Theorem 6.1(3), determinant-one converse in the odd-parity
dimensions.**  If `⌊d/2⌋` is odd, the transpose branch has determinant
`-1`; hence a positive trace-preserving map has determinant `1` exactly when it
is a unitary conjugation. -/
theorem channelDet_eq_one_iff_exists_unitary_of_positive_tracePreserving_of_odd
    [NeZero d] {T : MatrixEnd d}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hodd : Odd (d / 2)) :
    channelDet T = 1 ↔
      ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U := by
  constructor
  · intro hdet
    have hnorm : ‖channelDet T‖ = 1 := by rw [hdet, norm_one]
    obtain ⟨U, hunitary | htranspose⟩ :=
      exists_unitary_or_transpose_of_channelDet_norm_eq_one hPos hTP hnorm
    · exact ⟨U, hunitary⟩
    · have hneg : channelDet T = -1 := by
        rw [htranspose, channelDet_comp, channelDet_unitary_eq_one, one_mul,
          channelDet_transposeLinearMapComplex_eq_neg_one_iff.mpr hodd]
      rw [hdet] at hneg
      exact (by norm_num at hneg)
  · rintro ⟨U, rfl⟩
    exact channelDet_unitary_eq_one U

end Internal

end ChannelDeterminant
