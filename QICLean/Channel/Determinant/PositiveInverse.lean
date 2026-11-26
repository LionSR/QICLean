/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Matrix.MatrixTracePairing
import QICLean.Channel.Determinant.PositiveExtremality
import QICLean.Channel.Peripheral.Projection.CesaroRecurrence
import QICLean.Channel.PSDConeAutomorphism.RankPreservation

/-!
# Determinant saturation and positive invertible maps

This file formalizes the saturation step in Wolf Theorem 6.1 for positive
trace-preserving maps.  If `‖det T‖ = 1`, all eigenvalues are peripheral, so
Wolf's Dirichlet recurrent powers converge to the identity.  Surjectivity of
`T` then shows that its inverse is positive, equivalently that `T` maps the
positive-semidefinite cone onto itself.  Wolf Proposition 3.6 and its existing
Wigner-theorem proof classify such cone automorphisms; trace preservation
normalizes the implementing matrix to a unitary.

The determinant sign of ordinary transposition, and hence the parity clause in
Wolf Theorem 6.1(3), are computed in
`QICLean.Channel.Determinant.PositiveExtremality`, together with the
inverse-map interface used here.

Wolf's corollary on positive invertible maps follows: determinant bounds for a
map and its inverse force determinant modulus one, after which Wolf Theorem
6.1 supplies unitary conjugation or unitary conjugation after ordinary matrix
transposition.  The proof of Wolf Theorem 6.16 later applies this
classification to its block maps.  There the Schwarz inequality excludes the
transpose branch in matrix dimension at least two, while ordinary
transposition is the identity in dimension one.

## Main results

* `Module.End.peripheralProjection_eq_one_of_all_eigenvalues_norm_one`: with
  only peripheral eigenvalues, the peripheral projection is the identity.
* `ChannelDeterminant.Internal.mapsPSDConeOnto_of_channelDet_norm_eq_one`:
  determinant saturation makes a positive trace-preserving map a cone
  automorphism.
* `channelDet_norm_eq_one_iff_exists_unitary_or_transpose_of_positive_tracePreserving`
  (in `ChannelDeterminant.Internal`):
  Wolf Theorem 6.1(2) for positive trace-preserving maps.
* `channelDet_eq_neg_one_iff_exists_unitary_transpose_of_positive_tracePreserving`
  (in `ChannelDeterminant.Internal`):
  Wolf Theorem 6.1(3).
* `ChannelDeterminant.Internal.wolfPositiveInvertibleMaps`: Wolf's corollary on
  positive invertible maps.
* `ChannelDeterminant.Internal.wolfPositiveInvertibleSchwarzMaps`: the Schwarz
  condition excludes transposition (Wolf Theorem 6.16).

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.1.1][Wolf2012QChannels]

## Tags

quantum channel, positive map, determinant, recurrence, Wigner theorem, inverse
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

/-- **Wolf Corollary: positive invertible maps.**

For a positive trace-preserving bijection on a nonzero matrix algebra, the
inverse is positive exactly for unitary conjugations and unitary conjugations
after ordinary matrix transposition.  The forward direction follows Wolf's
determinant argument: the determinant bounds for `T` and `T⁻¹`, together with
multiplicativity, force `|det T| = 1`, so Wolf Theorem 6.1 applies.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 416--426. -/
theorem wolfPositiveInvertibleMaps [NeZero d]
    {T : MatrixEnd d} (hT : Function.Bijective T)
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    IsPositiveMap (inverseOfBijective T hT) ↔
      ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
        T = unitaryChannel U ∨
        T = (unitaryChannel U).comp
          (Matrix.transposeLinearMapComplex (Fin d)) := by
  constructor
  · intro hInvPos
    exact exists_unitary_or_transpose_of_channelDet_norm_eq_one hPos hTP
      (channelDet_norm_eq_one_of_inverseOfBijective_isPositiveMap
        hT hPos hTP hInvPos)
  · rintro ⟨U, hTUnitary | hTTranspose⟩
    · subst T
      exact inverseOfBijective_unitaryChannel_isPositiveMap U hT
    · subst T
      exact inverseOfBijective_unitaryChannel_comp_transpose_isPositiveMap U hT

/-- **Wolf Theorem 6.16: the Schwarz condition excludes transposition.**

A positive trace-preserving bijection with positive inverse that also
satisfies the Schwarz inequality is unitary conjugation.  Wolf's positive
invertible-map corollary gives unitary conjugation or unitary conjugation after
ordinary transposition.  The latter is not Schwarz for \(d\geq 2\), and for
\(d=1\) it is already the unitary branch.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`,
lines 1660--1663. -/
theorem wolfPositiveInvertibleSchwarzMaps [NeZero d]
    {T : MatrixEnd d} (hT : Function.Bijective T)
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hInvPos : IsPositiveMap (inverseOfBijective T hT))
    (hSchwarz : IsSchwarzMap T) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U := by
  obtain ⟨U, hUnitary | hTranspose⟩ :=
    (wolfPositiveInvertibleMaps hT hPos hTP).mp hInvPos
  · exact ⟨U, hUnitary⟩
  · by_cases hdOne : d = 1
    · subst d
      rw [unitaryChannel_comp_transpose_fin_one] at hTranspose
      exact ⟨U, hTranspose⟩
    · have hdPos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
      have hdTwo : 2 ≤ d := by omega
      rw [hTranspose] at hSchwarz
      exact (unitaryChannel_comp_transpose_not_isSchwarzMap hdTwo U hSchwarz).elim

end Internal

end ChannelDeterminant
