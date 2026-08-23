/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixSqrt
import QICLean.Channel.Schwarz.PositiveMapProperties
import QICLean.Channel.TransferMatrix
import QICLean.Channel.Wigner.SpectrumPreserver
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Positive Hermitian-rank preservers

This file proves implication (2) to (3) of Wolf's Proposition 3.6,
"Automorphisms and rank preserving maps". A positive complex-linear map on a
full matrix algebra that preserves the rank of every Hermitian matrix is an
invertible congruence, possibly after transposition.

The proof follows Wolf's route. First, rank drops of scalar shifts are used to
show that a unital Hermitian-rank preserver preserves the spectrum of every
Hermitian matrix. The existing Corollary 1.1 spectrum-preserver classification
then gives a unitary standard form. For a general positive rank preserver, the
map is normalized by the inverse square root of `T 1`, and the normalization is
undone with the corrected factor `Y = (T 1)^{1/2} U`.

## Main declarations

* `Matrix.isUnit_iff_rank_eq_card`: a square complex matrix is invertible
  exactly when it has full rank.
* `Matrix.mem_spectrum_iff_rank_sub_smul_one_lt_card`: membership in the
  matrix spectrum is equivalent to a rank drop of the scalar shift.
* `IsPositiveMap.preserves_hermitian_spectrum_of_unital_of_preserves_hermitian_rank`:
  Wolf's normalized rank-drop argument.
* `IsPositiveMap.exists_isUnit_det_conj_or_transpose_of_preserves_hermitian_rank`:
  implication (2) to (3) of Wolf Proposition 3.6.

## Reference

M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
Proposition 3.6; local source
`Notes/WolfNoteTexSource/ch03_positive_not_completely.tex`, lines 652--683.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {d : ℕ}

/-- A square complex matrix is invertible exactly when it has full rank.

This is the finite-dimensional linear-algebra bridge used in Wolf's rank-drop
description of the spectrum in the proof of Proposition 3.6. -/
theorem isUnit_iff_rank_eq_card (A : Matrix (Fin d) (Fin d) ℂ) :
    IsUnit A ↔ A.rank = d := by
  constructor
  · intro hA
    simpa only [Fintype.card_fin] using Matrix.rank_of_isUnit A hA
  · intro hA
    apply Matrix.mulVec_surjective_iff_isUnit.mp
    change Function.Surjective A.mulVecLin
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using hA

/-- A scalar belongs to the spectrum of a square complex matrix exactly when
subtracting that scalar from the matrix lowers its rank.

This is the rank-drop criterion recalled in Wolf's proof of Proposition 3.6.
It includes the zero-dimensional matrix algebra. -/
theorem mem_spectrum_iff_rank_sub_smul_one_lt_card
    (A : Matrix (Fin d) (Fin d) ℂ) (z : ℂ) :
    z ∈ spectrum ℂ A ↔
      (A - z • (1 : Matrix (Fin d) (Fin d) ℂ)).rank < d := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  rw [show z • (1 : Matrix (Fin d) (Fin d) ℂ) - A =
      -(A - z • (1 : Matrix (Fin d) (Fin d) ℂ)) by abel,
    IsUnit.neg_iff, Matrix.isUnit_iff_rank_eq_card]
  have hle := Matrix.rank_le_width
    (A - z • (1 : Matrix (Fin d) (Fin d) ℂ))
  omega

end Matrix

variable {d : ℕ}

/-- Every spectral value of a Hermitian complex matrix is real. -/
private theorem exists_real_eq_of_mem_spectrum_of_isHermitian
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z ∈ spectrum ℂ A) : ∃ r : ℝ, (r : ℂ) = z := by
  rw [hA.spectrum_eq_image_range] at hz
  rcases hz with ⟨r, ⟨i, rfl⟩, rfl⟩
  exact ⟨hA.eigenvalues i, rfl⟩

/-- A positive unital map that preserves the rank of Hermitian matrices
preserves their spectra as sets.

This is Wolf's normalized rank-drop argument in the proof of Proposition 3.6:
for real `r`, unitality identifies the image of `H - r • 1` with
`T H - r • 1`, and the equality of ranks identifies the two spectra. -/
theorem IsPositiveMap.preserves_hermitian_spectrum_of_unital_of_preserves_hermitian_rank
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hRank : ∀ H : Matrix (Fin d) (Fin d) ℂ,
      H.IsHermitian → (T H).rank = H.rank)
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    spectrum ℂ (T H) = spectrum ℂ H := by
  have hTH : (T H).IsHermitian := hT.map_isHermitian hH
  have hRealShift (r : ℝ) :
      (r : ℂ) ∈ spectrum ℂ (T H) ↔ (r : ℂ) ∈ spectrum ℂ H := by
    have hShift :
        (H - (r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).IsHermitian :=
      hH.sub (Matrix.isHermitian_one.smul (by simp [isSelfAdjoint_iff]))
    rw [Matrix.mem_spectrum_iff_rank_sub_smul_one_lt_card,
      Matrix.mem_spectrum_iff_rank_sub_smul_one_lt_card]
    have hMap :
        T (H - (r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) =
          T H - (r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      rw [map_sub, map_smul, hOne]
    rw [← hMap, hRank _ hShift]
  ext z
  constructor
  · intro hz
    obtain ⟨r, rfl⟩ := exists_real_eq_of_mem_spectrum_of_isHermitian hTH hz
    exact (hRealShift r).mp hz
  · intro hz
    obtain ⟨r, rfl⟩ := exists_real_eq_of_mem_spectrum_of_isHermitian hH hz
    exact (hRealShift r).mpr hz

/-- **Wolf Proposition 3.6, implication (2) to (3).**

Let `T` be a positive complex-linear map on `M_d(ℂ)` that preserves the
rank of every Hermitian matrix. Then there is an invertible matrix `Y` such
that `T` is either `X ↦ Y X Y†` or `X ↦ Y Xᵀ Y†`.

The proof normalizes by `T(1)^{-1/2}`, applies Wolf's Corollary 1.1 to the
resulting unital spectrum preserver, and then undoes the normalization. The
correct final factor is `Y = (T 1)^{1/2} U`; the factor printed in the final
line of the local source does not undo the displayed normalization. -/
theorem IsPositiveMap.exists_isUnit_det_conj_or_transpose_of_preserves_hermitian_rank
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hT : IsPositiveMap T)
    (hRank : ∀ H : Matrix (Fin d) (Fin d) ℂ,
      H.IsHermitian → (T H).rank = H.rank) :
    ∃ Y : Matrix (Fin d) (Fin d) ℂ, IsUnit Y.det ∧
      ((∀ X, T X = Y * X * Yᴴ) ∨
        ∀ X, T X = Y * Xᵀ * Yᴴ) := by
  set A : Matrix (Fin d) (Fin d) ℂ := T 1 with hA
  have hApsd : A.PosSemidef := by
    rw [hA]
    exact hT 1 Matrix.PosSemidef.one
  have hArank : A.rank = d := by
    rw [hA, hRank 1 Matrix.isHermitian_one]
    simp only [Matrix.rank_one, Fintype.card_fin]
  have hAunit : IsUnit A := (Matrix.isUnit_iff_rank_eq_card A).2 hArank
  have hApd : A.PosDef := hApsd.posDef_iff_isUnit.2 hAunit
  set S : Matrix (Fin d) (Fin d) ℂ := CFC.sqrt A with hS
  set R : Matrix (Fin d) (Fin d) ℂ := S⁻¹ with hR
  have hSHerm : Sᴴ = S := by
    rw [hS]
    exact Matrix.conjTranspose_cfc_sqrt A
  have hSdet : IsUnit S.det := by
    rw [hS]
    exact hApd.isUnit_det_cfc_sqrt
  have hRdet : IsUnit R.det := by
    rw [hR]
    exact S.isUnit_nonsing_inv_det hSdet
  have hRHerm : Rᴴ = R := by
    rw [hR, Matrix.conjTranspose_nonsing_inv, hSHerm]
  have hSR : S * R = 1 := by
    rw [hR]
    exact S.mul_nonsing_inv hSdet
  have hRS : R * S = 1 := by
    rw [hR]
    exact S.nonsing_inv_mul hSdet
  let T₀ := (unitaryConjLM R).comp T
  have hT₀_apply (X : Matrix (Fin d) (Fin d) ℂ) :
      T₀ X = R * T X * R := by
    simp only [T₀, LinearMap.comp_apply, unitaryConjLM_apply, hRHerm]
  have hT₀pos : IsPositiveMap T₀ := by
    intro X hX
    rw [hT₀_apply]
    simpa only [unitaryConjLM_apply, hRHerm] using
      (unitaryConjLM_isPositiveMap R (T X) (hT X hX))
  have hT₀one : T₀ 1 = 1 := by
    rw [hT₀_apply, ← hA]
    have hnorm :=
      Matrix.conjTranspose_inv_sqrt_mul_self_mul_inv_sqrt_eq_one_of_posDef A hApd
    rw [← hS, ← hR, hRHerm] at hnorm
    exact hnorm
  have hT₀Rank : ∀ H : Matrix (Fin d) (Fin d) ℂ,
      H.IsHermitian → (T₀ H).rank = H.rank := by
    intro H hH
    rw [hT₀_apply,
      Matrix.rank_mul_eq_left_of_isUnit_det R (R * T H) hRdet,
      Matrix.rank_mul_eq_right_of_isUnit_det R (T H) hRdet,
      hRank H hH]
  have hT₀Spectrum : ∀ H : Matrix (Fin d) (Fin d) ℂ,
      H.IsHermitian → spectrum ℂ (T₀ H) = spectrum ℂ H :=
    hT₀pos.preserves_hermitian_spectrum_of_unital_of_preserves_hermitian_rank
      hT₀one hT₀Rank
  have hrecover (X : Matrix (Fin d) (Fin d) ℂ) : T X = S * T₀ X * S := by
    calc
      T X = 1 * T X * 1 := by simp only [one_mul, mul_one]
      _ = (S * R) * T X * (R * S) := by rw [hSR, hRS]
      _ = S * (R * T X * R) * S := by
        simp only [Matrix.mul_assoc]
      _ = S * T₀ X * S := by rw [hT₀_apply]
  obtain ⟨U, hUconj | hUtranspose⟩ :=
    Projectivization.exists_unitary_conj_or_transpose_of_preserves_hermitian_spectrum
      T₀ hT₀pos.map_conjTranspose hT₀Spectrum
  · refine ⟨S * (U : Matrix (Fin d) (Fin d) ℂ), ?_, Or.inl ?_⟩
    · rw [Matrix.det_mul]
      exact hSdet.mul (Matrix.UnitaryGroup.det_isUnit U)
    · intro X
      rw [hrecover X, hUconj]
      simp only [Matrix.conjTranspose_mul, hSHerm, Matrix.mul_assoc]
  · refine ⟨S * (U : Matrix (Fin d) (Fin d) ℂ), ?_, Or.inr ?_⟩
    · rw [Matrix.det_mul]
      exact hSdet.mul (Matrix.UnitaryGroup.det_isUnit U)
    · intro X
      rw [hrecover X, hUtranspose]
      simp only [Matrix.conjTranspose_mul, hSHerm, Matrix.mul_assoc]
