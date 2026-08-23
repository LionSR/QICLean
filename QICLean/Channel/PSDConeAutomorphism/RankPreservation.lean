/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.HermitianHelpers
import QICLean.Channel.PSDConeAutomorphism.FaceDimension
import QICLean.Channel.PSDConeAutomorphism.RankPreserver
import QICLean.Channel.Schwarz.PositiveMapProperties
import QICLean.Channel.TransferMatrix

/-!
# Rank preservation from surjectivity on the positive-semidefinite cone

This file formalizes the implication (1) to (2) in Wolf, *Quantum Channels &
Operations*, Chapter 3, Proposition 3.6. The proof follows Wolf's cone argument:
surjectivity on the positive-semidefinite cone makes the linear map invertible,
the map carries Wolf's cone `C(P)` onto `C(T(P))`, and the dimension of its span
determines `rank(P)`.

## Main declarations

* `MapsPSDConeOnto.rank_eq_of_posSemidef`: cone surjectivity preserves rank on
  positive-semidefinite matrices.
* `MapsPSDConeOnto.rank_eq_of_isHermitian`: implication (1) to (2).
* `wolf_prop_3_6`: Wolf's full three-condition equivalence.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Unitary

variable {D : ℕ}

private theorem Matrix.rank_sub_le_add_rank (A B : MatrixAlg D) :
    (A - B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank]
  calc
    Module.finrank ℂ (LinearMap.range (A - B).mulVecLin) ≤
        Module.finrank ℂ ((LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :
          Submodule ℂ (Fin D → ℂ)) := by
      apply Submodule.finrank_mono
      simpa [sub_eq_add_neg] using LinearMap.range_add_le A.mulVecLin (-B.mulVecLin)
    _ ≤ Module.finrank ℂ (LinearMap.range A.mulVecLin) +
        Module.finrank ℂ (LinearMap.range B.mulVecLin) :=
      Submodule.finrank_add_le_finrank_add_finrank _ _

private theorem Matrix.IsHermitian.rank_cfc
    {H : MatrixAlg D} (hH : H.IsHermitian) (f : ℝ → ℝ) :
    (hH.cfc f).rank = Fintype.card {i // f (hH.eigenvalues i) ≠ 0} := by
  let U := hH.eigenvectorUnitary
  have hU : IsUnit (U : MatrixAlg D).det := Matrix.UnitaryGroup.det_isUnit U
  have hUh : IsUnit (star (U : MatrixAlg D)).det := by
    simpa [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] using hU.star
  rw [Matrix.IsHermitian.cfc, conjStarAlgAut_apply]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUh]
  rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ hU]
  rw [Matrix.rank_diagonal]
  simp

private theorem Matrix.IsHermitian.posPart_eq_cfc
    {H : MatrixAlg D} (hH : H.IsHermitian) :
    H⁺ = hH.cfc (fun x ↦ x⁺) := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc, hH.cfc_eq]

private theorem Matrix.IsHermitian.negPart_eq_cfc
    {H : MatrixAlg D} (hH : H.IsHermitian) :
    H⁻ = hH.cfc (fun x ↦ x⁻) := by
  rw [CFC.negPart_def, cfcₙ_eq_cfc, hH.cfc_eq]

private theorem Matrix.IsHermitian.rank_posPart_add_rank_negPart
    {H : MatrixAlg D} (hH : H.IsHermitian) :
    H⁺.rank + H⁻.rank = H.rank := by
  rw [hH.posPart_eq_cfc, hH.negPart_eq_cfc, hH.rank_cfc, hH.rank_cfc,
    hH.rank_eq_card_non_zero_eigs]
  have hdisj : Disjoint
      (fun i : Fin D => hH.eigenvalues i < 0)
      (fun i : Fin D => 0 < hH.eigenvalues i) := by
    rw [disjoint_iff]
    ext i
    simp only [Pi.inf_apply, inf_Prop_eq, Pi.bot_apply, Prop.bot_eq_false,
      iff_false, not_and, not_lt]
    exact fun h => h.le
  have hcard := Fintype.card_subtype_or_disjoint
    (fun i : Fin D => hH.eigenvalues i < 0)
    (fun i : Fin D => 0 < hH.eigenvalues i) hdisj
  simpa only [ne_eq, posPart_eq_zero, negPart_eq_zero, not_le, ne_iff_lt_or_gt,
    gt_iff_lt, Nat.add_comm] using hcard.symm

private theorem MapsPSDConeOnto.surjective
    {T : MatrixAlg D →ₗ[ℂ] MatrixAlg D} (hT : MapsPSDConeOnto T) :
    Function.Surjective T := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← CStarAlgebra.span_nonneg (A := MatrixAlg D)]
  rw [Submodule.span_le]
  intro A hA
  obtain ⟨X, _hX, hTX⟩ := hT.2 A (Matrix.nonneg_iff_posSemidef.mp hA)
  exact ⟨X, hTX⟩

private theorem MapsPSDConeOnto.bijective
    {T : MatrixAlg D →ₗ[ℂ] MatrixAlg D} (hT : MapsPSDConeOnto T) :
    Function.Bijective T := by
  have hsurj := hT.surjective
  exact ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩

private theorem MapsPSDConeOnto.symm
    {T : MatrixAlg D →ₗ[ℂ] MatrixAlg D} (hT : MapsPSDConeOnto T) :
    MapsPSDConeOnto (LinearEquiv.ofBijective T hT.bijective).symm.toLinearMap := by
  let e := LinearEquiv.ofBijective T hT.bijective
  constructor
  · intro A hA
    obtain ⟨X, hX, hTX⟩ := hT.2 A hA
    have heq : e.symm A = X := by
      apply e.injective
      simpa [e] using hTX.symm
    simpa [e, heq] using hX
  · intro A hA
    refine ⟨T A, hT.1 A hA, ?_⟩
    exact e.symm_apply_apply A

private theorem MapsPSDConeOnto.image_psdConeFace
    {T : MatrixAlg D →ₗ[ℂ] MatrixAlg D} (hT : MapsPSDConeOnto T)
    (P : MatrixAlg D) :
    T '' Matrix.psdConeFace P = Matrix.psdConeFace (T P) := by
  let e := LinearEquiv.ofBijective T hT.bijective
  ext A
  constructor
  · rintro ⟨B, ⟨c, hc, hzero, hle⟩, rfl⟩
    refine ⟨c, hc, ?_, ?_⟩
    · simpa only [LinearMap.map_smul_of_tower, map_zero] using hT.1.map_le_map hzero
    · simpa only [LinearMap.map_smul_of_tower] using hT.1.map_le_map hle
  · rintro ⟨c, hc, hzero, hle⟩
    refine ⟨e.symm A, ?_, e.apply_symm_apply A⟩
    refine ⟨c, hc, ?_, ?_⟩
    · simpa [e, LinearMap.map_smul_of_tower] using hT.symm.1.map_le_map hzero
    · have := hT.symm.1.map_le_map hle
      simpa [e, LinearMap.map_smul_of_tower] using this

/-- A linear map that maps the positive-semidefinite cone onto itself preserves
the rank of positive-semidefinite matrices. This is Wolf's cone-dimension step
after Proposition 3.6, equation (3.42). -/
theorem MapsPSDConeOnto.rank_eq_of_posSemidef
    {T : MatrixAlg D →ₗ[ℂ] MatrixAlg D} (hT : MapsPSDConeOnto T)
    {P : MatrixAlg D} (hP : P.PosSemidef) :
    (T P).rank = P.rank := by
  let e := LinearEquiv.ofBijective T hT.bijective
  have hTP : (T P).PosSemidef := hT.1 P hP
  have hspan :
      (Submodule.span ℂ (Matrix.psdConeFace P)).map e.toLinearMap =
        Submodule.span ℂ (Matrix.psdConeFace (T P)) := by
    change (Submodule.span ℂ (Matrix.psdConeFace P)).map T =
      Submodule.span ℂ (Matrix.psdConeFace (T P))
    rw [Submodule.map_span]
    rw [hT.image_psdConeFace P]
  apply Nat.pow_left_injective (by norm_num : 2 ≠ 0)
  change (T P).rank ^ 2 = P.rank ^ 2
  rw [← Matrix.finrank_span_psdConeFace_eq_rank_sq P hP,
    ← Matrix.finrank_span_psdConeFace_eq_rank_sq (T P) hTP, ← hspan]
  exact e.finrank_map_eq _

private theorem MapsPSDConeOnto.rank_le_of_isHermitian
    {T : MatrixAlg D →ₗ[ℂ] MatrixAlg D} (hT : MapsPSDConeOnto T)
    {H : MatrixAlg D} (hH : H.IsHermitian) :
    (T H).rank ≤ H.rank := by
  have hdecomp : H = H⁺ - H⁻ :=
    (CFC.posPart_sub_negPart H (isSelfAdjoint_iff.mpr hH)).symm
  have hmapdecomp : T H = T H⁺ - T H⁻ := by
    have := congrArg T hdecomp
    rwa [map_sub] at this
  calc
    (T H).rank = (T H⁺ - T H⁻).rank := congrArg Matrix.rank hmapdecomp
    _ ≤ (T H⁺).rank + (T H⁻).rank := Matrix.rank_sub_le_add_rank _ _
    _ = H⁺.rank + H⁻.rank := by
      rw [hT.rank_eq_of_posSemidef (Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H)),
        hT.rank_eq_of_posSemidef (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H))]
    _ = H.rank := hH.rank_posPart_add_rank_negPart

/-- Wolf Proposition 3.6, implication (1) to (2): a linear map that maps the
positive-semidefinite cone onto itself preserves the rank of every Hermitian
matrix. -/
theorem MapsPSDConeOnto.rank_eq_of_isHermitian
    {T : MatrixAlg D →ₗ[ℂ] MatrixAlg D} (hT : MapsPSDConeOnto T)
    {H : MatrixAlg D} (hH : H.IsHermitian) :
    (T H).rank = H.rank := by
  apply le_antisymm (hT.rank_le_of_isHermitian hH)
  let e := LinearEquiv.ofBijective T hT.bijective
  have hTH : (T H).IsHermitian := by
    have hmapstar := hT.1.map_conjTranspose H
    rw [hH.eq] at hmapstar
    exact hmapstar.symm
  have hinv := hT.symm.rank_le_of_isHermitian hTH
  simpa [e] using hinv

/-- **Wolf Proposition 3.6, automorphisms and rank-preserving maps.**

For a complex-linear map on `M_D(ℂ)`, the following are equivalent: it maps the
positive-semidefinite cone onto itself; it is positive and preserves the rank
of Hermitian matrices; and it is an invertible congruence, possibly after
transposition. -/
theorem wolf_prop_3_6
    (T : MatrixAlg D →ₗ[ℂ] MatrixAlg D) :
    List.TFAE [
      MapsPSDConeOnto T,
      IsPositiveMap T ∧ ∀ H : MatrixAlg D, H.IsHermitian → (T H).rank = H.rank,
      ∃ Y : MatrixAlg D, IsUnit Y.det ∧
        ((∀ X, T X = Y * X * Yᴴ) ∨ ∀ X, T X = Y * Xᵀ * Yᴴ)] := by
  tfae_have h12 : 1 → 2 := by
    intro hT
    exact ⟨hT.1, fun _ hH ↦ hT.rank_eq_of_isHermitian hH⟩
  tfae_have h23 : 2 → 3 := by
    rintro ⟨hT, hRank⟩
    exact hT.exists_isUnit_det_conj_or_transpose_of_preserves_hermitian_rank hRank
  tfae_have h31 : 3 → 1 := by
    rintro ⟨Y, hY, hconj | htranspose⟩
    · have hT : T = unitaryConjLM Y := by
        apply LinearMap.ext
        intro X
        simpa only [unitaryConjLM_apply] using hconj X
      rw [hT]
      exact unitaryConjLM_mapsPSDConeOnto Y hY
    · have hT : T =
          (unitaryConjLM Y).comp (Matrix.transposeLinearMapComplex (Fin D)) := by
        apply LinearMap.ext
        intro X
        change T X = Y * Xᵀ * Yᴴ
        exact htranspose X
      rw [hT]
      exact unitaryConjLM_comp_transpose_mapsPSDConeOnto Y hY
  tfae_finish
