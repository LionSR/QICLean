/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Instances.Matrix

/-!
# Continuous frames for the ranges of idempotents

The trace of a complex idempotent equals its rank, whether or not the idempotent is Hermitian.
Since integer-valued continuous functions are locally constant, a continuous family of
idempotents has locally constant rank.

A complex matrix `G` of rank `r` admits a fixed matrix `F` with `r` columns such that `G F` is
injective. For a continuous family `G(t)` of constant rank `r`, a section that is injective at
`t₀` stays injective on an open neighbourhood of `t₀`, where `G(t) F` parametrizes the full
range of `G(t)`.

For an injective complex matrix `C`, the Hermitian Gram matrix `C†C` is positive definite, so
`H = (C†C)⁻¹C†` satisfies `HC = I`; the formula does not require `C` to be isometric and applies
also to a zero-dimensional domain. Multiplying a fixed local section by a continuous family of
constant rank therefore gives a continuous frame `C` with the continuous left inverse `H`. In
particular this applies to non-Hermitian idempotents, whose ranks are locally constant.

Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993.

Moved from TNLean, `TNLean/Algebra/IdempotentRankContinuity.lean`,
`TNLean/Algebra/MatrixFixedSection.lean`, `TNLean/Algebra/MatrixGramLeftInverse.lean` and
`TNLean/Algebra/ContinuousIdempotentFrames.lean` at commit `49b78ed821` (Apache-2.0). Changes:
the four files are merged.

## Main results

* `Matrix.trace_eq_rank_of_idempotent`, `Matrix.exists_open_constantRank_of_idempotent`: the
  rank of a continuous family of idempotents is locally constant.
* `Matrix.exists_fixedSection_of_rank`, `Matrix.exists_open_fixedSection_range`: fixed sections
  of constant-rank families.
* `Matrix.gramLeftInverse_mul`, `Matrix.continuous_gramLeftInverse`: the Gram left inverse.
* `Matrix.exists_open_continuous_rangeFrame_of_constantRank`,
  `Matrix.exists_local_continuous_rangeFrame_of_idempotent`: continuous local frames and left
  inverses for constant-rank families and for idempotents.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

/-- The trace of a complex idempotent is its rank. Hermiticity is unnecessary. -/
theorem trace_eq_rank_of_idempotent {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsIdempotentElem P) :
    P.trace = (P.rank : ℂ) := by
  have hLin : IsIdempotentElem P.toLin' := by
    change P.toLin'.comp P.toLin' = P.toLin'
    rw [← Matrix.toLin'_mul, hP.eq]
  have hTrace := (LinearMap.IsIdempotentElem.isProj_range _ hLin).trace
  rw [Matrix.trace_toLin'_eq] at hTrace
  rw [Matrix.toLin'_apply'] at hTrace
  simpa only [Matrix.rank] using hTrace

/-- A continuous family of complex idempotents has locally constant rank. -/
theorem exists_open_constantRank_of_idempotent
    {T : Type*} [TopologicalSpace T] {n : ℕ}
    (P : T → Matrix (Fin n) (Fin n) ℂ) (hP : Continuous P)
    (hIdem : ∀ t, IsIdempotentElem (P t)) (t₀ : T) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧ ∀ t ∈ S, (P t).rank = (P t₀).rank := by
  have hRank : Continuous fun t => ((P t).rank : ℤ) := by
    apply Complex.isClosedEmbedding_intCast.isEmbedding.continuous_iff.mpr
    simpa only [Function.comp_def, Int.cast_natCast,
      ← trace_eq_rank_of_idempotent _ (hIdem _)] using hP.matrix_trace
  refine ⟨{t | ((P t).rank : ℤ) = ((P t₀).rank : ℤ)},
    (isOpen_discrete {((P t₀).rank : ℤ)}).preimage hRank, rfl, ?_⟩
  intro t ht
  exact_mod_cast ht


/-! ### Fixed sections of constant-rank families -/

/-- A rank-r matrix admits a fixed section on which it is injective. -/
theorem exists_fixedSection_of_rank {d r : ℕ}
    (G : Matrix (Fin d) (Fin d) ℂ) (hRank : G.rank = r) :
    ∃ F : Matrix (Fin d) (Fin r) ℂ, Function.Injective (G * F).mulVec := by
  classical
  let f := G.mulVecLin
  let e : (Fin r → ℂ) ≃ₗ[ℂ] LinearMap.range f :=
    (Module.finBasisOfFinrankEq ℂ (LinearMap.range f) hRank).equivFun.symm
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let F := LinearMap.toMatrix' (g.comp e.toLinearMap)
  have hFormula : ∀ x, (G * F) *ᵥ x = (e x : Fin d → ℂ) := by
    intro x
    rw [← mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    exact congrArg Subtype.val (LinearMap.congr_fun hg (e x))
  refine ⟨F, ?_⟩
  intro x y hxy
  rw [hFormula, hFormula] at hxy
  exact e.injective (Subtype.val_injective hxy)

/-- A fixed section of a constant-rank matrix range remains an injective
surjective parametrization of that range on an open neighborhood. -/
theorem exists_open_fixedSection_range
    {T : Type*} [TopologicalSpace T] {d r : ℕ}
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : Continuous G)
    (hRank : ∀ t, (G t).rank = r) (t₀ : T)
    (F : Matrix (Fin d) (Fin r) ℂ)
    (hBase : Function.Injective (G t₀ * F).mulVec) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧ ∀ t ∈ S,
      Function.Injective (G t * F).mulVec ∧
      LinearMap.range (G t * F).mulVecLin = LinearMap.range (G t).mulVecLin := by
  have hC : Continuous fun t => G t * F := hG.matrix_mul continuous_const
  have hGram : Continuous fun t => (G t * F)ᴴ * (G t * F) :=
    hC.matrix_conjTranspose.matrix_mul hC
  let S := {t | IsUnit ((G t * F)ᴴ * (G t * F))}
  refine ⟨S, Units.isOpen.preimage hGram, ?_, ?_⟩
  · exact (Matrix.PosDef.conjTranspose_mul_self _ hBase).isUnit
  · intro t ht
    have hInj : Function.Injective (G t * F).mulVec := by
      intro x y hxy
      apply (mulVec_injective_iff_isUnit.mpr ht)
      simpa only [mulVec_mulVec] using congrArg ((G t * F)ᴴ *ᵥ ·) hxy
    refine ⟨hInj, ?_⟩
    apply Submodule.eq_of_le_of_finrank_eq
    · simpa only [mulVecLin_mul] using
        LinearMap.range_comp_le_range F.mulVecLin (G t).mulVecLin
    · change (G t * F).rank = (G t).rank
      rw [hRank]
      change Module.finrank ℂ (LinearMap.range (G t * F).mulVecLin) = r
      rw [LinearMap.finrank_range_of_inj hInj]
      simp


/-! ### Gram left inverses -/

/-- The Gram left inverse of an injective rectangular complex matrix is a left inverse. -/
theorem gramLeftInverse_mul {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (C : Matrix m n ℂ) (hInj : Function.Injective C.mulVec) :
    ((Cᴴ * C)⁻¹ * Cᴴ) * C = 1 := by
  rw [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.PosDef.conjTranspose_mul_self _ hInj).isUnit)

/-- The Gram left inverse of a continuous injective matrix family is continuous. -/
theorem continuous_gramLeftInverse
    {T : Type*} [TopologicalSpace T] {m n : ℕ}
    (C : T → Matrix (Fin m) (Fin n) ℂ) (hC : Continuous C)
    (hInj : ∀ t, Function.Injective (C t).mulVec) :
    Continuous fun t => ((C t)ᴴ * C t)⁻¹ * (C t)ᴴ := by
  have hGram : Continuous fun t => (C t)ᴴ * C t :=
    hC.matrix_conjTranspose.matrix_mul hC
  have hInv : Continuous fun t => ((C t)ᴴ * C t)⁻¹ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    obtain ⟨u, hu⟩ := (Matrix.PosDef.conjTranspose_mul_self _ (hInj t)).isUnit
    have hAt : ContinuousAt Ring.inverse ((C t)ᴴ * C t) :=
      hu ▸ NormedRing.inverse_continuousAt u
    simpa only [Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using
      hAt.comp' (f := fun s : T => (C s)ᴴ * C s) hGram.continuousAt
  exact hInv.matrix_mul hC.matrix_conjTranspose


/-! ### Continuous frames -/

/-- A continuous constant-rank matrix family admits a continuous local frame
and a continuous left inverse, both explicitly obtained from a fixed section. -/
theorem exists_open_continuous_rangeFrame_of_constantRank
    {T : Type*} [TopologicalSpace T] {n D : ℕ}
    (P : T → Matrix (Fin n) (Fin n) ℂ) (hP : Continuous P)
    (hRank : ∀ t, (P t).rank = D) (t₀ : T) :
    ∃ (F : Matrix (Fin n) (Fin D) ℂ) (S : Set T), IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => P t * F) S ∧
      ContinuousOn (fun t => ((P t * F)ᴴ * (P t * F))⁻¹ * (P t * F)ᴴ) S ∧
      ∀ t ∈ S, Function.Injective (P t * F).mulVec ∧
        LinearMap.range (P t * F).mulVecLin = LinearMap.range (P t).mulVecLin ∧
        (((P t * F)ᴴ * (P t * F))⁻¹ * (P t * F)ᴴ) * (P t * F) = 1 := by
  obtain ⟨F, hF⟩ := exists_fixedSection_of_rank (P t₀) (hRank t₀)
  obtain ⟨S, hS, ht₀, hSection⟩ :=
    exists_open_fixedSection_range P hP hRank t₀ F hF
  have hH : ContinuousOn
      (fun t => ((P t * F)ᴴ * (P t * F))⁻¹ * (P t * F)ᴴ) S := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_gramLeftInverse (fun t : S => P t * F)
      ((hP.comp continuous_subtype_val).matrix_mul continuous_const)
      (fun t => (hSection t t.property).1)
  exact ⟨F, S, hS, ht₀, (hP.matrix_mul continuous_const).continuousOn,
    hH, fun t ht => ⟨(hSection t ht).1, (hSection t ht).2,
      gramLeftInverse_mul _ (hSection t ht).1⟩⟩

/-- The ranges of continuous complex idempotents admit continuous local frames
and continuous Gram left inverses. Neither Hermiticity nor positive rank is required. -/
theorem exists_local_continuous_rangeFrame_of_idempotent
    {T : Type*} [TopologicalSpace T] {n D : ℕ}
    (P : T → Matrix (Fin n) (Fin n) ℂ) (hP : Continuous P)
    (hIdem : ∀ t, IsIdempotentElem (P t)) (t₀ : T) (hRank : (P t₀).rank = D) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ∃ (F : Matrix (Fin n) (Fin D) ℂ)
        (C : S → Matrix (Fin n) (Fin D) ℂ)
        (H : S → Matrix (Fin D) (Fin n) ℂ),
        Continuous C ∧ Continuous H ∧ ∀ t,
          C t = P t * F ∧ H t = ((C t)ᴴ * C t)⁻¹ * (C t)ᴴ ∧
          Function.Injective (C t).mulVec ∧
          LinearMap.range (C t).mulVecLin = LinearMap.range (P t).mulVecLin ∧
          H t * C t = 1 ∧ P t * C t = C t := by
  obtain ⟨s, hsopen, ht₀, hsRank⟩ :=
    exists_open_constantRank_of_idempotent P hP hIdem t₀
  obtain ⟨F, q, hqopen, hp₀, hC, hH, hdata⟩ :=
    exists_open_continuous_rangeFrame_of_constantRank
      (fun t : s => P t) (hP.comp continuous_subtype_val)
      (fun t => (hsRank t t.property).trans hRank) (⟨t₀, ht₀⟩ : s)
  let w : Set T := Subtype.val '' q
  have hSub : w ⊆ s := by
    rintro t ⟨p, _, rfl⟩
    exact p.property
  let j₀ : w → s := fun t => ⟨t.val, hSub t.property⟩
  have hjq : ∀ t, j₀ t ∈ q := by
    rintro ⟨t, ⟨p, hp, rfl⟩⟩
    exact hp
  let j : w → q := fun t => ⟨j₀ t, hjq t⟩
  have hInj : ∀ t : w, Function.Injective (P t * F).mulVec :=
    fun t => (hdata (j t).val (j t).property).1
  have hCcont : Continuous (fun t : w => P t * F) :=
    (hP.comp continuous_subtype_val).matrix_mul continuous_const
  refine ⟨w, hsopen.isOpenMap_subtype_val q hqopen,
    ⟨(⟨t₀, ht₀⟩ : s), hp₀, rfl⟩, F,
    (fun t : w => P t * F),
    (fun t : w => ((P t * F)ᴴ * (P t * F))⁻¹ * (P t * F)ᴴ),
    hCcont, continuous_gramLeftInverse _ hCcont hInj, ?_⟩
  refine fun t => ⟨rfl, rfl, hInj t,
    (hdata (j t).val (j t).property).2.1,
    gramLeftInverse_mul _ (hInj t), ?_⟩
  exact (Matrix.mul_assoc _ _ _).symm.trans (congrArg (· * F) (hIdem t).eq)

end Matrix
