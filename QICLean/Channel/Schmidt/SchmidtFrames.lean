/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex (GPT-6).
These are original integration proofs using the existing QICLean Schmidt theorem
and Mathlib; no upstream OpenAI Lean proof text is reused in this file.
-/
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import QICLean.Channel.Schmidt.Decomposition
import QICLean.Analysis.TensorProduct.ProductSource

/-!
# Schmidt frames of a bipartite vector

A vector `ψ` on `L × R` with finite `L` and `R` is written as
`ψ (l, r) = ∑_a √λ_a E l a F r a` with nonnegative weights `λ_a` of total mass `‖ψ‖²` and two
rectangular isometries `E`, `F` (`Eᴴ E = 1`, `Fᴴ F = 1`) with `min (|L|, |R|)` columns:
Schmidt's theorem with its bases read as matrices on arbitrary finite types. A unit vector
gives probability weights.

## Main results

* `Matrix.exists_schmidtFrames`: Schmidt frames with weights of mass `‖ψ‖²`.
* `Matrix.exists_schmidtFrames_of_norm_eq_one`: probability weights for a unit vector.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `04-compression.tex:279–309`, `eq:compression-random-source`.
* Wolf, *Quantum Channels & Operations*, Chapter 1, Proposition 1.1 (Schmidt decomposition).
-/

open Matrix
open scoped BigOperators ComplexConjugate

namespace Matrix

noncomputable section

/-- The matrix whose columns are an orthonormal family has orthonormal columns. -/
private theorem column_isometry_of_orthonormal {L I : Type*} [Fintype L] [DecidableEq I]
    (v : I → EuclideanSpace ℂ L) (hv : Orthonormal ℂ v) :
    (Matrix.of (fun l i ↦ v i l)).conjTranspose * Matrix.of (fun l i ↦ v i l) = 1 := by
  classical
  calc
    _ = Matrix.gram ℂ v := by
      simpa only [EuclideanSpace.basisFun_repr] using
        (Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun L ℂ) v).symm
    _ = 1 := Matrix.gram_eq_one_iff_orthonormal.mpr hv

/-- Schmidt frames for an arbitrary finite bipartite Euclidean vector: nonnegative weights of
mass `‖ψ‖²`, including for the zero vector, and two matrices with orthonormal columns.
Source: `eq:compression-random-source`, `04-compression.tex:281–289`;
Schmidt existence is supplied by Wolf Proposition 1.1 through
`Matrix.exists_isSchmidtDecomposition`. -/
theorem exists_schmidtFrames {L R : Type*} [Fintype L] [Fintype R]
    (ψ : EuclideanSpace ℂ (L × R)) :
    ∃ (lam : Fin (min (Fintype.card L) (Fintype.card R)) → ℝ)
      (E : Matrix L (Fin (min (Fintype.card L) (Fintype.card R))) ℂ)
      (F : Matrix R (Fin (min (Fintype.card L) (Fintype.card R))) ℂ),
      (∀ a, 0 ≤ lam a) ∧ E.conjTranspose * E = 1 ∧ F.conjTranspose * F = 1 ∧
        schmidtFrameVector lam E F = ψ.ofLp ∧ ∑ a, lam a = ‖ψ‖ ^ 2 := by
  classical
  let eL : L ≃ Fin (Fintype.card L) := Fintype.equivFin L
  let eR : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  let ψFin : Fin (Fintype.card L) × Fin (Fintype.card R) → ℂ :=
    fun p ↦ ψ (eL.symm p.1, eR.symm p.2)
  obtain ⟨e, f, lam, hnonneg, hrepr, hmass⟩ := Matrix.exists_isSchmidtDecomposition ψFin
  let tL := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eL.symm
  let tR := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eR.symm
  let vL : Fin (min (Fintype.card L) (Fintype.card R)) → EuclideanSpace ℂ L :=
    fun a ↦ tL (e (a.castLE (min_le_left _ _)))
  let vR : Fin (min (Fintype.card L) (Fintype.card R)) → EuclideanSpace ℂ R :=
    fun a ↦ tR (f (a.castLE (min_le_right _ _)))
  let E : Matrix L (Fin (min (Fintype.card L) (Fintype.card R))) ℂ :=
    Matrix.of fun l a ↦ vL a l
  let F : Matrix R (Fin (min (Fintype.card L) (Fintype.card R))) ℂ :=
    Matrix.of fun r a ↦ vR a r
  have hvL : Orthonormal ℂ vL :=
    (e.orthonormal.comp _ (Fin.castLE_injective _)).comp_linearIsometryEquiv tL
  have hvR : Orthonormal ℂ vR :=
    (f.orthonormal.comp _ (Fin.castLE_injective _)).comp_linearIsometryEquiv tR
  refine ⟨lam, E, F, hnonneg, column_isometry_of_orthonormal vL hvL,
    column_isometry_of_orthonormal vR hvR, ?_, ?_⟩
  · funext p
    have h := hrepr (eL p.1) (eR p.2)
    simpa only [ψFin, Equiv.symm_apply_apply, E, F, Matrix.of_apply,
      vL, vR, tL, tR, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply, Equiv.symm_symm, schmidtFrameVector] using h.symm
  · rw [hmass, EuclideanSpace.norm_sq_eq]
    exact Fintype.sum_equiv (eL.symm.prodCongr eR.symm) _ _ (fun p ↦ rfl)

/-- A unit vector has Schmidt frames whose weights are probabilities.
Source: `eq:compression-random-source`, `04-compression.tex:281–290`. -/
theorem exists_schmidtFrames_of_norm_eq_one {L R : Type*} [Fintype L] [Fintype R]
    (ψ : EuclideanSpace ℂ (L × R)) (hψ : ‖ψ‖ = 1) :
    ∃ (lam : Fin (min (Fintype.card L) (Fintype.card R)) → ℝ)
      (E : Matrix L (Fin (min (Fintype.card L) (Fintype.card R))) ℂ)
      (F : Matrix R (Fin (min (Fintype.card L) (Fintype.card R))) ℂ),
      (∀ a, 0 ≤ lam a) ∧ ∑ a, lam a = 1 ∧ E.conjTranspose * E = 1 ∧
        F.conjTranspose * F = 1 ∧ schmidtFrameVector lam E F = ψ.ofLp := by
  obtain ⟨lam, E, F, hnonneg, hE, hF, hrepr, hmass⟩ := exists_schmidtFrames ψ
  exact ⟨lam, E, F, hnonneg, by simpa [hψ] using hmass, hE, hF, hrepr⟩

end

end Matrix
