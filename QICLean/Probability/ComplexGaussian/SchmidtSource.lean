/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex (GPT-6).
These are original integration proofs using the existing QICLean Schmidt theorem
and Mathlib; no upstream OpenAI Lean proof text is reused in this file.
The imported Gaussian foundation retains its source and modification notices.
-/
import QICLean.Channel.SchmidtDecomposition
import QICLean.Probability.ComplexGaussian.ProductSourceTransport

/-!
# Actual Schmidt frames for Gaussian source replacement

The genuine Schmidt theorem supplies two rectangular isometries and nonnegative
weights for each finite bipartite Euclidean vector. Reindexing its bases gives
arbitrary finite ambient endpoint types. The weight mass is the actual squared
vector norm; unit vectors therefore give probability lists.

This is the source representation used in *Polynomial PEPS approximation of
gapped square-grid ground states*, September 24, 2026,
`04-compression.tex:279–309`, `eq:compression-random-source`.
-/

open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix.Norms.Elementwise

namespace QICLean.ComplexGaussian

noncomputable section

local instance {m n : Type*} [Fintype m] [Fintype n] : ContinuousENorm (Matrix m n ℂ) :=
  SeminormedAddGroup.toContinuousENorm

private theorem column_isometry_of_orthonormal {L I : Type*} [Fintype L] [DecidableEq I]
    (v : I → EuclideanSpace ℂ L) (hv : Orthonormal ℂ v) :
    (Matrix.of (fun l i ↦ v i l)).conjTranspose * Matrix.of (fun l i ↦ v i l) = 1 := by
  classical
  calc
    _ = Matrix.gram ℂ v := by
      simpa only [EuclideanSpace.basisFun_repr] using
        (Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun L ℂ) v).symm
    _ = 1 := Matrix.gram_eq_one_iff_orthonormal.mpr hv

/-- Actual Schmidt frames for an arbitrary finite bipartite Euclidean vector.
The weights have their actual norm-squared mass, including the zero vector.
Source: `eq:compression-random-source`, `04-compression.tex:281–289`;
Schmidt existence is supplied by Wolf Proposition 1.1 through
`Matrix.exists_isSchmidtDecomposition`. -/
theorem exists_schmidtSourceFrames {L R : Type*} [Fintype L] [Fintype R]
    (ψ : EuclideanSpace ℂ (L × R)) :
    ∃ (lam : Fin (min (Fintype.card L) (Fintype.card R)) → ℝ)
      (E : Matrix L (Fin (min (Fintype.card L) (Fintype.card R))) ℂ)
      (F : Matrix R (Fin (min (Fintype.card L) (Fintype.card R))) ℂ),
      (∀ a, 0 ≤ lam a) ∧ E.conjTranspose * E = 1 ∧ F.conjTranspose * F = 1 ∧
        ambientSchmidtVector lam E F = ψ.ofLp ∧ ∑ a, lam a = ‖ψ‖ ^ 2 := by
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
      Equiv.piCongrLeft'_apply, Equiv.symm_symm, ambientSchmidtVector] using h.symm
  · rw [hmass, EuclideanSpace.norm_sq_eq]
    exact Fintype.sum_equiv (eL.symm.prodCongr eR.symm) _ _ (fun p ↦ rfl)

/-- Unit-norm source vectors give actual normalized Schmidt probability lists.
Source: `eq:compression-random-source`, `04-compression.tex:281–290`. -/
theorem exists_probability_schmidtSourceFrames {L R : Type*} [Fintype L] [Fintype R]
    (ψ : EuclideanSpace ℂ (L × R)) (hψ : ‖ψ‖ = 1) :
    ∃ (lam : Fin (min (Fintype.card L) (Fintype.card R)) → ℝ)
      (E : Matrix L (Fin (min (Fintype.card L) (Fintype.card R))) ℂ)
      (F : Matrix R (Fin (min (Fintype.card L) (Fintype.card R))) ℂ),
      (∀ a, 0 ≤ lam a) ∧ ∑ a, lam a = 1 ∧ E.conjTranspose * E = 1 ∧
        F.conjTranspose * F = 1 ∧ ambientSchmidtVector lam E F = ψ.ofLp := by
  obtain ⟨lam, E, F, hnonneg, hE, hF, hrepr, hmass⟩ := exists_schmidtSourceFrames ψ
  exact ⟨lam, E, F, hnonneg, by simpa [hψ] using hmass, hE, hF, hrepr⟩

/-- The Gaussian source replacement of two actual bipartite vectors, with its
Schmidt weights and local isometries obtained from the genuine Schmidt theorem.
The ket and bra endpoint dimensions may differ. Source:
`eq:compression-random-source`, `04-compression.tex:279–309`. -/
theorem exists_schmidtSourceReplacement {L R Lt Rt : Type*}
    [Fintype L] [Fintype R] [Fintype Lt] [Fintype Rt]
    (ψ : EuclideanSpace ℂ (L × R)) (φ : EuclideanSpace ℂ (Lt × Rt))
    (k : ℕ) (hk : 0 < k) :
    ∃ (lam : Fin (min (Fintype.card L) (Fintype.card R)) → ℝ)
      (mu : Fin (min (Fintype.card Lt) (Fintype.card Rt)) → ℝ)
      (E : Matrix L (Fin (min (Fintype.card L) (Fintype.card R))) ℂ)
      (F : Matrix R (Fin (min (Fintype.card L) (Fintype.card R))) ℂ)
      (Et : Matrix Lt (Fin (min (Fintype.card Lt) (Fintype.card Rt))) ℂ)
      (Ft : Matrix Rt (Fin (min (Fintype.card Lt) (Fintype.card Rt))) ℂ),
      (∀ a, 0 ≤ lam a) ∧ (∀ c, 0 ≤ mu c) ∧
        ∑ a, lam a = ‖ψ‖ ^ 2 ∧ ∑ c, mu c = ‖φ‖ ^ 2 ∧
        E.conjTranspose * E = 1 ∧ F.conjTranspose * F = 1 ∧
        Et.conjTranspose * Et = 1 ∧ Ft.conjTranspose * Ft = 1 ∧
        ambientSchmidtSource lam mu E F Et Ft =
          Matrix.vecMulVec ψ.ofLp (fun q ↦ conj (φ.ofLp q)) ∧
        Integrable (ambientSampledSource k lam mu E F Et Ft)
          (law (Fin k × (Fin (min (Fintype.card L) (Fintype.card R)) ×
            Fin (min (Fintype.card Lt) (Fintype.card Rt))))) ∧
        (∫ x, ambientSampledSource k lam mu E F Et Ft x
          ∂law (Fin k × (Fin (min (Fintype.card L) (Fintype.card R)) ×
            Fin (min (Fintype.card Lt) (Fintype.card Rt))))) =
          Matrix.vecMulVec ψ.ofLp (fun q ↦ conj (φ.ofLp q)) := by
  obtain ⟨lam, E, F, hlam, hE, hF, hψ, hmass⟩ := exists_schmidtSourceFrames ψ
  obtain ⟨mu, Et, Ft, hmu, hEt, hFt, hφ, hmass'⟩ := exists_schmidtSourceFrames φ
  have hsource : ambientSchmidtSource lam mu E F Et Ft =
      Matrix.vecMulVec ψ.ofLp (fun q ↦ conj (φ.ofLp q)) := by
    rw [ambientSchmidtSource, hψ, hφ]
  refine ⟨lam, mu, E, F, Et, Ft, hlam, hmu, hmass, hmass', hE, hF, hEt, hFt,
    hsource, integrable_ambientSampledSource k hk lam mu hlam hmu E F Et Ft, ?_⟩
  rw [integral_ambientSampledSource k hk lam mu hlam hmu E F Et Ft, hsource]

end

end QICLean.ComplexGaussian
