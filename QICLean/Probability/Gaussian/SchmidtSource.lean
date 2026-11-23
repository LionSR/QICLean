/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex (GPT-6).
These are original integration proofs using the existing QICLean Schmidt theorem
and Mathlib; no upstream OpenAI Lean proof text is reused in this file.
The imported Gaussian foundation retains its source and modification notices.
-/
import QICLean.Channel.Schmidt.SchmidtFrames
import QICLean.Probability.Gaussian.ProductSourceTransport

/-!
# Gaussian source replacement of two Schmidt-decomposed vectors

The Schmidt frames of `Matrix.exists_schmidtFrames` (two rectangular isometries and
nonnegative weights of mass `‖ψ‖²` for each finite bipartite Euclidean vector) give the
Gaussian source replacement of the outer product of two such vectors, with its integrability
and its expectation.

This is the source representation used in *Polynomial PEPS approximation of
gapped square-grid ground states*, September 24, 2026,
`04-compression.tex:279–309`, `eq:compression-random-source`.
-/

open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix.Norms.Elementwise

namespace QICLean.ComplexGaussian

open ProductSource

noncomputable section

local instance {m n : Type*} [Fintype m] [Fintype n] : ContinuousENorm (Matrix m n ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

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
        Matrix.schmidtFrameOuterProduct lam mu E F Et Ft =
          Matrix.vecMulVec ψ.ofLp (fun q ↦ conj (φ.ofLp q)) ∧
        Integrable (ambientSampledSource k lam mu E F Et Ft)
          (law (Fin k × (Fin (min (Fintype.card L) (Fintype.card R)) ×
            Fin (min (Fintype.card Lt) (Fintype.card Rt))))) ∧
        (∫ x, ambientSampledSource k lam mu E F Et Ft x
          ∂law (Fin k × (Fin (min (Fintype.card L) (Fintype.card R)) ×
            Fin (min (Fintype.card Lt) (Fintype.card Rt))))) =
          Matrix.vecMulVec ψ.ofLp (fun q ↦ conj (φ.ofLp q)) := by
  obtain ⟨lam, E, F, hlam, hE, hF, hψ, hmass⟩ := Matrix.exists_schmidtFrames ψ
  obtain ⟨mu, Et, Ft, hmu, hEt, hFt, hφ, hmass'⟩ := Matrix.exists_schmidtFrames φ
  have hsource : Matrix.schmidtFrameOuterProduct lam mu E F Et Ft =
      Matrix.vecMulVec ψ.ofLp (fun q ↦ conj (φ.ofLp q)) := by
    rw [Matrix.schmidtFrameOuterProduct, hψ, hφ]
  refine ⟨lam, mu, E, F, Et, Ft, hlam, hmu, hmass, hmass', hE, hF, hEt, hFt,
    hsource, integrable_ambientSampledSource k hk lam mu hlam hmu E F Et Ft, ?_⟩
  rw [integral_ambientSampledSource k hk lam mu hlam hmu E F Et Ft, hsource]

end

end QICLean.ComplexGaussian
