/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ContractionWordDecaySpectator
import QICLean.Probability.PoissonWord

/-!
# Excited-state decay for the concrete Poissonized word law

The finite chronological products and their actual probability law give a
dimension-free exponential bound, including arbitrary entangled spectator inputs.
The probability normalization, integrability and word recurrence are proved in
the imported modules; none is an assumed expected-decrease hypothesis.

This is an independently written finite-word form of the estimate in the area-law
manuscript, `09-amplification.tex`, lines 237–253, pinned at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Identifying this law with chronological
events of independent rate-one clocks remains a separate formal bridge. Coupled
clock locality and the full amplification proposition are not asserted here.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal Kronecker InnerProductSpace MatrixOrder ComplexOrder
  Matrix.Norms.L2Operator

namespace Matrix

variable {n ι a : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
  [Fintype a] [DecidableEq a]

/-- The squared Euclidean norm after the actual chronological root word,
with the identity on a finite spectator. -/
def poissonContractionWordEnergy (k : ι → Matrix n n ℂ)
    (ξ : EuclideanSpace ℂ (n × a)) (w : PoissonWord.Word ι) : ℝ :=
  ‖toEuclideanLin ((contractionWord k w.1 w.2) ⊗ₖ (1 : Matrix a a ℂ)) ξ‖ ^ 2

/-- The actual word observable is integrable and decays exponentially on the
excited sector. No upper bound on the gap or nonempty-label premise is imposed. -/
theorem poissonContractionWordEnergy_integrable_and_le (k : ι → Matrix n n ℂ)
    (hk : ∀ i, k i ≤ 1) {Ω : EuclideanSpace ℂ n} {ξ : EuclideanSpace ℂ (n × a)}
    {g : ℝ} (hΩ : ∀ i, toEuclideanLin (k i) Ω = 0)
    (hgap : (g : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ ∑ i, k i)
    (hξ : ∀ r : a, ⟪Ω, WithLp.toLp 2 (fun i => ξ (i, r))⟫_ℂ = 0) (t : ℝ≥0) :
    Integrable (poissonContractionWordEnergy k ξ) (PoissonWord.measure ι t) ∧
      (∫ w, poissonContractionWordEnergy k ξ w ∂PoissonWord.measure ι t) ≤
        Real.exp (-g * (t : ℝ)) * ‖ξ‖ ^ 2 := by
  by_cases hg : g ≤ Fintype.card ι
  · have hbound := PoissonWord.integrable_and_integral_le_of_sum_le_pow
      (ι := ι) t (poissonContractionWordEnergy k ξ)
      (fun _ => sq_nonneg _) (sub_nonneg.mpr hg) (sq_nonneg ‖ξ‖)
      (fun m => contractionWordSpectatorSum_le_pow k hk hΩ hgap hg hξ m)
    refine ⟨hbound.1, ?_⟩
    convert hbound.2 using 1
    congr 2
    ring
  · have hzero : ξ = 0 := spectator_eq_zero_of_card_lt_gap k hk hgap hξ (lt_of_not_ge hg)
    have hf : poissonContractionWordEnergy k ξ = (0 : PoissonWord.Word ι → ℝ) := by
      ext w
      simp [hzero, poissonContractionWordEnergy]
    rw [hf]
    exact ⟨integrable_zero _ _ _, by simp [hzero]⟩

/-- Source excited-state estimate for the literal complementary ground projection
and any joint input, under the constructed Poissonized word probability measure. -/
theorem poissonContractionWord_excitedProjection_decay (k : ι → Matrix n n ℂ)
    (hk : ∀ i, k i ≤ 1) {Ω : EuclideanSpace ℂ n} {g : ℝ} (hnorm : ‖Ω‖ = 1)
    (hΩ : ∀ i, toEuclideanLin (k i) Ω = 0)
    (hgap : (g : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ ∑ i, k i)
    (ζ : EuclideanSpace ℂ (n × a)) (t : ℝ≥0) :
    let ξ := toEuclideanLin ((1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ⊗ₖ
      (1 : Matrix a a ℂ)) ζ
    Integrable (poissonContractionWordEnergy k ξ) (PoissonWord.measure ι t) ∧
      (∫ w, poissonContractionWordEnergy k ξ w ∂PoissonWord.measure ι t) ≤
        Real.exp (-g * (t : ℝ)) * ‖ξ‖ ^ 2 := by
  exact poissonContractionWordEnergy_integrable_and_le k hk hΩ hgap
    (inner_spectatorSlice_excitedProjection_eq_zero hnorm ζ) t

end Matrix
