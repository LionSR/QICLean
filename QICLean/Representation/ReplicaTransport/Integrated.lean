/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.Proposition

/-!
# The integrated entropy gain

The entropy estimate of the area-law paper, Proposition 7.4, integrates over a closed
subinterval `[p₀, p₁] ⊆ [0, 1]` using the continuous endpoint values of `N`
(`06-transport.tex` lines 427--429 and 769--779): the entropy integrand and its error are
bounded uniformly in `p`, `N` is continuous and positive up to the endpoints, and the
fundamental theorem of calculus applies to `-log N²`.

The proof is written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy

noncomputable section

namespace TensorPower.ReplicaTransport.TransportData

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]
  {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)

/-- The entropy-gain term is interval integrable in `p` on every `[p₀, p₁] ⊆ [0, 1]`. -/
theorem intervalIntegrable_entropyGain (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) {pre : Config k (fun v => Fin (n v)) → ℂ}
    (hpre : pre ≠ 0) (p₀ p₁ : ℝ) :
    IntervalIntegrable (fun p => D.entropyGain n t k pre p) volume p₀ p₁ := by
  sorry

/-- **Integrated entropy gain** (`06-transport.tex` lines 427--429): integrating the
pointwise bound `L(p) ≤ -∂_p log N(p)²` over `[p₀, p₁] ⊆ [0, 1]`. -/
theorem integral_le_log_filteredNormSq_sub (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t)
    {k : ℕ} (hcomm : D.CrossBandCommute n t k) {pre : Config k (fun v => Fin (n v)) → ℂ}
    (hpre : pre ≠ 0) {L : ℝ → ℝ} (hL : IntervalIntegrable L volume 0 1)
    (hLle : ∀ p ∈ Ioo (0 : ℝ) 1, L p ≤ D.exactDerivative n t k pre p)
    {p₀ p₁ : ℝ} (h0 : 0 ≤ p₀) (h01 : p₀ ≤ p₁) (h1 : p₁ ≤ 1) :
    ∫ p in p₀..p₁, L p ≤
      Real.log (Transport.filteredNormSq (D.rootPath n t k p₀) pre) -
        Real.log (Transport.filteredNormSq (D.rootPath n t k p₁) pre) := by
  sorry

end TensorPower.ReplicaTransport.TransportData
