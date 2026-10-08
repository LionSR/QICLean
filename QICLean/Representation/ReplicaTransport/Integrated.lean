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

omit [∀ h, Fintype (C h)] in
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
  have hA : ∀ h, (D.oldMetric n t k h).PosDef := fun h => D.posDef_input hD ht hcomm ⟨h, none⟩
  have hA' : ∀ h c, (D.newMetric n t k h c).PosDef := fun h c =>
    D.posDef_input hD ht hcomm ⟨h, some c⟩
  obtain ⟨hint, heq⟩ := Transport.log_filteredNormSq_sub_eq_integral (T := D.histTree)
    (S := D.choiceTree) hA hA' hD.histWeight_pos hpre h0 h01 h1
  have hL' : IntervalIntegrable L volume p₀ p₁ := hL.mono_set (by
    rw [uIcc_of_le h01, uIcc_of_le zero_le_one]; exact Icc_subset_Icc h0 h1)
  exact (intervalIntegral.integral_mono_on_of_le_Ioo h01 hL' hint fun p hp =>
    hLle p ⟨h0.trans_lt hp.1, hp.2.trans_le h1⟩).trans_eq heq.symm

end TensorPower.ReplicaTransport.TransportData
