/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProbabilityEntropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Entropy from concentration on a finite set

Jensen's inequality bounds the entropy contribution of a finite set by its mass
and cardinality. Applying this estimate to a set and its complement gives the
binary-entropy decomposition bound. If the mass outside the set is at most `ε`,
the entropy is at most the logarithm of its cardinality, plus `ε` times the
logarithm of the ambient cardinality, plus `log 2`.

These elementary estimates provide an alternative to the continuity step in
the entropy-based approximation obstruction of Schuch–Wolf–Verstraete–Cirac,
arXiv:0705.0292v2, lines 278–305. That passage uses Audenaert's inequality.
The estimates here do not assume that the weights are strictly positive.
Empty parts are included, with the convention `Real.log 0 = 0`.
-/

open scoped BigOperators

namespace Entropy

/-- The entropy contribution of a finite set is bounded by its mass and cardinality.
This is Jensen's inequality for the concave function `Real.negMulLog`. -/
theorem sum_negMulLog_le_mass_log_card {Z : Type*} (s : Finset Z) (p : Z → ℝ)
    (hp : ∀ z ∈ s, 0 ≤ p z) :
    ∑ z ∈ s, Real.negMulLog (p z) ≤
      (∑ z ∈ s, p z) * Real.log s.card + Real.negMulLog (∑ z ∈ s, p z) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hk : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hj := Real.concaveOn_negMulLog.le_map_sum
    (t := s) (w := fun _ : Z ↦ (s.card : ℝ)⁻¹) (p := p)
    (fun _ _ ↦ by positivity)
    (by simp [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hk.ne']) hp
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  have hm := mul_le_mul_of_nonneg_left hj hk.le
  rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul] at hm
  calc
    _ ≤ (s.card : ℝ) * Real.negMulLog ((s.card : ℝ)⁻¹ * ∑ z ∈ s, p z) := hm
    _ = _ := by
      rw [Real.negMulLog_mul, Real.negMulLog, Real.log_inv]
      field_simp [hk.ne']

/-- Splitting a probability distribution into a set and its complement bounds its
entropy by the binary entropy of their masses and their conditional cardinalities. -/
theorem probabilityEntropy_le_binary_partition {Z : Type*} [Fintype Z]
    [DecidableEq Z] (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1)
    (s : Finset Z) :
    probabilityEntropy p ≤
      (1 - ∑ z ∈ sᶜ, p z) * Real.log s.card +
      (∑ z ∈ sᶜ, p z) * Real.log sᶜ.card + Real.binEntropy (∑ z ∈ sᶜ, p z) := by
  have hsplit : (∑ z ∈ s, p z) + (∑ z ∈ sᶜ, p z) = 1 :=
    (s.sum_add_sum_compl p).trans hsum
  have hins : ∑ z ∈ s, p z = 1 - ∑ z ∈ sᶜ, p z := by linarith
  have hleft := sum_negMulLog_le_mass_log_card s p (fun z _ ↦ hp z)
  have hright := sum_negMulLog_le_mass_log_card sᶜ p (fun z _ ↦ hp z)
  rw [hins] at hleft
  rw [probabilityEntropy, ← s.sum_add_sum_compl,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  linarith

/-- Concentration on a finite set bounds entropy by its logarithmic cardinality,
the omitted mass times the ambient logarithmic cardinality, and `log 2`.
This spectral-mass estimate provides an alternative to the continuity step in
Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2, lines 278–305. -/
theorem probabilityEntropy_le_log_card_add_tail {Z : Type*} [Fintype Z]
    [DecidableEq Z] (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1)
    (s : Finset Z) {ε : ℝ} (hε : ∑ z ∈ sᶜ, p z ≤ ε) :
    probabilityEntropy p ≤ Real.log s.card +
      ε * Real.log (Fintype.card Z) + Real.log 2 := by
  have ht : 0 ≤ ∑ z ∈ sᶜ, p z := Finset.sum_nonneg fun z _ ↦ hp z
  have hlogc : Real.log sᶜ.card ≤ Real.log (Fintype.card Z) := by
    rcases Nat.eq_zero_or_pos sᶜ.card with hz | hz
    · simp only [hz, Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg _
    · apply Real.log_le_log (by exact_mod_cast hz)
      exact_mod_cast Finset.card_le_univ sᶜ
  have hbound := probabilityEntropy_le_binary_partition p hp hsum s
  have hfirst := mul_nonneg ht (Real.log_natCast_nonneg s.card)
  have hsecond := mul_le_mul_of_nonneg_left hlogc ht
  have hthird := mul_le_mul_of_nonneg_right hε (Real.log_natCast_nonneg (Fintype.card Z))
  have hbinary := Real.binEntropy_le_log_two (p := ∑ z ∈ sᶜ, p z)
  nlinarith only [hbound, hfirst, hsecond, hthird, hbinary]

end Entropy
