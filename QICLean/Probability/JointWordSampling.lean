/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.FiniteMatrixSampling
import QICLean.Probability.UniformWordFrequency
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Joint matrix approximation and word-frequency sampling

Let `Y` be a matrix-valued function of words of length `m` over `n ≥ 1` letters,
with `‖Y w‖ ≤ R`. The mean is its actual finite uniform average over all words.
For one uniform family of `ℓ ≥ 1` sampled words, the fraction failing either
mean approximation at tolerance `η > 0` or the simultaneous letter-count
threshold `u` is at most

`N * (4 * p² * R² / (ℓ * η²))^p + n * ℓ * exp (m / n - u * log 2)`.

Here `N` is the matrix dimension and `p ≥ 1`. The proof derives the bound `2R`
after centering at the actual mean and applies the proved finite matrix moment
tail. It then unions the two actual exceptional subsets of the same finite
assignment space. A numerical sum below one gives a single sample satisfying
both conclusions. The matrices need not be Hermitian.

The sample index set is nonempty throughout, so the sample mean has positive
normalizing cardinality. The word length may be zero. These are generic joint
sampling results for the sampled-projector argument of LVV,
arXiv:1307.5143v1, Section 2.3.1, Corollary 2.14. Applying them to a normalized
Hamiltonian power requires its mean identity, norm estimate and ground-energy
dependence separately.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
open WordMultiplicity

namespace Matrix

open Classical in
/-- The actual finite matrix mean has an explicit sample-approximation failure bound.
Centering derives norm at most `2R`; the coefficient `4` records its square.
The nonempty sample index set is required for the sample mean. -/
theorem finite_uniform_average_sub_mean_tail_bound
    {α β n : Type*} [Fintype α] [Fintype β] [Fintype n] [DecidableEq n]
    [Nonempty α] [Nonempty β] [Nonempty n]
    (Y : α → Matrix n n ℂ) {R η : ℝ} (hη : 0 < η) (hY : ∀ a, ‖Y a‖ ≤ R)
    {p : ℕ} (hp : 0 < p) :
    let μ := (Fintype.card α : ℂ)⁻¹ • ∑ a, Y a
    ((Finset.univ.filter fun σ : β → α ↦
        η ≤ ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, Y (σ b) - μ‖).card : ℝ) /
        (Fintype.card (β → α) : ℝ) ≤
      (Fintype.card n : ℝ) *
        (4 * (p : ℝ) ^ 2 * R ^ 2 / ((Fintype.card β : ℝ) * η ^ 2)) ^ p := by
  classical
  intro μ
  have hR : 0 ≤ R := (norm_nonneg (Y (Classical.arbitrary α))).trans (hY _)
  have hαR : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hαC : (Fintype.card α : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hβC : (Fintype.card β : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmass : ∑ _a : α, (Fintype.card α : ℝ)⁻¹ = 1 := by simp [hαR]
  have hμ : ‖μ‖ ≤ R := by
    have hh := norm_sum_smul_le (t := Finset.univ)
      (w := fun _ : α ↦ (Fintype.card α : ℝ)⁻¹) (z := Y)
      (fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)) hmass (fun a _ ↦ hY a)
    simpa only [μ, ← Finset.smul_sum, ← Complex.ofReal_natCast,
      ← Complex.ofReal_inv, Complex.coe_smul] using hh
  have hcenter : ∑ a, (Y a - μ) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, μ, smul_smul, mul_inv_cancel₀ hαC, one_smul, sub_self]
  have hXY (_b : β) (a : α) : ‖Y a - μ‖ ≤ 2 * R :=
    (norm_sub_le _ _).trans (by linarith [hY a, hμ])
  have hexpand (σ : β → α) : (Fintype.card β : ℂ)⁻¹ • ∑ b, (Y (σ b) - μ) =
      (Fintype.card β : ℂ)⁻¹ • ∑ b, Y (σ b) - μ := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hβC, one_smul]
  have hh := finite_uniform_tail_bound_of_centered (fun (_b : β) a ↦ Y a - μ)
    (mul_nonneg (by norm_num) hR) hη hXY (fun _ ↦ hcenter) hp
  have hcoeff : (p : ℝ) ^ 2 * (2 * R) ^ 2 = 4 * (p : ℝ) ^ 2 * R ^ 2 := by ring
  simpa only [hexpand, hcoeff] using hh


open Classical in
/-- On one full uniform family of sampled words, the probability of either matrix
approximation failure or a large letter count is bounded by the sum of the two
proved bounds. The mean is the actual uniform finite sum over all words. -/
theorem finite_uniform_word_sampling_failure_bound
    {α β n : Type*} [Fintype α] [Fintype β] [Fintype n] [DecidableEq n]
    [Nonempty α] [Nonempty β] [Nonempty n]
    {m : ℕ} (Y : (Fin m → α) → Matrix n n ℂ) {R η : ℝ}
    (hη : 0 < η) (hY : ∀ w, ‖Y w‖ ≤ R) {p : ℕ} (hp : 0 < p) (u : ℕ) :
    let μ := (Fintype.card (Fin m → α) : ℂ)⁻¹ • ∑ w, Y w
    ((Finset.univ.filter fun σ : β → Fin m → α ↦
        (η ≤ ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, Y (σ b) - μ‖) ∨
          ∃ b a, u ≤ countsFinsupp (σ b) a).card : ℝ) /
        (Fintype.card (β → Fin m → α) : ℝ) ≤
      (Fintype.card n : ℝ) *
        (4 * (p : ℝ) ^ 2 * R ^ 2 / ((Fintype.card β : ℝ) * η ^ 2)) ^ p +
      (Fintype.card α : ℝ) * Fintype.card β *
        Real.exp ((m : ℝ) / Fintype.card α - u * Real.log 2) := by
  classical
  intro μ
  let badMatrix : Finset (β → Fin m → α) := Finset.univ.filter fun σ ↦
    η ≤ ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, Y (σ b) - μ‖
  let badFrequency : Finset (β → Fin m → α) := Finset.univ.filter fun σ ↦
    ∃ b a, u ≤ countsFinsupp (σ b) a
  have hC : 0 < (Fintype.card (β → Fin m → α) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hbad : (Finset.univ.filter fun σ : β → Fin m → α ↦
      (η ≤ ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, Y (σ b) - μ‖) ∨
        ∃ b a, u ≤ countsFinsupp (σ b) a) = badMatrix ∪ badFrequency := by
    ext σ
    simp [badMatrix, badFrequency]
  have hunion : ((Finset.univ.filter fun σ : β → Fin m → α ↦
      (η ≤ ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, Y (σ b) - μ‖) ∨
        ∃ b a, u ≤ countsFinsupp (σ b) a).card : ℝ) ≤
      (badMatrix.card : ℝ) + badFrequency.card := by
    rw [hbad]
    exact_mod_cast Finset.card_union_le badMatrix badFrequency
  have hM := finite_uniform_average_sub_mean_tail_bound (β := β) Y hη hY hp
  have hF := uniform_word_family_frequency_tail (α := α) (β := β) m u
  calc
    _ ≤ ((badMatrix.card : ℝ) + badFrequency.card) /
        (Fintype.card (β → Fin m → α) : ℝ) := div_le_div_of_nonneg_right hunion hC.le
    _ = (badMatrix.card : ℝ) / (Fintype.card (β → Fin m → α) : ℝ) +
        (badFrequency.card : ℝ) / (Fintype.card (β → Fin m → α) : ℝ) := add_div _ _ _
    _ ≤ _ := add_le_add hM hF

open Classical in
/-- One sample simultaneously approximates the actual matrix mean and bounds every
letter count when the explicit numerical sum of failure bounds is below one.
No successful sample or concentration estimate is supplied as a hypothesis. -/
theorem exists_average_sub_mean_norm_lt_and_word_counts_lt
    {α β n : Type*} [Fintype α] [Fintype β] [Fintype n] [DecidableEq n]
    [Nonempty α] [Nonempty β] [Nonempty n]
    {m : ℕ} (Y : (Fin m → α) → Matrix n n ℂ) {R η : ℝ}
    (hη : 0 < η) (hY : ∀ w, ‖Y w‖ ≤ R) {p : ℕ} (hp : 0 < p) (u : ℕ)
    (hsmall : (Fintype.card n : ℝ) *
        (4 * (p : ℝ) ^ 2 * R ^ 2 / ((Fintype.card β : ℝ) * η ^ 2)) ^ p +
      (Fintype.card α : ℝ) * Fintype.card β *
        Real.exp ((m : ℝ) / Fintype.card α - u * Real.log 2) < 1) :
    let μ := (Fintype.card (Fin m → α) : ℂ)⁻¹ • ∑ w, Y w
    ∃ σ : β → Fin m → α,
      ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, Y (σ b) - μ‖ < η ∧
        ∀ b a, countsFinsupp (σ b) a < u := by
  classical
  intro μ
  let bad : Finset (β → Fin m → α) := Finset.univ.filter fun σ ↦
    (η ≤ ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, Y (σ b) - μ‖) ∨
      ∃ b a, u ≤ countsFinsupp (σ b) a
  have hC : 0 < (Fintype.card (β → Fin m → α) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have htail := finite_uniform_word_sampling_failure_bound (β := β) Y hη hY hp u
  have hratio : (bad.card : ℝ) / (Fintype.card (β → Fin m → α) : ℝ) < 1 :=
    htail.trans_lt hsmall
  have hcard : bad.card < (Finset.univ : Finset (β → Fin m → α)).card := by
    have hh := (div_lt_one hC).mp hratio
    exact_mod_cast hh
  obtain ⟨σ, _, hσ⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hgood : ¬((η ≤ ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, Y (σ b) - μ‖) ∨
      ∃ b a, u ≤ countsFinsupp (σ b) a) := by
    simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hσ
  refine ⟨σ, lt_of_not_ge (not_or.mp hgood).1, ?_⟩
  intro b a
  exact lt_of_not_ge fun h ↦ (not_or.mp hgood).2 ⟨b, a, h⟩

end Matrix
