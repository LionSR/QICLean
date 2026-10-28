/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.WordMultiplicity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Simultaneous frequencies in independent uniform words

For a uniform word of length `m` over an alphabet of size `n ≥ 1`, the exact
exponential moment of a fixed letter count is `(1 + 1 / n)^m` at base `2`.
For `ℓ` independent uniform words, scalar exponential Markov and a union over
all sample indices and letters give

`Pr (∃ b a, u ≤ count (word b) a) ≤ n * ℓ * exp (m / n - u * log 2)`.

The probability is expressed as the actual cardinality fraction in the full
finite product of words. The exact rational bound is proved first. An explicit
integer ceiling gives a simultaneous failure probability at most any `δ > 0`.
Empty sample families and zero word length are included.

These estimates control word frequencies alongside operator-norm concentration
in the sampled-projector argument of LVV, arXiv:1307.5143v1, Section 2.3.1,
Corollary 2.14. Ground-energy normalization and operator approximation are
separate estimates.
-/

open scoped BigOperators

namespace WordMultiplicity

open Classical in
/-- The exact sum of base-two exponential letter counts over all words.
Each position contributes `card α + 1` after summing over its letter. -/
theorem sum_two_pow_countsFinsupp {α : Type*} [Fintype α] (a : α) (m : ℕ) :
    (∑ w : Fin m → α, (2 : ℝ) ^ countsFinsupp w a) =
      ((Fintype.card α : ℝ) + 1) ^ m := by
  classical
  have hfactor (w : Fin m → α) :
      (2 : ℝ) ^ countsFinsupp w a = ∏ j, if w j = a then (2 : ℝ) else 1 := by
    simp only [countsFinsupp, Finsupp.finsetSum_apply]
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro j _
    by_cases h : w j = a
    · simp [h]
    · simp [h]
  have hsum : (∑ b : α, if b = a then (2 : ℝ) else 1) =
      (Fintype.card α : ℝ) + 1 := by
    have hp (b : α) : (if b = a then (2 : ℝ) else 1) =
        1 + (if b = a then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    simp_rw [hp, Finset.sum_add_distrib]
    simp
  simp_rw [hfactor]
  have hexp := (Fintype.sum_pow (fun b : α ↦ if b = a then (2 : ℝ) else 1) m).symm
  simpa only [hsum] using hexp

open Classical in
/-- The exact base-two exponential moment of a letter count in a uniform word. -/
theorem average_two_pow_countsFinsupp {α : Type*} [Fintype α] [Nonempty α]
    (a : α) (m : ℕ) :
    (∑ w : Fin m → α, (2 : ℝ) ^ countsFinsupp w a) /
        (Fintype.card (Fin m → α) : ℝ) =
      (1 + (Fintype.card α : ℝ)⁻¹) ^ m := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [sum_two_pow_countsFinsupp, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ← div_pow]
  congr 1
  field_simp

open Classical in
/-- The average of a coordinate function in a full finite product is its marginal average. -/
private theorem average_eval {I S : Type*} [Fintype I] [Fintype S] [Nonempty S]
    (j : I) (f : S → ℝ) :
    (∑ σ : I → S, f (σ j)) / (Fintype.card (I → S) : ℝ) =
      (∑ s, f s) / (Fintype.card S : ℝ) := by
  classical
  let e := Equiv.funSplitAt j S
  have heq : (∑ σ : I → S, f (σ j)) =
      (Fintype.card ({i : I // i ≠ j} → S) : ℝ) * (∑ s, f s) := by
    rw [← e.symm.sum_comp (fun σ ↦ f (σ j)), Fintype.sum_prod_type]
    simp [e, Equiv.funSplitAt_symm_apply, Finset.mul_sum]
  rw [heq, Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  have hC : (Fintype.card ({i : I // i ≠ j} → S) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp


open Classical in
/-- The simultaneous word-frequency bound from the exact exponential moment and
scalar Markov, with the union taken over all sample indices and alphabet letters.
The left side is the actual fraction of exceptional assignments in the full product. -/
theorem uniform_word_family_frequency_tail_exact
    {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] (m u : ℕ) :
    ((Finset.univ.filter fun σ : β → Fin m → α ↦
        ∃ b a, u ≤ countsFinsupp (σ b) a).card : ℝ) /
        (Fintype.card (β → Fin m → α) : ℝ) ≤
      (Fintype.card α : ℝ) * Fintype.card β *
        ((1 + (Fintype.card α : ℝ)⁻¹) ^ m / (2 : ℝ) ^ u) := by
  classical
  let E (i : β × α) : Finset (β → Fin m → α) :=
    Finset.univ.filter fun σ ↦ u ≤ countsFinsupp (σ i.1) i.2
  let bad : Finset (β → Fin m → α) :=
    Finset.univ.filter fun σ ↦ ∃ b a, u ≤ countsFinsupp (σ b) a
  have hC : 0 < (Fintype.card (β → Fin m → α) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hpow : 0 < (2 : ℝ) ^ u := by positivity
  have hE (i : β × α) : (E i).card / (Fintype.card (β → Fin m → α) : ℝ) ≤
      (1 + (Fintype.card α : ℝ)⁻¹) ^ m / (2 : ℝ) ^ u := by
    have hmarkov : ((E i).card : ℝ) * (2 : ℝ) ^ u ≤
        ∑ σ : β → Fin m → α, (2 : ℝ) ^ countsFinsupp (σ i.1) i.2 := by
      calc
        _ ≤ ∑ σ ∈ E i, (2 : ℝ) ^ countsFinsupp (σ i.1) i.2 := by
          simpa only [nsmul_eq_mul] using (E i).card_nsmul_le_sum
            (fun σ ↦ (2 : ℝ) ^ countsFinsupp (σ i.1) i.2) ((2 : ℝ) ^ u)
            (fun σ hσ ↦ pow_le_pow_right₀ (by norm_num) (Finset.mem_filter.mp hσ).2)
        _ ≤ ∑ σ : β → Fin m → α, (2 : ℝ) ^ countsFinsupp (σ i.1) i.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun σ _ _ ↦ by positivity)
    have hh : (E i).card / (Fintype.card (β → Fin m → α) : ℝ) ≤
        ((∑ σ : β → Fin m → α, (2 : ℝ) ^ countsFinsupp (σ i.1) i.2) /
          (Fintype.card (β → Fin m → α) : ℝ)) / (2 : ℝ) ^ u := by
      apply (le_div_iff₀ hpow).mpr
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hmarkov hC.le
    rw [average_eval i.1 (fun w ↦ (2 : ℝ) ^ countsFinsupp w i.2),
      average_two_pow_countsFinsupp] at hh
    exact hh
  have hbad : bad = Finset.univ.biUnion E := by
    ext σ
    simp [bad, E]
  have hunion : (bad.card : ℝ) ≤ ∑ i : β × α, ((E i).card : ℝ) := by
    rw [hbad]
    exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := E))
  calc
    _ ≤ (∑ i : β × α, ((E i).card : ℝ)) /
        (Fintype.card (β → Fin m → α) : ℝ) := div_le_div_of_nonneg_right hunion hC.le
    _ = ∑ i : β × α, (E i).card / (Fintype.card (β → Fin m → α) : ℝ) :=
      by simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ _i : β × α, (1 + (Fintype.card α : ℝ)⁻¹) ^ m / (2 : ℝ) ^ u :=
      Finset.sum_le_sum fun i _ ↦ hE i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Nat.cast_mul, nsmul_eq_mul]
      ring

open Classical in
/-- The simultaneous exponential tail for independent uniform words:
`n * ℓ * exp (m / n - u * log 2)`. This includes empty sample families. -/
theorem uniform_word_family_frequency_tail
    {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] (m u : ℕ) :
    ((Finset.univ.filter fun σ : β → Fin m → α ↦
        ∃ b a, u ≤ countsFinsupp (σ b) a).card : ℝ) /
        (Fintype.card (β → Fin m → α) : ℝ) ≤
      (Fintype.card α : ℝ) * Fintype.card β *
        Real.exp ((m : ℝ) / Fintype.card α - u * Real.log 2) := by
  have hmajor : (1 + (Fintype.card α : ℝ)⁻¹) ^ m ≤
      Real.exp ((m : ℝ) / Fintype.card α) := by
    calc
      _ ≤ (Real.exp (Fintype.card α : ℝ)⁻¹) ^ m :=
        pow_le_pow_left₀ (by positivity)
          (by simpa only [add_comm] using Real.add_one_le_exp (Fintype.card α : ℝ)⁻¹) _
      _ = _ := by simp only [← Real.exp_nat_mul, div_eq_mul_inv]
  have hh : (1 + (Fintype.card α : ℝ)⁻¹) ^ m / (2 : ℝ) ^ u ≤
      Real.exp ((m : ℝ) / Fintype.card α - u * Real.log 2) := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hmajor (by positivity)
  exact (uniform_word_family_frequency_tail_exact (α := α) (β := β) m u).trans
    (mul_le_mul_of_nonneg_left hh (by positivity))


open Classical in
/-- The word-frequency failure fraction is at most `δ` under the explicit
logarithmic threshold. For an empty sample family, the exceptional set is empty. -/
theorem uniform_word_family_frequency_tail_le
    {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] (m u : ℕ)
    {δ : ℝ} (hδ : 0 < δ)
    (hu : (m : ℝ) / Fintype.card α +
      Real.log ((Fintype.card α : ℝ) * Fintype.card β / δ) ≤ u * Real.log 2) :
    ((Finset.univ.filter fun σ : β → Fin m → α ↦
        ∃ b a, u ≤ countsFinsupp (σ b) a).card : ℝ) /
        (Fintype.card (β → Fin m → α) : ℝ) ≤ δ := by
  apply (uniform_word_family_frequency_tail (α := α) (β := β) m u).trans
  by_cases hβ : Fintype.card β = 0
  · simpa only [hβ, Nat.cast_zero, mul_zero, zero_mul] using hδ.le
  let c : ℝ := (Fintype.card α : ℝ) * Fintype.card β
  have hc : 0 < c := mul_pos
    (by exact_mod_cast Fintype.card_pos)
    (by exact_mod_cast Nat.pos_of_ne_zero hβ)
  have hlog : Real.log (c / δ) = -Real.log (δ / c) := by
    rw [Real.log_div hc.ne' hδ.ne', Real.log_div hδ.ne' hc.ne']
    ring
  change (m : ℝ) / Fintype.card α + Real.log (c / δ) ≤ _ at hu
  rw [hlog] at hu
  have hexp : (m : ℝ) / Fintype.card α - u * Real.log 2 ≤ Real.log (δ / c) := by
    linarith
  change c * Real.exp _ ≤ δ
  calc
    _ ≤ c * Real.exp (Real.log (δ / c)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hc.le
    _ = δ := by rw [Real.exp_log (div_pos hδ hc)]; field_simp

open Classical in
/-- An explicit integer threshold with simultaneous failure fraction at most `δ`.
For a nonempty sample family it is the ceiling of
`(m / n + log (n * ℓ / δ)) / log 2`. -/
theorem uniform_word_family_frequency_tail_ceil
    {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] (m : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    let u := ⌈((m : ℝ) / Fintype.card α +
      Real.log ((Fintype.card α : ℝ) * Fintype.card β / δ)) / Real.log 2⌉₊
    ((Finset.univ.filter fun σ : β → Fin m → α ↦
        ∃ b a, u ≤ countsFinsupp (σ b) a).card : ℝ) /
        (Fintype.card (β → Fin m → α) : ℝ) ≤ δ := by
  intro u
  apply uniform_word_family_frequency_tail_le m u hδ
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp (Nat.le_ceil _)

end WordMultiplicity
