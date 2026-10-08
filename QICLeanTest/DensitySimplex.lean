import QICLean.Analysis.DensitySimplex
import Mathlib.Tactic.NormNum

/-! Regression examples for genuine last-filter minima and boundary coordinates. -/

open scoped BigOperators
open Entropy

private theorem boundary_minimum :
    IsMinOn (simplexFilterObjective ![(1 : ℝ), 0] 1 1)
      {y : Fin 2 → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} ![1, 0] := by
  intro y hy
  have hy0 : y 0 ≤ 1 := (Finset.single_le_sum (fun i _ ↦ hy.1 i)
    (Finset.mem_univ 0)).trans_eq hy.2
  have hden : 0 < y 0 + 1 := add_pos_of_nonneg_of_pos (hy.1 0) zero_lt_one
  simpa [simplexFilterObjective, Fin.sum_univ_two, Real.rpow_neg_one] using
    one_div_le_one_div_of_le hden (by simpa [add_comm] using add_le_add_right hy0 1)

-- An actual boundary minimum with a zero input and output spectral weight.
example : ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
    ∀ i : Fin 2, (![1, 0] : Fin 2 → ℝ) i + 1 =
      max (normalizedFilterWeights ![1, 0] 1 1 ![1, 0] i / lam) 1 := by
  apply Exists.imp (fun lam h ↦ ⟨h.1, h.2.1, h.2.2.2.2⟩)
    (normalizedFilterWeights_clipped_of_isMinOn
      (r := ![1, 0]) (x := ![1, 0]) (a := 1) (b := 1)
      (by intro i; fin_cases i <;> norm_num)
      (by norm_num [Fin.sum_univ_two]) (by norm_num) (by norm_num)
      (by intro i; fin_cases i <;> norm_num)
      (by norm_num [Fin.sum_univ_two]) boundary_minimum)

-- Feasibility alone does not give the necessary conditions.
example : ¬ IsMinOn (simplexFilterObjective ![(1 : ℝ), 0] 1 1)
    {y : Fin 2 → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} ![0, 1] := by
  intro hm
  have h := hm (a := ![1, 0])
    (show (![1, 0] : Fin 2 → ℝ) ∈
      {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} from
      ⟨by intro i; fin_cases i <;> norm_num, by norm_num [Fin.sum_univ_two]⟩)
  norm_num [simplexFilterObjective, Fin.sum_univ_two, Real.rpow_neg_one] at h

-- At exponent zero every feasible density minimizes the objective.
example : IsMinOn (simplexFilterObjective ![(0 : ℝ), 1] 0 1)
    {y : Fin 2 → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} ![1, 0] := by
  exact fun y _ ↦ by simp [simplexFilterObjective, Fin.sum_univ_two]

-- The corresponding KKT multiplier cannot be positive: the exponent hypothesis matters.
example : ¬ ∃ lam : ℝ, 0 < lam ∧
    ∀ i : Fin 2, 0 < (![1, 0] : Fin 2 → ℝ) i →
      normalizedFilterWeights ![0, 1] 0 1 ![1, 0] i /
        ((![1, 0] : Fin 2 → ℝ) i + 1) = lam := by
  rintro ⟨lam, hpos, hsupp⟩
  have hz := hsupp 0 (by norm_num)
  norm_num [normalizedFilterWeights] at hz
  linarith
