/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SoftHardTruncation
import QICLean.Analysis.MatrixBernsteinInputs
import Mathlib.Data.Nat.Choose.Sum

/-!
# The finite heat expansion of soft truncation

The defining polynomial is expanded into the actual heat functions at times from zero through
`m / t`. This is the finite algebra underlying ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268. The identity term and the scale factor are retained.
-/

open Finset

namespace Real

/-- The coefficient of the heat function at time `a / t` in the finite binomial expansion.
ALVV, arXiv:1602.08828v2, `def:ft` and `lem:exp-approx-eff`, lines 1152–1157 and 1262–1268. -/
noncomputable def softTruncationHeatCoefficient (t : ℝ) (m a : ℕ) : ℝ :=
  t * (-1) ^ a * ∑ j ∈ range m, ((j + 1).choose a : ℝ) / (j + 1 : ℝ)

private theorem one_sub_pow_eq_sum (z : ℝ) {j m : ℕ} (hj : j ≤ m) :
    (1 - z) ^ j = ∑ a ∈ range (m + 1), (-1 : ℝ) ^ a * (j.choose a : ℝ) * z ^ a := by
  calc
    _ = (-z + 1) ^ j := by congr 1; ring
    _ = ∑ a ∈ range (j + 1), (-z) ^ a * (1 : ℝ) ^ (j - a) * (j.choose a : ℝ) :=
      (Commute.all (-z) (1 : ℝ)).add_pow j
    _ = ∑ a ∈ range (j + 1), (-1 : ℝ) ^ a * (j.choose a : ℝ) * z ^ a := by
      apply sum_congr rfl
      intro a _ha
      rw [neg_pow]
      simp only [one_pow, mul_one]
      ring
    _ = _ := by
      apply sum_subset (range_mono (Nat.add_le_add_right hj 1))
      intro a _ha hnot
      have hja : j < a := by simp only [mem_range] at hnot; omega
      simp [Nat.choose_eq_zero_of_lt hja]

/-- Soft truncation is an exact finite linear combination of heat functions, including the
constant heat function. ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
lemma softTruncation_eq_sum_heat (t : ℝ) (m : ℕ) (x : ℝ) :
    softTruncation t m x = ∑ a ∈ range (m + 1),
      softTruncationHeatCoefficient t m a * exp (-((a : ℝ) * x / t)) := by
  have he (j : ℕ) (hj : j ∈ range m) :
      (1 - exp (-(x / t))) ^ (j + 1) / (j + 1 : ℝ) =
        ∑ a ∈ range (m + 1),
          ((-1 : ℝ) ^ a * ((j + 1).choose a : ℝ) / (j + 1 : ℝ)) *
            exp (-((a : ℝ) * x / t)) := by
    rw [one_sub_pow_eq_sum _ (Nat.succ_le_of_lt (mem_range.mp hj)), sum_div]
    apply sum_congr rfl
    intro a _ha
    rw [← exp_nat_mul]
    have hexp : (a : ℝ) * (-(x / t)) = -((a : ℝ) * x / t) := by ring
    rw [hexp]
    ring
  unfold softTruncation
  simp_rw [sum_congr rfl he]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro a _ha
  simp only [softTruncationHeatCoefficient, mul_sum, sum_mul]
  apply sum_congr rfl
  intro j _hj
  ring

private theorem sum_choose_eq_two_pow {j m : ℕ} (hj : j ≤ m) :
    ∑ a ∈ range (m + 1), (j.choose a : ℝ) = (2 : ℝ) ^ j := by
  calc
    _ = ∑ a ∈ range (j + 1), (j.choose a : ℝ) := by
      symm
      apply sum_subset (range_mono (Nat.add_le_add_right hj 1))
      intro a _ha hnot
      have hja : j < a := by simp only [mem_range] at hnot; omega
      simp [Nat.choose_eq_zero_of_lt hja]
    _ = _ := by exact_mod_cast Nat.sum_range_choose j

/-- The total absolute coefficient budget retains the scale factor. This finite bound supports
ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
lemma sum_abs_softTruncationHeatCoefficient_le (t : ℝ) (m : ℕ) (ht : 0 ≤ t) :
    ∑ a ∈ range (m + 1), |softTruncationHeatCoefficient t m a| ≤
      t * (2 : ℝ) ^ (m + 1) := by
  have hn (a : ℕ) : 0 ≤ ∑ j ∈ range m, ((j + 1).choose a : ℝ) / (j + 1 : ℝ) :=
    sum_nonneg fun _ _ ↦ div_nonneg (Nat.cast_nonneg _) (by positivity)
  have habs (a : ℕ) : |softTruncationHeatCoefficient t m a| =
      t * ∑ j ∈ range m, ((j + 1).choose a : ℝ) / (j + 1 : ℝ) := by
    simp [softTruncationHeatCoefficient, abs_mul, abs_of_nonneg ht, abs_of_nonneg (hn a)]
  simp_rw [habs]
  rw [← mul_sum, sum_comm]
  apply mul_le_mul_of_nonneg_left ?_ ht
  calc
    _ = ∑ j ∈ range m, (2 : ℝ) ^ (j + 1) / (j + 1 : ℝ) := by
      apply sum_congr rfl
      intro j hj
      rw [← sum_div, sum_choose_eq_two_pow (Nat.succ_le_of_lt (mem_range.mp hj))]
    _ ≤ ∑ j ∈ range m, (2 : ℝ) ^ (j + 1) := by
      apply sum_le_sum
      intro j _hj
      exact div_le_self (by positivity) (by norm_num)
    _ ≤ (2 : ℝ) ^ (m + 1) := by
      clear hn habs
      induction m with
      | zero => norm_num
      | succ m ih =>
        rw [sum_range_succ]
        rw [pow_succ (2 : ℝ) (m + 1)]
        linarith

end Real

namespace Matrix

open scoped Matrix.Norms.L2Operator

/-- Functional calculus transfers the exact scalar heat expansion to the same Hermitian
matrix. ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
lemma IsHermitian.cfc_softTruncation_eq_sum_heat
    {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ} (hU : U.IsHermitian)
    (t : ℝ) (m : ℕ) :
    cfc (Real.softTruncation t m) U = ∑ a ∈ Finset.range (m + 1),
      Real.softTruncationHeatCoefficient t m a •
        NormedSpace.exp (-(((a : ℝ) / t) • U)) := by
  classical
  have hf : Real.softTruncation t m = ∑ a ∈ range (m + 1),
      (fun x : ℝ ↦ Real.softTruncationHeatCoefficient t m a *
        Real.exp (-((a : ℝ) * x / t))) := by
    funext x
    simpa only [Finset.sum_apply] using Real.softTruncation_eq_sum_heat t m x
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ U) :=
    U.finite_real_spectrum.continuousOn f
  rw [hf, cfc_sum _ _ _ (fun _ _ ↦ hc _)]
  apply sum_congr rfl
  intro a _ha
  rw [cfc_const_mul _ _ U (hc _), ← neg_smul, hU.exp_smul_eq_cfc]
  apply congrArg (fun f : ℝ → ℝ ↦ Real.softTruncationHeatCoefficient t m a • cfc f U)
  funext x
  congr 1
  ring

end Matrix
