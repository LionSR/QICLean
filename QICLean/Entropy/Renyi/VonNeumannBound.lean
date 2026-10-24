/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.Renyi.Defs
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Rényi entropies of order above one and the von Neumann entropy

For a probability vector `p` and an order `α > 1`, the concavity of the logarithm with weights
`p` gives `ln ∑ pᵢ^α = ln ∑ pᵢ pᵢ^{α−1} ≥ (α − 1) ∑ pᵢ ln pᵢ`. Dividing by `1 − α < 0` shows
that the Rényi entropy of order `α` is at most the Shannon entropy. Applied to the eigenvalues of
a density matrix, the Rényi entropy of order `α > 1` is at most the von Neumann entropy.

## Main results

* `inv_one_sub_mul_log_sum_rpow_le_sum_negMulLog`: `(1 − α)⁻¹ ln ∑ pᵢ^α ≤ −∑ pᵢ ln pᵢ`.
* `renyiEntropy_le_vonNeumannEntropy_of_one_lt`: `S_α(ρ) ≤ S(ρ)` for `α > 1`, when the
  eigenvalues of `ρ` are nonnegative and sum to one.
* `Matrix.PosSemidef.renyiEntropy_le_vonNeumannEntropy_of_one_lt`: the same for a positive
  semidefinite matrix of unit trace.
-/

open Matrix Finset
open scoped ComplexOrder

/-- **Rényi entropy of order above one of a probability vector.** For nonnegative `p` with
`∑ pᵢ = 1` and `α > 1`, `(1 − α)⁻¹ ln ∑ pᵢ^α ≤ ∑ negMulLog pᵢ = −∑ pᵢ ln pᵢ`. -/
theorem inv_one_sub_mul_log_sum_rpow_le_sum_negMulLog {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (h0 : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) {α : ℝ} (hα : 1 < α) :
    (1 - α)⁻¹ * Real.log (∑ i, p i ^ α) ≤ ∑ i, Real.negMulLog (p i) := by
  classical
  set t := univ.filter (fun i ↦ 0 < p i)
  have hzero : ∀ i, i ∉ t → p i = 0 := fun i hi ↦ by
    simp only [t, mem_filter, mem_univ, true_and, not_lt] at hi
    exact le_antisymm hi (h0 i)
  have ht1 : ∑ i ∈ t, p i = 1 := by
    rw [← h1, sum_filter_of_ne fun i _ h ↦ lt_of_le_of_ne (h0 i) (Ne.symm h)]
  have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := t) (w := p)
    (p := fun i ↦ p i ^ (α - 1)) (fun i _ ↦ h0 i) ht1
    (fun i hi ↦ Real.rpow_pos_of_pos (mem_filter.1 hi).2 _)
  simp only [smul_eq_mul] at hJ
  have hpow : ∀ i ∈ t, p i * p i ^ (α - 1) = p i ^ α := fun i hi ↦ by
    have hp := (mem_filter.1 hi).2
    rw [← Real.rpow_one_add' hp.le (by linarith)]; ring_nf
  have hlog : ∀ i ∈ t, p i * Real.log (p i ^ (α - 1)) = (α - 1) * (p i * Real.log (p i)) :=
    fun i hi ↦ by rw [Real.log_rpow (mem_filter.1 hi).2]; ring
  rw [sum_congr rfl hpow, sum_congr rfl hlog, ← mul_sum] at hJ
  have hS : ∑ i ∈ t, p i ^ α = ∑ i, p i ^ α :=
    sum_subset (subset_univ _) fun i _ hi ↦ by rw [hzero i hi, Real.zero_rpow (by linarith)]
  have hL : ∑ i ∈ t, p i * Real.log (p i) = ∑ i, p i * Real.log (p i) :=
    sum_subset (subset_univ _) fun i _ hi ↦ by rw [hzero i hi, zero_mul]
  rw [hS, hL] at hJ
  have hneg : ∑ i, Real.negMulLog (p i) = -∑ i, p i * Real.log (p i) := by
    simp [Real.negMulLog, sum_neg_distrib]
  rw [hneg]
  have hinv : (1 - α)⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
  calc (1 - α)⁻¹ * Real.log (∑ i, p i ^ α)
      ≤ (1 - α)⁻¹ * ((α - 1) * ∑ i, p i * Real.log (p i)) :=
        mul_le_mul_of_nonpos_left hJ hinv.le
    _ = -∑ i, p i * Real.log (p i) := by
        rw [show α - 1 = -(1 - α) by ring, neg_mul, mul_neg, ← mul_assoc,
          inv_mul_cancel₀ (by linarith : (1 - α) ≠ 0), one_mul]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Rényi entropy of order above one and the von Neumann entropy.** If the eigenvalues of the
Hermitian matrix `ρ` are nonnegative and sum to one, then `S_α(ρ) ≤ S(ρ)` for every `α > 1`. -/
theorem renyiEntropy_le_vonNeumannEntropy_of_one_lt {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (h0 : ∀ i, 0 ≤ hρ.eigenvalues i) (h1 : ∑ i, hρ.eigenvalues i = 1) {α : ℝ} (hα : 1 < α) :
    renyiEntropy ρ hρ α ≤ vonNeumannEntropy ρ hρ := by
  have hα0 : α ≠ 0 := by linarith
  simp only [renyiEntropy, hα0, hα.ne', ↓reduceIte]
  change (1 - α)⁻¹ * Real.log (RCLike.re ((hρ.cfc (fun x => x ^ α)).trace)) ≤ _
  rw [hρ.trace_cfc_eq_sum_re, vonNeumannEntropy]
  exact inv_one_sub_mul_log_sum_rpow_le_sum_negMulLog _ h0 h1 hα

/-- **Rényi entropy of order above one of a density matrix.** For a positive semidefinite `ρ`
of unit trace and every `α > 1`, `S_α(ρ) ≤ S(ρ)`. -/
theorem Matrix.PosSemidef.renyiEntropy_le_vonNeumannEntropy_of_one_lt {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {α : ℝ} (hα : 1 < α) :
    renyiEntropy ρ hρ.isHermitian α ≤ vonNeumannEntropy ρ hρ.isHermitian := by
  refine _root_.renyiEntropy_le_vonNeumannEntropy_of_one_lt hρ.isHermitian
    hρ.eigenvalues_nonneg ?_ hα
  have h := congrArg RCLike.re hρ.isHermitian.trace_eq_sum_eigenvalues
  rw [htr] at h
  simpa using h.symm
