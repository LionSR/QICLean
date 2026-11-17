/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.JordanBlockDirectSum
import Mathlib.Tactic.NoncommRing

/-!
# Operator-norm comparison under similarity

This file formalizes the basis-level comparison used in Wolf's Equation
(8.108).  It deliberately keeps a chosen invertible similarity `A, B`
explicit.  Wolf defines the Jordan condition number `κ_T` as an infimum over
all Jordan bases. `QICLean.Analysis.JordanConditionNumber` supplies the
limiting comparison when a common Jordan-power norm has been established.

Source: Wolf (2012), Chapter 8, Equation (8.108), local source
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1247--1254.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- An invertible change of basis has condition factor at least one. -/
theorem one_le_l2_opNorm_mul_of_mul_eq_one (P Q : Matrix ι ι ℂ) (hPQ : P * Q = 1) :
    1 ≤ ‖P‖ * ‖Q‖ := by
  simpa only [hPQ, norm_one] using l2_opNorm_mul P Q

/-- Equation (8.108) for one chosen similarity `X = A J A⁻¹`, with the
inverse supplied as `B`.

No Jordan-normal-form existence or minimization of the condition factor is
assumed here. -/
theorem l2_opNorm_pow_similarity_bounds
    (A B J X : Matrix ι ι ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (hX : X = A * J * B) (n : ℕ) :
    (‖A‖ * ‖B‖)⁻¹ * ‖J ^ n‖ ≤ ‖X ^ n‖ ∧
      ‖X ^ n‖ ≤ (‖A‖ * ‖B‖) * ‖J ^ n‖ := by
  have hcond : 0 < ‖A‖ * ‖B‖ :=
    zero_lt_one.trans_le (one_le_l2_opNorm_mul_of_mul_eq_one A B hAB)
  have hpow : X ^ n = A * J ^ n * B := by
    induction n with
    | zero => simpa only [pow_zero, Matrix.mul_one] using hAB.symm
    | succ n ih =>
        rw [pow_succ, ih, hX, pow_succ]
        calc
          A * J ^ n * B * (A * J * B) = A * J ^ n * (B * A) * J * B := by
            simp only [Matrix.mul_assoc]
          _ = A * (J ^ n * J) * B := by
            rw [hBA]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hpow' : J ^ n = B * X ^ n * A := by
    rw [hpow]
    symm
    calc
      B * (A * J ^ n * B) * A = (B * A) * J ^ n * (B * A) := by
        simp only [Matrix.mul_assoc]
      _ = J ^ n := by rw [hBA, Matrix.one_mul, Matrix.mul_one]
  constructor
  · have hle : ‖J ^ n‖ ≤ (‖A‖ * ‖B‖) * ‖X ^ n‖ := by
      calc
        ‖J ^ n‖ = ‖B * X ^ n * A‖ := by rw [hpow']
        _ ≤ ‖B * X ^ n‖ * ‖A‖ := l2_opNorm_mul _ _
        _ ≤ (‖B‖ * ‖X ^ n‖) * ‖A‖ := by
          gcongr
          exact l2_opNorm_mul _ _
        _ = (‖A‖ * ‖B‖) * ‖X ^ n‖ := by ring
    exact (inv_mul_le_iff₀ hcond).2 hle
  · rw [hpow]
    calc
      ‖A * J ^ n * B‖ ≤ ‖A * J ^ n‖ * ‖B‖ := l2_opNorm_mul _ _
      _ ≤ (‖A‖ * ‖J ^ n‖) * ‖B‖ := by
        gcongr
        exact l2_opNorm_mul _ _
      _ = (‖A‖ * ‖B‖) * ‖J ^ n‖ := by ring

/-- Polynomial-exponential scaling after an explicit similarity to a finite
sum of genuine Jordan blocks. The upper bound holds at every positive
exponent and the printed lower constant holds from `d - 1` onward.

**Scope restriction:** this constructs the constants for supplied block data
and a chosen similarity, not for an arbitrary channel or its infimum.
See `docs/paper-gaps/wolf_thm823_jordan_scaling_qualifications.tex`.
Source: Wolf Eqs. (8.106)--(8.108), lines 1226--1267. -/
theorem exists_pos_pow_similarity_jordanBlockDirectSum_bounds
    {β : Type*} [Fintype β] [DecidableEq β]
    (D : β → ℕ) [∀ i, NeZero (D i)] (a : β → ℂ) (k : β)
    (hmod : ∀ i, ‖a i‖ ≤ ‖a k‖)
    (hdim : ∀ i, ‖a i‖ = ‖a k‖ → D i ≤ D k)
    (hk0 : 0 < ‖a k‖) (hk1 : ‖a k‖ ≤ 1)
    (P Q X : Matrix (Σ i, Fin (D i)) (Σ i, Fin (D i)) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hX : X = P * jordanBlockDirectSum D a * Q) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      (∀ n : ℕ, 0 < n → ‖X ^ n‖ ≤ C₂ * ‖a k‖ ^ n * (n : ℝ) ^ (D k - 1)) ∧
      ∀ n : ℕ, D k - 1 ≤ n →
        (‖P‖ * ‖Q‖)⁻¹ * ((‖a k‖ * (D k - 1 : ℕ))⁻¹) ^ (D k - 1) *
          ‖a k‖ ^ n * (n : ℝ) ^ (D k - 1) ≤ ‖X ^ n‖ := by
  have : Nonempty (Σ i, Fin (D i)) := ⟨⟨k, 0⟩⟩
  have hc : 0 < ‖P‖ * ‖Q‖ :=
    zero_lt_one.trans_le (one_le_l2_opNorm_mul_of_mul_eq_one P Q hPQ)
  obtain ⟨C, hC, hupper⟩ :=
    exists_pos_jordanBlockDirectSum_pow_le_polynomial D a k hmod hdim hk0 hk1
  refine ⟨(‖P‖ * ‖Q‖) * C, mul_pos hc hC, ?_, ?_⟩
  · intro n hn
    have hb := (l2_opNorm_pow_similarity_bounds P Q _ X hPQ hQP hX n).2
    exact hb.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hupper n hn) hc.le)
  · intro n hn
    have hb := (l2_opNorm_pow_similarity_bounds P Q _ X hPQ hQP hX n).1
    refine le_trans ?_ hb
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (le_l2_opNorm_jordanBlockDirectSum_pow_polynomial D a k hk0 n hn)
      (inv_nonneg.mpr hc.le)

/-- Zero maximal modulus after a supplied Jordan similarity gives exact
vanishing from the largest block dimension onward. It does not imply
vanishing at earlier positive exponents.
Source qualification: Wolf Eq. (8.107), documented in
`docs/paper-gaps/wolf_thm823_jordan_scaling_qualifications.tex`. -/
theorem pow_eq_zero_of_similarity_jordanBlockDirectSum_maximal_zero
    {β : Type*} [Fintype β] [DecidableEq β]
    (D : β → ℕ) [∀ i, NeZero (D i)] (a : β → ℂ) (k : β)
    (hmod : ∀ i, ‖a i‖ ≤ ‖a k‖)
    (hdim : ∀ i, ‖a i‖ = ‖a k‖ → D i ≤ D k) (hk0 : ‖a k‖ = 0)
    (P Q X : Matrix (Σ i, Fin (D i)) (Σ i, Fin (D i)) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hX : X = P * jordanBlockDirectSum D a * Q) (n : ℕ) (hn : D k ≤ n) :
    X ^ n = 0 := by
  have : Nonempty (Σ i, Fin (D i)) := ⟨⟨k, 0⟩⟩
  have hb := (l2_opNorm_pow_similarity_bounds P Q _ X hPQ hQP hX n).2
  rw [jordanBlockDirectSum_pow_eq_zero_of_maximal_zero D a k hmod hdim hk0 n hn,
    norm_zero, mul_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

end Matrix
