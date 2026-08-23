/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.JordanBlockPower
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial scaling of one Jordan block

This file derives the source-shaped polynomial-exponential scaling of a
single Jordan block from Wolf's Equation (8.104).  For a block of dimension
`D`, eigenvalue `a` with `0 < ‖a‖ ≤ 1`, and `D - 1 ≤ n`, the norm of its
`n`-th power is bounded above and below by explicit positive constants times

`‖a‖ ^ n * n ^ (D - 1)`.

In the application to Wolf's Theorem "Asymptotic convergence I", `‖a‖` is
the largest subperipheral modulus `μ` and `D` is the largest corresponding
Jordan-block dimension `d_μ`.  Selecting that block from a Jordan normal form,
proving eventual dominance in the block direct sum, and passing from a chosen
similarity factor to Wolf's infimum `κ_T` are deliberately outside this file.
The assumption `0 < ‖a‖` also records the source boundary at `μ = 0`, where a
nontrivial nilpotent block has nonzero small positive powers but the displayed
scaling factor vanishes.

Source: Wolf (2012), Chapter 8, Equations (8.104), (8.106), and (8.107), local
source `Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1197--1214
and 1225--1266.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

private theorem div_pow_le_choose_cast (n k : ℕ) (hk : k ≤ n) :
    ((n : ℝ) / (k : ℝ)) ^ k ≤ (n.choose k : ℝ) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have hkm : k ≤ m := by omega
      by_cases hk0 : k = 0
      · subst k
        simp
      · have hkpos : 0 < (k : ℝ) := by positivity
        have hksuccpos : 0 < (k + 1 : ℝ) := by positivity
        have hratio : ((m + 1 : ℕ) : ℝ) / (k + 1 : ℕ) ≤ (m : ℝ) / k := by
          norm_num only [Nat.cast_add, Nat.cast_one]
          rw [div_le_div_iff₀ hksuccpos hkpos]
          have hkmR : (k : ℝ) ≤ m := by exact_mod_cast hkm
          nlinarith
        have hpowratio :
            (((m + 1 : ℕ) : ℝ) / (k + 1 : ℕ)) ^ k ≤ ((m : ℝ) / k) ^ k := by
          gcongr
        have hih := ih m hkm
        calc
          (((m + 1 : ℕ) : ℝ) / (k + 1 : ℕ)) ^ (k + 1) =
              (((m + 1 : ℕ) : ℝ) / (k + 1 : ℕ)) ^ k *
                (((m + 1 : ℕ) : ℝ) / (k + 1 : ℕ)) := by rw [pow_succ]
          _ ≤ ((m : ℝ) / k) ^ k * (((m + 1 : ℕ) : ℝ) / (k + 1 : ℕ)) := by
            gcongr
          _ ≤ (m.choose k : ℝ) * (((m + 1 : ℕ) : ℝ) / (k + 1 : ℕ)) := by
            gcongr
          _ = ((m + 1).choose (k + 1) : ℝ) := by
            field_simp
            exact_mod_cast (by
              simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq m k))

/-- The lower polynomial-exponential estimate for one Jordan block, obtained
from the lower half of Wolf's Equation (8.104) with `k₀ = D - 1` and
`(n / k₀) ^ k₀ ≤ n.choose k₀`.

The hypotheses `0 < ‖a‖` and `D - 1 ≤ n` make explicit the positive-modulus
and sufficiently-large-positive-power range used by the source argument. -/
theorem le_l2_opNorm_jordanBlock_pow_polynomial (D : ℕ) [NeZero D]
    (a : ℂ) (n : ℕ) (ha : 0 < ‖a‖) (hn : D - 1 ≤ n) :
    ((‖a‖ * (D - 1 : ℕ))⁻¹) ^ (D - 1) * ‖a‖ ^ n *
        (n : ℝ) ^ (D - 1) ≤ ‖jordanBlock D a ^ n‖ := by
  let k := D - 1
  have hk : k ≤ min n (D - 1) := le_min hn le_rfl
  have hbase := le_l2_opNorm_jordanBlock_pow D a n k hk
  by_cases hk0 : k = 0
  · simpa [k, hk0] using hbase
  · have hkpos : 0 < (k : ℝ) := by positivity
    have hchoose : ((n : ℝ) / (k : ℝ)) ^ k ≤ (n.choose k : ℝ) :=
      div_pow_le_choose_cast n k hn
    have hpow : ‖a‖ ^ n = ‖a‖ ^ (n - k) * ‖a‖ ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hn]
    have halg : ((‖a‖ * (k : ℝ))⁻¹) ^ k * ‖a‖ ^ n * (n : ℝ) ^ k =
        ‖a‖ ^ (n - k) * ((n : ℝ) / (k : ℝ)) ^ k := by
      rw [hpow]
      field_simp [mul_pow]
      rw [← mul_pow, ← mul_pow]
      congr 1
      field_simp [ha.ne', hkpos.ne']
    change ((‖a‖ * (k : ℝ))⁻¹) ^ k * ‖a‖ ^ n * (n : ℝ) ^ k ≤ _
    calc
      ((‖a‖ * (k : ℝ))⁻¹) ^ k * ‖a‖ ^ n * (n : ℝ) ^ k =
          ‖a‖ ^ (n - k) * ((n : ℝ) / (k : ℝ)) ^ k := halg
      _ ≤ ‖a‖ ^ (n - k) * (n.choose k : ℝ) := by gcongr
      _ ≤ ‖jordanBlock D a ^ n‖ := hbase

/-- An explicit upper polynomial-exponential estimate for one Jordan block,
derived from the upper half of Wolf's Equation (8.104).  The constant
`D * ‖a‖⁻¹ ^ (D - 1)` is deliberately block-local; Wolf only asserts the
existence of a global `C₂` after the eventual largest-block argument. -/
theorem l2_opNorm_jordanBlock_pow_le_polynomial (D : ℕ) [NeZero D]
    (a : ℂ) (n : ℕ) (ha : 0 < ‖a‖) (ha1 : ‖a‖ ≤ 1)
    (hn : D - 1 ≤ n) :
    ‖jordanBlock D a ^ n‖ ≤
      (D : ℝ) * (‖a‖⁻¹) ^ (D - 1) * ‖a‖ ^ n *
        (n : ℝ) ^ (D - 1) := by
  let kTop := D - 1
  have hD : kTop + 1 = D := by
    have := NeZero.pos D
    omega
  have hmin : min n (D - 1) = kTop := by simp [kTop, hn]
  have hsum := l2_opNorm_jordanBlock_pow_le D a n
  rw [hmin] at hsum
  have hterm : ∀ k ∈ Finset.range (kTop + 1),
      ‖a‖ ^ (n - k) * (n.choose k : ℝ) ≤
        ‖a‖ ^ (n - kTop) * (n : ℝ) ^ kTop := by
    intro k hk
    have hkTop : k ≤ kTop := by
      rw [Finset.mem_range] at hk
      omega
    have hpowNorm : ‖a‖ ^ (n - k) ≤ ‖a‖ ^ (n - kTop) := by
      exact pow_le_pow_of_le_one (norm_nonneg a) ha1 (by omega)
    have hchoose : (n.choose k : ℝ) ≤ (n : ℝ) ^ k := by
      exact_mod_cast Nat.choose_le_pow n k
    have hpowNat : (n : ℝ) ^ k ≤ (n : ℝ) ^ kTop := by
      by_cases hkTop0 : kTop = 0
      · have hk0 : k = 0 := by omega
        subst k
        simp [hkTop0]
      · have hn1 : 1 ≤ n := by omega
        exact pow_right_mono₀ (by exact_mod_cast hn1) hkTop
    exact mul_le_mul hpowNorm (hchoose.trans hpowNat)
      (Nat.cast_nonneg _) (pow_nonneg (norm_nonneg a) _)
  have hsumBound :
      (∑ k ∈ Finset.range (kTop + 1), ‖a‖ ^ (n - k) * (n.choose k : ℝ)) ≤
        (D : ℝ) * (‖a‖ ^ (n - kTop) * (n : ℝ) ^ kTop) := by
    calc
      (∑ k ∈ Finset.range (kTop + 1), ‖a‖ ^ (n - k) * (n.choose k : ℝ)) ≤
          ∑ _k ∈ Finset.range (kTop + 1),
            ‖a‖ ^ (n - kTop) * (n : ℝ) ^ kTop :=
        Finset.sum_le_sum fun k hk ↦ hterm k hk
      _ = (D : ℝ) * (‖a‖ ^ (n - kTop) * (n : ℝ) ^ kTop) := by
        simp [hD]
  have hpow : ‖a‖ ^ n = ‖a‖ ^ (n - kTop) * ‖a‖ ^ kTop := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  have hfactor : (‖a‖⁻¹) ^ kTop * ‖a‖ ^ n = ‖a‖ ^ (n - kTop) := by
    rw [hpow]
    calc
      (‖a‖⁻¹) ^ kTop * (‖a‖ ^ (n - kTop) * ‖a‖ ^ kTop) =
          ‖a‖ ^ (n - kTop) * ((‖a‖⁻¹) ^ kTop * ‖a‖ ^ kTop) := by ring
      _ = ‖a‖ ^ (n - kTop) := by
        rw [← mul_pow, inv_mul_cancel₀ ha.ne', one_pow, mul_one]
  calc
    ‖jordanBlock D a ^ n‖ ≤
        ∑ k ∈ Finset.range (kTop + 1), ‖a‖ ^ (n - k) * (n.choose k : ℝ) := hsum
    _ ≤ (D : ℝ) * (‖a‖ ^ (n - kTop) * (n : ℝ) ^ kTop) := hsumBound
    _ = (D : ℝ) * (‖a‖⁻¹) ^ kTop * ‖a‖ ^ n * (n : ℝ) ^ kTop := by
      rw [← hfactor]
      ring

/-- Two-sided polynomial-exponential scaling for one positive-modulus Jordan
block.  This is the single-block prerequisite used in Wolf's proof of
Equations (8.106)--(8.107), not the full channel theorem. -/
theorem l2_opNorm_jordanBlock_pow_polynomial_bounds (D : ℕ) [NeZero D]
    (a : ℂ) (n : ℕ) (ha : 0 < ‖a‖) (ha1 : ‖a‖ ≤ 1)
    (hn : D - 1 ≤ n) :
    ((‖a‖ * (D - 1 : ℕ))⁻¹) ^ (D - 1) * ‖a‖ ^ n *
          (n : ℝ) ^ (D - 1) ≤ ‖jordanBlock D a ^ n‖ ∧
      ‖jordanBlock D a ^ n‖ ≤
        (D : ℝ) * (‖a‖⁻¹) ^ (D - 1) * ‖a‖ ^ n *
          (n : ℝ) ^ (D - 1) :=
  ⟨le_l2_opNorm_jordanBlock_pow_polynomial D a n ha hn,
    l2_opNorm_jordanBlock_pow_le_polynomial D a n ha ha1 hn⟩

end Matrix
