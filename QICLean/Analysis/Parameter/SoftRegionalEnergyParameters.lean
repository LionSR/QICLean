/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Explicit parameters for a regional soft-energy estimate

The soft threshold 768, order twelve and tail cutoff 384 give a residual
smaller than one sixteenth. The resulting norm bound is dominated by the
existing improving-family count. Its prescribed comparison accuracy and
one-word loss then satisfy both regional-energy precision requirements.

These are scalar auxiliaries to ALVV, arXiv:1602.08828v2,
`def:soft-trunc`, lines 1178–1185, and the energy-estimation argument in the
proof of `t:alg1`, line 1807. They concern a separate soft regional energy
operator used with the corrected hard improving family. They do not
identify that family with the literal soft `Generate` construction in
Figure `fig:generate`, lines 1348–1361, or assert a running time.
-/

namespace Real

/-- A fixed soft threshold, order and tail cutoff give the residual
required by the regional-energy estimate. Scalar auxiliary to ALVV,
arXiv:1602.08828v2, `def:soft-trunc`, lines 1178–1185, and the
energy-estimation argument at line 1807. -/
theorem soft_regional_fixed_residual_lt :
    0 ≤ 32 * exp (-(((384 : ℝ) - 48) / 8)) +
      (768 / (12 : ℝ)) * (384 / (768 : ℝ)) ^ 12 ∧
    32 * exp (-(((384 : ℝ) - 48) / 8)) +
      (768 / (12 : ℝ)) * (384 / (768 : ℝ)) ^ 12 < 1 / 16 := by
  norm_num
  have hExp : (3375 : ℝ) ≤ exp 42 := by
    calc
      (3375 : ℝ) = 15 ^ 3 := by norm_num
      _ ≤ exp 14 ^ 3 := pow_le_pow_left₀ (by norm_num)
        (by linarith only [add_one_le_exp 14]) 3
      _ = exp 42 := by rw [← exp_nat_mul]; norm_num
  have hInv : exp (-42) ≤ 1 / 3375 := by
    simpa only [exp_neg, one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3375) hExp
  exact ⟨by positivity, by linarith only [hInv]⟩

/-- The actual count dominates the norm of the fixed-parameter soft
regional operator. The lower bound on the count follows from the usual
count formula with count base at least fifty. Scalar auxiliary to ALVV,
arXiv:1602.08828v2, `eq:gapless-D-def`, and line 1807. -/
theorem soft_regional_fixed_norm_bound (ell D : ℕ)
    (hell : 21 ≤ ell) (hD : 50 * ell ^ 2 ≤ D) :
    let A := 768 * (1 + log (12 : ℝ)) + 4 * (ell : ℝ) + 14
    0 ≤ A ∧ A + 1 ≤ (D : ℝ) := by
  intro A
  have hbounds : (21 : ℝ) ≤ ell ∧ 50 * (ell : ℝ) ^ 2 ≤ D := by
    exact_mod_cast And.intro hell hD
  have hlog0 : 0 ≤ log (12 : ℝ) := log_nonneg (by norm_num)
  refine ⟨by dsimp only [A]; positivity, ?_⟩
  dsimp only [A]
  nlinarith only [hbounds.1, hbounds.2, sq_nonneg ((ell : ℝ) - 21),
    log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12)]

/-- The prescribed target accuracy and the literal one-word viability
loss satisfy both regional-energy requirements at the same count.
Scalar auxiliary to ALVV, arXiv:1602.08828v2, Lemma `l:er`,
lines 597–622, the interleaved parameters at lines 1797–1805,
and the energy-estimation argument at line 1807. -/
theorem soft_regional_filter_precision_bounds (D s : ℕ)
    (hD : 2 ≤ D) (hs : 1 ≤ s) :
    let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
    let tau := a ^ 2 / 1048576
    let Delta := 1 / (200000 * (D : ℝ) ^ 12)
    0 < tau ∧ tau ≤ 1 / (1024 * ((D : ℝ) + 1)) ∧
      0 < Delta / (1 - (1 / 4 : ℝ)) ^ 2 ∧
      Delta / (1 - (1 / 4 : ℝ)) ^ 2 ≤ 1 / (100 * ((D : ℝ) + 1)) := by
  intro a tau Delta
  have hbase : (2 : ℝ) ≤ D ∧ (1 : ℝ) ≤ s := by
    exact_mod_cast And.intro hD hs
  rcases hbase with ⟨hDR, hsR⟩
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by norm_num) hDR
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le (by norm_num) hsR
  have hDpow : (D : ℝ) ≤ (D : ℝ) ^ 12 :=
    le_self_pow₀ (by linarith only [hDR]) (by norm_num : 12 ≠ 0)
  have hpow : (D : ℝ) ≤ (D : ℝ) ^ 12 * (s : ℝ) ^ 5 :=
    hDpow.trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hsR))
  have ha : a ≤ 3 / (32 * (D : ℝ)) := by
    dsimp only [a]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith only [hpow])
  have hsmall : (3 / (32 * (D : ℝ))) ^ 2 / 1048576 ≤
      1 / (1024 * ((D : ℝ) + 1)) := by
    field_simp
    nlinarith only [hDR, sq_nonneg ((D : ℝ) - 1)]
  have hword : Delta / (1 - (1 / 4 : ℝ)) ^ 2 ≤
      1 / (100 * ((D : ℝ) + 1)) := by
    dsimp only [Delta]
    field_simp
    nlinarith only [hDR, hDpow]
  have ha0 : 0 < a := by dsimp only [a]; positivity
  refine ⟨by dsimp only [tau]; positivity, ?_,
    by dsimp only [Delta]; norm_num; positivity, hword⟩
  exact (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ ha0.le ha 2) (by norm_num)).trans hsmall

end Real
