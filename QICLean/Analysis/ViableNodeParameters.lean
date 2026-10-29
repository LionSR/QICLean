/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Scalar scales for a powered viable-space step

The exponent is the upper integer logarithm of the desired lower bound on
the powered family parameter. These estimates support the merge and error
reduction steps of ALVV, arXiv:1602.08828v2, Lemma `l:er`, lines 597–622,
and the degenerate-ground-space analysis, lines 1777–1817.
They do not construct a recursively selected family or assert a runtime.
-/

namespace Nat

/-- The actual integer power scale gives a cubic dimension bound after
applying the squared powered family to an input of dimension at most `s`.
Supporting ALVV, arXiv:1602.08828v2, `l:er`, lines 597–622, and the
merge analysis, lines 1777–1817. -/
theorem viable_node_power_bounds {D s : ℕ} (hD : 2 ≤ D) (hs : 1 ≤ s) :
    let k := clog D (D ^ 2 * s)
    2 ≤ k ∧ D ^ 2 * s ≤ D ^ k ∧ D ^ k ≤ D ^ 3 * s ∧
      (D ^ k) ^ 2 * s ≤ D ^ 6 * s ^ 3 := by
  intro k
  have hD1 : 1 < D := hD
  have hthreshold : D ^ 2 ≤ D ^ 2 * s := by simpa using Nat.mul_le_mul_left (D ^ 2) hs
  have hk2 : 2 ≤ k := by
    simpa only [Nat.clog_pow D 2 hD1] using Nat.clog_mono_right D hthreshold
  have hlower : D ^ 2 * s ≤ D ^ k := Nat.le_pow_clog hD1 _
  have hprev : D ^ k.pred < D ^ 2 * s :=
    Nat.pow_pred_clog_lt_self hD1 (by nlinarith only [hD, hs])
  have hupper : D ^ k ≤ D ^ 3 * s := by
    calc
      D ^ k = D * D ^ k.pred := by
        rw [← pow_succ', Nat.succ_pred_eq_of_pos (by omega : 0 < k)]
      _ ≤ D * (D ^ 2 * s) := Nat.mul_le_mul_left D hprev.le
      _ = D ^ 3 * s := by ring
  refine ⟨hk2, hlower, hupper, ?_⟩
  calc
    (D ^ k) ^ 2 * s ≤ (D ^ 3 * s) ^ 2 * s :=
      Nat.mul_le_mul_right s (Nat.pow_le_pow_left hupper 2)
    _ = D ^ 6 * s ^ 3 := by ring

/-- The truncated sample retains the ratio required by a polynomial bound
on the actual merged dimension. Supporting ALVV, arXiv:1602.08828v2,
Lemma `l:rs`, lines 530–558, and the merge analysis, lines 1777–1817. -/
theorem viable_node_sample_ratio {D s Q : ℕ} (hD : 2 ≤ D) (hs : 1 ≤ s)
    (hQ : Q ≤ D ^ 12 * s ^ 6) :
    Q ≤ D ^ 12 * s ^ 5 * min s Q := by
  by_cases hfull : Q ≤ s
  · rw [Nat.min_eq_right hfull]
    have hA : 1 ≤ D ^ 12 * s ^ 5 := by
      simpa only [one_mul] using Nat.mul_le_mul
        (Nat.one_le_pow 12 D (by omega)) (Nat.one_le_pow 5 s hs)
    simpa only [one_mul] using Nat.mul_le_mul_right Q hA
  · rw [Nat.min_eq_left (by omega : s ≤ Q)]
    calc
      Q ≤ D ^ 12 * s ^ 6 := hQ
      _ = D ^ 12 * s ^ 5 * s := by ring

end Nat

namespace Real

/-- The genuine powered family satisfies a strict tradeoff whenever its
base tradeoff is at most a number strictly between zero and one. The upper
integer logarithm forces at least two powers. Supporting ALVV,
arXiv:1602.08828v2, `l:er`, lines 597–622, and the merge analysis,
lines 1777–1817. -/
theorem viable_node_power_tradeoff_lt {D s : ℕ} (hD : 2 ≤ D) (hs : 1 ≤ s)
    {Delta budget : ℝ} (hDelta : 0 ≤ Delta) (hbudget : 0 < budget)
    (hbudget1 : budget < 1) (hbase : (D : ℝ) ^ 12 * Delta ≤ budget) :
    let k := Nat.clog D (D ^ 2 * s)
    ((D ^ k : ℕ) : ℝ) ^ 12 * Delta ^ k < budget := by
  intro k
  have hk2 : 2 ≤ k := (Nat.viable_node_power_bounds hD hs).1
  have hidentity : ((D ^ k : ℕ) : ℝ) ^ 12 * Delta ^ k =
      ((D : ℝ) ^ 12 * Delta) ^ k := by
    simp only [Nat.cast_pow, mul_pow, ← pow_mul, Nat.mul_comm k 12]
  rw [hidentity]
  exact (pow_le_pow_left₀ (by positivity) hbase k).trans_lt
    (pow_lt_self_of_lt_one₀ hbudget hbudget1 (by omega : 1 < k))

/-- The actual sample-or-full overlap has a uniform polynomial lower bound.
Supporting ALVV, arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558,
and the merge analysis, lines 1777–1817. -/
theorem viable_node_sample_overlap_lower {D s Q : ℕ} (hD : 2 ≤ D) (hs : 1 ≤ s)
    (hQ0 : 0 < Q) (hQ : Q ≤ D ^ 12 * s ^ 6) {delta : ℝ} (hdelta : delta ≤ 1 / 4) :
    3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)) ≤
      (1 - delta) * (min s Q : ℕ) / (8 * Q) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hQ0R : (0 : ℝ) < Q := by exact_mod_cast hQ0
  let A : ℝ := (D : ℝ) ^ 12 * (s : ℝ) ^ 5
  have hA : 0 < A := by dsimp only [A]; positivity
  have hratio : (Q : ℝ) ≤ A * (min s Q : ℕ) := by
    dsimp only [A]
    exact_mod_cast Nat.viable_node_sample_ratio hD hs hQ
  apply (div_le_div_iff₀ (by positivity : 0 < 32 * A) (by positivity : 0 < 8 * (Q : ℝ))).2
  have hdelta' : 3 / 4 ≤ 1 - delta := by linarith only [hdelta]
  have hprod := mul_le_mul_of_nonneg_right hdelta'
    (show 0 ≤ A * (min s Q : ℕ) by positivity)
  nlinarith only [hratio, hprod]

/-- The powered suppression compensates the actual sample-or-full overlap
at the stable polynomial dimension scale. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:er`, lines 597–622, and the merge analysis,
lines 1777–1817. No sampling event or recursively selected family is assumed. -/
theorem viable_node_power_error_bound {D s Q : ℕ} (hD : 2 ≤ D) (hs : 1 ≤ s)
    (hQ0 : 0 < Q) (hQ : Q ≤ D ^ 12 * s ^ 6) {delta Delta budget : ℝ}
    (hdelta : delta ≤ 1 / 4) (hDelta : 0 ≤ Delta) (hbudget : 0 < budget)
    (hbudget1 : budget < 1) (hbase : (D : ℝ) ^ 12 * Delta ≤ budget) :
    let k := Nat.clog D (D ^ 2 * s)
    let c := (1 - delta) * (min s Q : ℕ) / (8 * Q)
    0 < c ∧ Delta ^ k / c ^ 2 ≤ (1024 / 9 : ℝ) * budget / (s : ℝ) ^ 2 := by
  intro k c
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  let A : ℝ := (D : ℝ) ^ 12 * (s : ℝ) ^ 5
  let B : ℝ := (D : ℝ) ^ 24 * (s : ℝ) ^ 12
  have hA0 : 0 < A := by dsimp only [A]; positivity
  have hB0 : 0 < B := by dsimp only [B]; positivity
  have hlow0 : 0 < 3 / (32 * A) := by positivity
  have hclower : 3 / (32 * A) ≤ c := viable_node_sample_overlap_lower hD hs hQ0 hQ hdelta
  have hc0 : 0 < c := hlow0.trans_le hclower
  refine ⟨hc0, ?_⟩
  have hpower0 : 0 ≤ Delta ^ k := pow_nonneg hDelta k
  have htrade : ((D ^ k : ℕ) : ℝ) ^ 12 * Delta ^ k < budget :=
    viable_node_power_tradeoff_lt hD hs hDelta hbudget hbudget1 hbase
  have hDlower : ((D : ℝ) ^ 2 * (s : ℝ)) ^ 12 ≤ ((D ^ k : ℕ) : ℝ) ^ 12 := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast (Nat.viable_node_power_bounds hD hs).2.1
  have hDeltaBound : Delta ^ k ≤ budget / B := by
    apply (le_div_iff₀ hB0).mpr
    calc
      Delta ^ k * B = ((D : ℝ) ^ 2 * (s : ℝ)) ^ 12 * Delta ^ k := by
        dsimp only [B]
        ring
      _ ≤ ((D ^ k : ℕ) : ℝ) ^ 12 * Delta ^ k :=
        mul_le_mul_of_nonneg_right hDlower hpower0
      _ ≤ budget := htrade.le
  calc
    Delta ^ k / c ^ 2 ≤ (budget / B) / c ^ 2 :=
      div_le_div_of_nonneg_right hDeltaBound (sq_nonneg _)
    _ ≤ (budget / B) / (3 / (32 * A)) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlow0)
        (pow_le_pow_left₀ hlow0.le hclower 2)
    _ = (1024 / 9 : ℝ) * budget / (s : ℝ) ^ 2 := by
      dsimp only [A, B]
      field_simp
      ring

end Real
