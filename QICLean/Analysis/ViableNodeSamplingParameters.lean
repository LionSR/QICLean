/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# One sampling size for all polynomially bounded parent spaces

These scalar estimates choose the sampling size before every input space.
They support the degenerate-ground-space merge analysis of ALVV,
arXiv:1602.08828v2, lines 1777–1817, with the genuine polynomial word-family
profile and corrected complex-sphere count. They do not assert adaptive
measurability or a probability bound for an entire recursively sampled tree.

**Local fix (complex sphere net count):** The failure estimate retains the
corrected exponent and net scale documented in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

namespace Real

/-- An explicit ceiling scale has a logarithmic upper bound, uniformly in
all subsequently chosen parent spaces. This is an auxiliary estimate for
ALVV, arXiv:1602.08828v2, merge analysis, lines 1777–1817; its numerical
constant is not the printed parameter prescription. -/
theorem viable_node_sample_size_log_bound {r : ℕ} {A : ℝ}
    (hr : 1 ≤ r) (hA : 1 ≤ A) (hlogr : log (r : ℝ) ≤ A - 1) :
    let s := Nat.ceil (4096 * (r : ℝ) * A)
    1 ≤ s ∧ 4096 * (r : ℝ) * A ≤ s ∧ (s : ℝ) ≤ 4097 * (r : ℝ) * A ∧
      log (s : ℝ) ≤ 13 * A := by
  intro s
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith only [hrR]
  have hA0 : 0 < A := by linarith only [hA]
  have hrA : 1 ≤ (r : ℝ) * A := one_le_mul_of_one_le_of_one_le hrR hA
  have hs : 1 ≤ s := Nat.one_le_ceil_iff.mpr (by positivity)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hlower : 4096 * (r : ℝ) * A ≤ s := Nat.le_ceil _
  have hupper : (s : ℝ) ≤ 4097 * (r : ℝ) * A := by
    have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4096 * (r : ℝ) * A)).le
    nlinarith only [hceil, hrA]
  refine ⟨hs, hlower, hupper, ?_⟩
  have hlog4097 : log (4097 : ℝ) ≤ 13 := by
    calc
      log (4097 : ℝ) ≤ log ((2 : ℝ) ^ 13) := log_le_log (by norm_num) (by norm_num)
      _ = 13 * log 2 := log_pow 2 13
      _ ≤ 13 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogs := log_le_log hs0 hupper
  rw [log_mul (by positivity) hA0.ne', log_mul (by norm_num) hr0.ne'] at hlogs
  have hlogA := log_le_sub_one_of_pos hA0
  linarith only [hlogs, hlog4097, hlogr, hlogA, hA]

/-- The corrected fixed-input failure estimate admits a common logarithmic
majorant at the cubic dimension scale. Supporting ALVV,
arXiv:1602.08828v2, merge analysis, lines 1777–1817, with the corrected
complex-sphere count rather than the printed exponent. -/
theorem viable_node_sampling_failure_le_exp {D r s Q : ℕ}
    (hD : 2 ≤ D) (hr : 1 ≤ r) (hs : 1 ≤ s) (hQ : 1 ≤ Q)
    (hdim : Q ≤ D ^ 12 * s ^ 6) :
    (1 + 2 / sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^ (2 * r) * Q *
        exp (-(s / 16 : ℝ)) ≤
      exp (32 * r * log (D : ℝ) + 12 * r * log (s : ℝ) - s / 16) := by
  have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hD0 : (0 : ℝ) < D := by linarith only [hDR]
  have hr0 : (0 : ℝ) < r := by linarith only [hrR]
  have hs0 : (0 : ℝ) < s := by linarith only [hsR]
  have hQ0 : (0 : ℝ) < Q := by linarith only [hQR]
  let x : ℝ := (1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q)
  let base := 1 + 2 / sqrt x
  have hx : 0 < x := by dsimp only [x]; positivity
  have hroot : 0 < sqrt x := sqrt_pos.mpr hx
  have hbase : 0 < base := by dsimp only [base]; positivity
  have hprod : x * Q = (3 / 32 : ℝ) * s := by
    dsimp only [x]
    field_simp
    ring
  have hrootprod : (1 / 4 : ℝ) ≤ sqrt x * sqrt (Q : ℝ) := by
    rw [← sqrt_mul hx.le, hprod]
    exact le_sqrt_of_sq_le (by nlinarith only [hsR])
  have hratio : 2 / sqrt x ≤ 8 * sqrt (Q : ℝ) := by
    apply (div_le_iff₀ hroot).mpr
    nlinarith only [hrootprod]
  have hrootQ : 1 ≤ sqrt (Q : ℝ) := one_le_sqrt.mpr hQR
  have hbaseBound : base ≤ 16 * sqrt (Q : ℝ) := by
    dsimp only [base]
    linarith only [hratio, hrootQ]
  have hlog16 : log (16 : ℝ) = 4 * log 2 := by
    calc
      log (16 : ℝ) = log ((2 : ℝ) ^ 4) := by norm_num
      _ = 4 * log 2 := log_pow 2 4
  have hlogBase : log base ≤ 4 * log 2 + log (Q : ℝ) / 2 := by
    have hb := log_le_log hbase hbaseBound
    rwa [log_mul (by norm_num) (sqrt_pos.mpr hQ0).ne', hlog16, log_sqrt hQ0.le] at hb
  have hdimR : (Q : ℝ) ≤ (D : ℝ) ^ 12 * (s : ℝ) ^ 6 := by exact_mod_cast hdim
  have hlogQ : log (Q : ℝ) ≤ 12 * log (D : ℝ) + 6 * log (s : ℝ) := by
    have hb := log_le_log hQ0 hdimR
    simpa only [log_mul (pow_ne_zero _ hD0.ne') (pow_ne_zero _ hs0.ne'),
      log_pow, Nat.cast_ofNat] using hb
  have hlogQ0 : 0 ≤ log (Q : ℝ) := log_nonneg hQR
  have hlog2D : log 2 ≤ log (D : ℝ) := log_le_log (by norm_num) hDR
  have hlogPoly : (2 * (r : ℝ)) * log base + log (Q : ℝ) ≤
      32 * r * log (D : ℝ) + 12 * r * log (s : ℝ) := by
    calc
      (2 * (r : ℝ)) * log base + log (Q : ℝ) ≤
          (2 * r) * (4 * log 2 + log (Q : ℝ) / 2) + log (Q : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hlogBase
          (by positivity : 0 ≤ 2 * (r : ℝ))) (le_refl (log (Q : ℝ)))
      _ = 8 * r * log 2 + ((r : ℝ) + 1) * log (Q : ℝ) := by ring
      _ ≤ 8 * r * log (D : ℝ) + (2 * r) * log (Q : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hlog2D
          (by positivity : 0 ≤ 8 * (r : ℝ)))
          (mul_le_mul_of_nonneg_right (by linarith only [hrR]) hlogQ0)
      _ ≤ 32 * r * log (D : ℝ) + 12 * r * log (s : ℝ) := by
        have hb := mul_le_mul_of_nonneg_left hlogQ (by positivity : 0 ≤ 2 * (r : ℝ))
        linarith only [hb]
  change base ^ (2 * r) * (Q : ℝ) * exp (-(s / 16 : ℝ)) ≤ _
  apply (log_le_iff_le_exp (by positivity : 0 < base ^ (2 * r) * (Q : ℝ) *
    exp (-(s / 16 : ℝ)))).mp
  rw [log_mul (mul_pos (pow_pos hbase _) hQ0).ne' (exp_ne_zero _),
    log_mul (pow_ne_zero _ hbase.ne') hQ0.ne', log_pow, log_exp]
  push_cast
  linarith only [hlogPoly]

/-- One explicit sampling size bounds the corrected failure probability
for every parent dimension at the cubic profile. The size precedes that
dimension. Supporting ALVV, arXiv:1602.08828v2, merge analysis,
lines 1777–1817. This is a fixed-input bound, not an adaptive-tree theorem. -/
theorem viable_node_uniform_sampling_size {D r : ℕ} (hD : 2 ≤ D) (hr : 1 ≤ r)
    {beta : ℝ} (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) :
    let A := 1 + log (r : ℝ) + log (D : ℝ) + log (1 / beta)
    let s := Nat.ceil (4096 * (r : ℝ) * A)
    1 ≤ s ∧ (s : ℝ) ≤ 4097 * (r : ℝ) * A ∧ exp (-(s / 64 : ℝ)) ≤ beta ∧
      ∀ Q : ℕ, Q ≤ D ^ 12 * s ^ 6 →
        (if Q ≤ s then 0 else
          (1 + 2 / sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * Q))) ^ (2 * r) * Q *
            exp (-(s / 16 : ℝ))) ≤ exp (-(s / 64 : ℝ)) := by
  intro A s
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
  have hr0 : (0 : ℝ) < r := by linarith only [hrR]
  have hlogr : 0 ≤ log (r : ℝ) := log_nonneg hrR
  have hlogD : 0 ≤ log (D : ℝ) := log_nonneg hDR
  have hlogbeta : 0 ≤ log (1 / beta) := by
    apply log_nonneg
    apply (le_div_iff₀ hbeta).mpr
    simpa only [one_mul] using hbeta1
  have hA : 1 ≤ A := by dsimp only [A]; linarith only [hlogr, hlogD, hlogbeta]
  have hlogrA : log (r : ℝ) ≤ A - 1 := by
    dsimp only [A]
    linarith only [hlogD, hlogbeta]
  obtain ⟨hs, hlower, hupper, hlogs⟩ := viable_node_sample_size_log_bound hr hA hlogrA
  have hDleA : log (D : ℝ) ≤ A := by
    dsimp only [A]
    linarith only [hlogr, hlogbeta]
  have hbetaLeA : log (1 / beta) ≤ A := by
    dsimp only [A]
    linarith only [hlogr, hlogD]
  have hAr : A ≤ (r : ℝ) * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hrR (by linarith only [hA])
  have htail : exp (-(s / 64 : ℝ)) ≤ beta := by
    calc
      exp (-(s / 64 : ℝ)) ≤ exp (-log (1 / beta)) := by
        apply exp_le_exp.mpr
        linarith only [hlower, hAr, hbetaLeA, hA]
      _ = beta := by rw [one_div, log_inv, neg_neg, exp_log hbeta]
  refine ⟨hs, hupper, htail, ?_⟩
  intro Q hdim
  by_cases hfull : Q ≤ s
  · simp only [ite_eq_left hfull]
    exact (exp_pos _).le
  · rw [ite_eq_right hfull]
    have hQ : 1 ≤ Q := by omega
    apply (viable_node_sampling_failure_le_exp hD hr hs hQ hdim).trans
    apply exp_le_exp.mpr
    have hlogDscale := mul_le_mul_of_nonneg_left hDleA
      (by positivity : 0 ≤ 32 * (r : ℝ))
    have hlogsscale := mul_le_mul_of_nonneg_left hlogs
      (by positivity : 0 ≤ 12 * (r : ℝ))
    nlinarith only [hlower, hlogDscale, hlogsscale]

end Real
