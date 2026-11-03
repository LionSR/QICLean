/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.BootstrapFailureParameters
import Mathlib.Basic.ENNReal.Real

/-!
# Uniform scalar schedules for finite interval resampling

At fixed local dimension and family parameter, a threshold coefficient is chosen
before the chain length, target dimension and sampling carriers. Linear stopping
rounds and a quadratic common count then have one inverse-square total failure
budget, including the empty and one-site chains. These are numerical auxiliaries
to ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817; they assert neither
sampling success nor a running-time estimate.

**Local fix (complex sphere net count):** The threshold uses the corrected
bootstrap failure from `docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
It is not asserted to be the printed logarithmic threshold.
-/

open scoped ENNReal

namespace Real

/-- With `q*L` rounds and per-round coefficient `1/q`, the total count of
at most `L-1` parents has an inverse-square failure budget. The endpoints
`L=0,1` are included. Numerical auxiliary for ALVV,
arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
theorem interval_sampling_failure_budget (q L : ℕ) (hq : 0 < q) :
    ((L - 1 : ℕ) : ℝ) * ((q * L : ℕ) : ℝ) *
      ((1 / (q : ℝ)) / ((L : ℝ) + 2) ^ 4) ≤ 1 / ((L : ℝ) + 1) ^ 2 := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hsub : ((L - 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.sub_le L 1
  calc
    _ = ((L - 1 : ℕ) : ℝ) * (L : ℝ) / ((L : ℝ) + 2) ^ 4 := by
      push_cast
      field_simp
    _ ≤ (L : ℝ) ^ 2 / ((L : ℝ) + 2) ^ 4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith only [hsub, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < ((L : ℝ) + 2) ^ 4)
        (by positivity : (0 : ℝ) < ((L : ℝ) + 1) ^ 2)).mpr
      nlinarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L),
        sq_nonneg (L : ℝ), pow_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L) 3]

end Real

namespace ENNReal

/-- The inverse-square resampling budget in the extended nonnegative reals,
ready for a union bound over at most `L-1` parents and `q*L` rounds.
Numerical auxiliary for ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
theorem interval_sampling_failure_budget (q L : ℕ) (hq : 0 < q) :
    ((L - 1 : ℕ) : ℝ≥0∞) * ((q * L : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal ((1 / (q : ℝ)) / ((L : ℝ) + 2) ^ 4) ≤
        ENNReal.ofReal (1 / ((L : ℝ) + 1) ^ 2) := by
  have h := ENNReal.ofReal_le_ofReal (Real.interval_sampling_failure_budget q L hq)
  rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg (L - 1))
    (Nat.cast_nonneg (q * L))), ENNReal.ofReal_mul (Nat.cast_nonneg (L - 1)),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast] at h
  exact h

end ENNReal

namespace Submodule

/-- One threshold coefficient and natural common-count coefficient precede
all lengths and target dimensions. The stopping and failure budgets are
proved for the same scalar schedule; no sampling carrier or success event
is supplied. Numerical auxiliary for ALVV, arXiv:1602.08828v2,
lines 749–755 and 1777–1817. -/
theorem exists_uniform_interval_sampling_schedule
    (q D width : ℕ) (hq : 2 ≤ q) (hD : 2 ≤ D) :
    ∃ K C : ℕ, 1 ≤ K ∧ 1 ≤ C ∧ C = q ^ width + 4 * D ^ 2 * K ∧
      ∀ L r : ℕ,
      let threshold := K * (r + 1) * (L + 2) ^ 2
      let rounds := q * L
      let count := max (q ^ width) (D ^ 2 * threshold)
      2 ≤ threshold ∧ 4 * D ^ 2 ≤ threshold ∧
      (∀ Q : ℕ, threshold ≤ Q →
        bootstrapFailure D Q r ≤ (1 / (q : ℝ)) / ((L : ℝ) + 2) ^ 4) ∧
      (∀ s : ℕ, s ≤ L → q ^ s ≤ 2 ^ rounds) ∧
      count ≤ C * ((L + 1) * (r + 1)) ^ 2 ∧
      ((L - 1 : ℕ) : ℝ≥0∞) * (rounds : ℝ≥0∞) *
        ENNReal.ofReal ((1 / (q : ℝ)) / ((L : ℝ) + 2) ^ 4) ≤
          ENNReal.ofReal (1 / ((L : ℝ) + 1) ^ 2) := by
  obtain ⟨K, hK, hfailure⟩ := exists_bootstrapFailure_polynomial_threshold
    D 4 hD (1 / (q : ℝ)) (by positivity)
  let C := q ^ width + 4 * D ^ 2 * K
  have hC : 1 ≤ C := (one_le_pow₀ (by omega : 1 ≤ q)).trans
    (Nat.le_add_right (q ^ width) (4 * D ^ 2 * K))
  refine ⟨K, C, hK, hC, rfl, ?_⟩
  intro L r threshold rounds count
  have hthreshold : 4 * D ^ 2 ≤ threshold := (hfailure r L threshold le_rfl).1
  have hDsq : 4 ≤ D ^ 2 := by nlinarith only [hD]
  refine ⟨by omega, hthreshold, ?_, ?_, ?_,
    ENNReal.interval_sampling_failure_budget q L (by omega)⟩
  · intro Q hQ
    exact (hfailure r L Q hQ).2
  · intro s hs
    calc
      q ^ s ≤ q ^ L := Nat.pow_le_pow_right (by omega) hs
      _ ≤ 2 ^ rounds := by
        simpa only [rounds, Nat.pow_mul] using
          Nat.pow_le_pow_left (Nat.le_of_lt (show q < 2 ^ q from Nat.lt_two_pow_self)) L
  · apply max_le
    · exact (Nat.le_add_right (q ^ width) (4 * D ^ 2 * K)).trans
        (Nat.le_mul_of_pos_right C (by positivity))
    · calc
        D ^ 2 * threshold = D ^ 2 * K * (r + 1) * (L + 2) ^ 2 := by
          dsimp only [threshold]
          ring
        _ ≤ D ^ 2 * K * (r + 1) ^ 2 * (2 * (L + 1)) ^ 2 := by
          gcongr
          · nlinarith only [Nat.zero_le r]
          · omega
        _ = (4 * D ^ 2 * K) * ((L + 1) * (r + 1)) ^ 2 := by ring
        _ ≤ C * ((L + 1) * (r + 1)) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.le_add_left (4 * D ^ 2 * K) (q ^ width))

end Submodule
