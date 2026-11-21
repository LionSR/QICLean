/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Nat.Log

/-!
# A fixed bound for stopped dimension halving

A nonnegative integer sequence halves whenever it is above a threshold
and does not increase below it. An initial ceiling given by a power of two therefore
gives a predetermined number of rounds after which the sequence is below the threshold.
For a chain of L sites of local dimension q, q*L rounds suffice for every
threshold at least two.

This is numerical supporting algebra for the repeated amplification
construction associated with ALVV, arXiv:1602.08828v2,
`sec:merge-process`, lines 711–736, and the proof of `t:alg1`,
lines 1783–1817. It does not supply a random success or viability premise.
-/

namespace Nat

/-- An initial ceiling given by a power of two bounds the number of rounds of a stopped
halving sequence. Below the threshold the sequence may decrease further.
Numerical auxiliary for ALVV, arXiv:1602.08828v2,
`sec:merge-process`, lines 711–736. -/
theorem lt_threshold_of_stopped_halving (a : ℕ → ℕ) (threshold rounds : ℕ)
    (hthreshold : 2 ≤ threshold) (hzero : a 0 ≤ 2 ^ rounds)
    (hstep : ∀ i < rounds,
      a (i + 1) ≤ if threshold ≤ a i then a i / 2 else a i) :
    a rounds < threshold := by
  have hbound : ∀ i ≤ rounds, a i < threshold ∨ a i * 2 ^ i ≤ a 0 := by
    intro i
    induction i with
    | zero =>
        intro _
        exact Or.inr (by simp)
    | succ i ih =>
        intro hi
        have hiR : i < rounds := by omega
        by_cases hactive : threshold ≤ a i
        · have hprev : a i * 2 ^ i ≤ a 0 :=
            (ih (by omega)).resolve_left (Nat.not_lt_of_ge hactive)
          have hhalf : a (i + 1) ≤ a i / 2 := by
            simpa only [ite_eq_left hactive] using hstep i hiR
          have hmul : a (i + 1) * 2 ≤ a i :=
            (Nat.le_div_iff_mul_le Nat.zero_lt_two).mp hhalf
          exact Or.inr (by
            simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
              (Nat.mul_le_mul_right (2 ^ i) hmul).trans hprev)
        · exact Or.inl ((show a (i + 1) ≤ a i from by
            simpa only [ite_eq_right hactive] using hstep i hiR).trans_lt
              (Nat.lt_of_not_ge hactive))
  rcases hbound rounds (Nat.le_refl rounds) with hsmall | hlarge
  · exact hsmall
  · have hpower : 0 < 2 ^ rounds := Nat.pow_pos Nat.zero_lt_two
    by_contra hsmall
    have htwice : 2 * 2 ^ rounds ≤ a rounds * 2 ^ rounds :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- A chain's ambient dimension gives a fixed number of halving rounds
proportional to its length, before any sample is selected. This is a dimension-counting
auxiliary for ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1783–1817;
no probability or algorithmic running-time estimate is asserted. -/
theorem lt_threshold_of_stopped_halving_chain (a : ℕ → ℕ) (threshold q L : ℕ)
    (hthreshold : 2 ≤ threshold) (hzero : a 0 ≤ q ^ L)
    (hstep : ∀ i < q * L,
      a (i + 1) ≤ if threshold ≤ a i then a i / 2 else a i) :
    a (q * L) < threshold := by
  have hdim : q ^ L ≤ 2 ^ (q * L) := by
    simpa only [Nat.pow_mul] using
      Nat.pow_le_pow_left (Nat.le_of_lt (show q < 2 ^ q from Nat.lt_two_pow_self)) L
  exact lt_threshold_of_stopped_halving a threshold (q * L) hthreshold
    (hzero.trans hdim) hstep

end Nat
