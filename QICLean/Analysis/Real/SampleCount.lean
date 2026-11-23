/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Binomial error sums and an explicit sample count

The nonempty subsets of a finite set of positions, weighted by `a ^ |s|`, sum to the binomial
expression `(1 + a) ^ N - 1`. With `a = Q / √k` and the positive integer sample count
`k = ⌈(8 N Q / ε) ^ 2⌉ + 1`, this sum is at most `ε / 4` for `0 < ε ≤ 1`. The count is at most
quadratic in `N`, `Q` and `1 / ε`, so power bounds on these three quantities give a power bound
on the count; the statements on `binomialSampleCount (max 1 N) Q ε` cover an empty set of
positions as well.

The Lean proofs in this file are newly written from the mathematical argument and Mathlib.
No OpenAI Lean source is copied or adapted.

## Main definitions

* `binomialSampleCount`: the sample count `⌈(8 N Q / ε) ^ 2⌉ + 1`.

## Main results

* `Finset.sum_powerset_erase_empty_pow_mul_rpow`: the exact binomial sum.
* `one_add_div_sqrt_binomialSampleCount_pow_sub_one_le`: quarter accuracy of the sample count.
* `Finset.sum_powerset_erase_empty_binomialSampleCount_le`: quarter accuracy of the sample
  count at `max 1 N`.
* `binomialSampleCount_lt_of_power_bounds`: a power bound on the sample count.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), Theorem 5.2, `eq:compression-total-error`,
  `eq:compression-polynomial-bounds` and the sample choice, `04-compression.tex`,
  lines 174–175, 269–277, 364–369 and 540–567.
-/

noncomputable section

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- The nonempty correction subsets have exactly the binomial total cost.
Source: Theorem 5.2, `eq:compression-total-error`, `04-compression.tex:540--551`.
The index set consists of source positions, not monomial labels. -/
theorem Finset.sum_powerset_erase_empty_pow_card (slots : Finset ι) (a : ℝ) :
    (∑ s ∈ slots.powerset.erase ∅, a ^ s.card) = (1 + a) ^ slots.card - 1 := by
  have hsum : (∑ s ∈ slots.powerset, a ^ s.card) = (1 + a) ^ slots.card := by
    simpa [add_comm] using Finset.sum_pow_mul_eq_add_pow a (1 : ℝ) slots
  have herase := Finset.sum_erase_add slots.powerset (fun s ↦ a ^ s.card)
    (Finset.empty_mem_powerset slots)
  simp only [Finset.card_empty, pow_zero] at herase
  linarith

/-- Exact weighted correction sum in the square-root form used for sampling.
Source: Theorem 5.2, `eq:compression-total-error`, `04-compression.tex:540--551`. -/
theorem Finset.sum_powerset_erase_empty_pow_div_sqrt_pow (slots : Finset ι) (Q k : ℝ) :
    (∑ s ∈ slots.powerset.erase ∅, Q ^ s.card / (Real.sqrt k) ^ s.card) =
      (1 + Q / Real.sqrt k) ^ slots.card - 1 := by
  simpa only [div_pow] using Finset.sum_powerset_erase_empty_pow_card slots (Q / Real.sqrt k)

/-- The real-power expression in the paper is the same square-root weight for positive `k`.
Source: Theorem 5.2, `eq:compression-one-choice`, `04-compression.tex:531--545`. -/
theorem Real.rpow_neg_natCast_div_two (k : ℝ) (hk : 0 < k) (n : ℕ) :
    k ^ (-(n : ℝ) / 2) = 1 / (Real.sqrt k) ^ n := by
  have hexp : -(n : ℝ) / 2 = -((1 / 2 : ℝ) * n) := by ring
  rw [hexp, Real.rpow_neg hk.le, Real.rpow_mul_natCast hk.le,
    ← Real.sqrt_eq_rpow, one_div]

/-- The source's real-power correction weights sum to the claimed total error.
Source: Theorem 5.2, `eq:compression-total-error`, `04-compression.tex:540--551`. -/
theorem Finset.sum_powerset_erase_empty_pow_mul_rpow (slots : Finset ι) (Q k : ℝ) (hk : 0 < k) :
    (∑ s ∈ slots.powerset.erase ∅, Q ^ s.card * k ^ (-(s.card : ℝ) / 2)) =
      (1 + Q / Real.sqrt k) ^ slots.card - 1 := by
  simp_rw [Real.rpow_neg_natCast_div_two k hk, ← div_eq_mul_one_div]
  exact Finset.sum_powerset_erase_empty_pow_div_sqrt_pow slots Q k

/-- The binomial sampling bound is controlled by its exponential majorant.
Source: Theorem 5.2, realization paragraph, `04-compression.tex:553--565`. -/
theorem Real.one_add_pow_sub_one_le_exp_sub_one (N : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (1 + a) ^ N - 1 ≤ Real.exp ((N : ℝ) * a) - 1 := by
  have hpow : (1 + a) ^ N ≤ (Real.exp a) ^ N := by
    exact pow_le_pow_left₀ (by positivity)
      (by simpa [add_comm] using Real.add_one_le_exp a) N
  rw [← Real.exp_nat_mul] at hpow
  linarith

/-- The paper's quarter-accuracy exponential bound, for its accuracy range.
Source: Theorem 5.2, realization paragraph, `04-compression.tex:558--565`.
Here `0 < ε ≤ 1` follows from the source's target accuracy `ε = L⁻ᵖ`. -/
theorem Real.exp_div_eight_sub_one_le_div_four (ε : ℝ) (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    Real.exp (ε / 8) - 1 ≤ ε / 4 := by
  have habs : |ε / 8| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hexp := Real.abs_exp_sub_one_le habs
  rw [abs_of_nonneg (by positivity : 0 ≤ ε / 8)] at hexp
  linarith [le_abs_self (Real.exp (ε / 8) - 1)]

/-- The prescribed ratio bounds the total error by a quarter of the accuracy.
Source: Theorem 5.2, `eq:compression-total-error` and sample choice,
`04-compression.tex:546--565`. -/
theorem Real.one_add_pow_sub_one_le_div_four (N : ℕ) (a ε : ℝ) (hN : 0 < N)
    (ha : 0 ≤ a) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hsmall : a ≤ ε / (8 * N)) :
    (1 + a) ^ N - 1 ≤ ε / 4 := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmul : (N : ℝ) * a ≤ ε / 8 := by
    have h := (le_div_iff₀ (by positivity : 0 < (8 : ℝ) * N)).mp hsmall
    nlinarith
  calc
    (1 + a) ^ N - 1 ≤ Real.exp ((N : ℝ) * a) - 1 :=
      Real.one_add_pow_sub_one_le_exp_sub_one N a ha
    _ ≤ Real.exp (ε / 8) - 1 := by gcongr
    _ ≤ ε / 4 := Real.exp_div_eight_sub_one_le_div_four ε hε.le hε₁

/-- A square sample-count lower bound gives the ratio required by the paper.
Source: Theorem 5.2, sample choice, `04-compression.tex:553--558`.
Positive `k` is necessary for the sample average. -/
theorem Real.div_sqrt_le_of_sq_le (N k : ℕ) (Q ε : ℝ) (hN : 0 < N) (hk : 0 < k)
    (hε : 0 < ε) (hcount : (8 * N * Q / ε) ^ 2 ≤ (k : ℝ)) :
    Q / Real.sqrt k ≤ ε / (8 * N) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hsqrt := Real.le_sqrt_of_sq_le hcount
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hkreal)]
  have hmul := (div_le_iff₀ hε).mp hsqrt
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < (8 : ℝ) * N)).mpr
  nlinarith

/-- Any positive integer sample count above the required square gives quarter accuracy.
Source: Theorem 5.2, `eq:compression-total-error` and sample choice,
`04-compression.tex:546--565`. The zero-slot case has exact zero error. -/
theorem Real.one_add_div_sqrt_pow_sub_one_le_div_four (N k : ℕ) (Q ε : ℝ) (hk : 0 < k)
    (hQ : 0 ≤ Q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hcount : (8 * N * Q / ε) ^ 2 ≤ (k : ℝ)) :
    (1 + Q / Real.sqrt k) ^ N - 1 ≤ ε / 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [pow_zero, sub_self]
    positivity
  · exact Real.one_add_pow_sub_one_le_div_four N _ ε hN (by positivity) hε hε₁
      (Real.div_sqrt_le_of_sq_le N k Q ε hN hk hε hcount)

/-- Positive sample count chosen only from the slot count, correction cost and accuracy.
Source: Theorem 5.2, sample choice, `04-compression.tex:553--558`.
Adding one handles `Q = 0` while keeping the same polynomial size bound. -/
def binomialSampleCount (N : ℕ) (Q ε : ℝ) : ℕ := ⌈(8 * N * Q / ε) ^ 2⌉₊ + 1

/-- The explicit integer choice is positive, dominates the required square, and is less than
that square plus two. Source: Theorem 5.2, `04-compression.tex:553--558`. -/
theorem binomialSampleCount_bounds (N : ℕ) (Q ε : ℝ) :
    0 < binomialSampleCount N Q ε ∧
      (8 * N * Q / ε) ^ 2 ≤ (binomialSampleCount N Q ε : ℝ) ∧
      (binomialSampleCount N Q ε : ℝ) < (8 * N * Q / ε) ^ 2 + 2 := by
  dsimp [binomialSampleCount]
  refine ⟨by omega, ?_, ?_⟩
  · push_cast
    exact (Nat.le_ceil _).trans (by linarith)
  · push_cast
    have h := Nat.ceil_lt_add_one (sq_nonneg (8 * N * Q / ε))
    linarith

/-- The explicit positive integer sample count achieves the quarter-error estimate.
Source: Theorem 5.2, `eq:compression-total-error` and sample choice,
`04-compression.tex:546--565`. The zero-slot case requires no sampling estimate. -/
theorem one_add_div_sqrt_binomialSampleCount_pow_sub_one_le (N : ℕ) (Q ε : ℝ) (hQ : 0 ≤ Q)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (1 + Q / Real.sqrt (binomialSampleCount N Q ε)) ^ N - 1 ≤ ε / 4 := by
  obtain ⟨hk, hcount, _⟩ := binomialSampleCount_bounds N Q ε
  exact Real.one_add_div_sqrt_pow_sub_one_le_div_four N _ Q ε hk hQ hε hε₁ hcount

/-! ### The sample count at `max 1 N` -/

/-- The sample count at `max 1 |slots|` makes the weighted sum over the nonempty subsets of
`slots` at most a quarter of the accuracy; with no slots the sum is empty.
Source: Theorem 5.2, `eq:compression-total-error` and sample choice,
`04-compression.tex`, lines 540–558. -/
theorem Finset.sum_powerset_erase_empty_binomialSampleCount_le (slots : Finset ι) (Q ε : ℝ)
    (hQ : 0 ≤ Q) (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (∑ s ∈ slots.powerset.erase ∅,
      Q ^ s.card * (binomialSampleCount (max 1 slots.card) Q ε : ℝ) ^ (-(s.card : ℝ) / 2)) ≤
      ε / 4 := by
  obtain ⟨hk, hcount, _⟩ := binomialSampleCount_bounds (max 1 slots.card) Q ε
  rw [Finset.sum_powerset_erase_empty_pow_mul_rpow slots Q _ (by exact_mod_cast hk)]
  refine Real.one_add_div_sqrt_pow_sub_one_le_div_four _ _ Q ε hk hQ hε hε₁ (le_trans ?_ hcount)
  have hN : (slots.card : ℝ) ≤ ((max 1 slots.card : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_right 1 slots.card
  have h0 : 0 ≤ 8 * (slots.card : ℝ) * Q / ε := by positivity
  have hle : 8 * (slots.card : ℝ) * Q / ε ≤ 8 * ((max 1 slots.card : ℕ) : ℝ) * Q / ε := by
    gcongr
  exact pow_le_pow_left₀ h0 hle 2

/-- Power bounds `N ≤ C_N L ^ n`, `Q ≤ C_Q L ^ q` and `1 / ε ≤ C_ε L ^ p` give the power bound
`(64 C_N² C_Q² C_ε² + 2) L ^ (2 (n + q + p))` on the sample count at `max 1 N`.
Source: Theorem 5.2, `eq:compression-polynomial-bounds`, `04-compression.tex`, lines 174–175,
269–277, 364–369 and 548–558. -/
theorem binomialSampleCount_lt_of_power_bounds (N : ℕ) (Q ε L : ℝ) (C_N C_Q C_ε : ℝ) (n q p : ℕ)
    (hL : 1 ≤ L) (hCN : 1 ≤ C_N) (hCQ : 0 ≤ C_Q) (hQ : 0 ≤ Q) (hε : 0 < ε)
    (hN : (N : ℝ) ≤ C_N * L ^ n) (hQbound : Q ≤ C_Q * L ^ q)
    (hεbound : ε⁻¹ ≤ C_ε * L ^ p) :
    (binomialSampleCount (max 1 N) Q ε : ℝ) <
      (64 * C_N ^ 2 * C_Q ^ 2 * C_ε ^ 2 + 2) * L ^ (2 * (n + q + p)) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hNmax : ((max 1 N : ℕ) : ℝ) ≤ C_N * L ^ n := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (one_le_mul_of_one_le_of_one_le hCN (one_le_pow₀ hL)) hN
  have ht : 8 * ((max 1 N : ℕ) : ℝ) * Q / ε ≤
      (8 * C_N * C_Q * C_ε) * L ^ (n + q + p) := by
    calc
      _ ≤ 8 * (C_N * L ^ n) * (C_Q * L ^ q) * (C_ε * L ^ p) := by
        rw [div_eq_mul_inv]
        gcongr
      _ = _ := by
        simp only [pow_add]
        ring
  have hs : (8 * ((max 1 N : ℕ) : ℝ) * Q / ε) ^ 2 ≤
      (64 * C_N ^ 2 * C_Q ^ 2 * C_ε ^ 2) * L ^ (2 * (n + q + p)) := by
    calc
      _ ≤ ((8 * C_N * C_Q * C_ε) * L ^ (n + q + p)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) ht 2
      _ = _ := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm (n + q + p) 2]
        ring
  have hLp : 1 ≤ L ^ (2 * (n + q + p)) := one_le_pow₀ hL
  have hk := (binomialSampleCount_bounds (max 1 N) Q ε).2.2
  nlinarith

/-- At inverse-power accuracy `ε = L⁻ᵖ` the exponent of the sample count is twice the sum of
the exponents of the number of sources, the cost bound and the accuracy.
Source: Theorem 5.2, `eq:compression-polynomial-bounds`, `04-compression.tex`, lines 548–558. -/
theorem binomialSampleCount_inv_pow_lt (N : ℕ) (Q L C_N C_Q : ℝ) (n q p : ℕ) (hL : 1 ≤ L)
    (hCN : 1 ≤ C_N) (hCQ : 0 ≤ C_Q) (hQ : 0 ≤ Q) (hN : (N : ℝ) ≤ C_N * L ^ n)
    (hQbound : Q ≤ C_Q * L ^ q) :
    (binomialSampleCount (max 1 N) Q (L ^ p)⁻¹ : ℝ) <
      (64 * C_N ^ 2 * C_Q ^ 2 + 2) * L ^ (2 * (n + q + p)) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  simpa only [one_pow, mul_one] using
    binomialSampleCount_lt_of_power_bounds N Q (L ^ p)⁻¹ L C_N C_Q 1
      n q p hL hCN hCQ hQ (by positivity) hN hQbound (by simp)

/-- With the cost `Q = B ^ (4 b) D ^ 4`, power bounds on the number of sources, on the
coefficient bound `B` and on the dimension `D` give a power bound on the sample count at
`max 1 N` and accuracy `L⁻ᵖ`; the exponent depends on the participation bound `b`.
Source: Theorem 5.2, `eq:compression-choice-cost` and `eq:compression-polynomial-bounds`,
`04-compression.tex`, lines 174–175, 269–277, 364–369 and 548–558. -/
theorem binomialSampleCount_lt_of_cost_power_bounds (N b : ℕ) (B D L C_N C_B C_D : ℝ) (n m r p : ℕ)
    (hL : 1 ≤ L) (hCN : 1 ≤ C_N) (hCB : 0 ≤ C_B) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hN : (N : ℝ) ≤ C_N * L ^ n) (hBbound : B ≤ C_B * L ^ m) (hDbound : D ≤ C_D * L ^ r) :
    (binomialSampleCount (max 1 N) (B ^ (4 * b) * D ^ 4) (L ^ p)⁻¹ : ℝ) <
      (64 * C_N ^ 2 * (C_B ^ (4 * b) * C_D ^ 4) ^ 2 + 2) *
        L ^ (2 * (n + 4 * b * m + 4 * r + p)) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hQbound : B ^ (4 * b) * D ^ 4 ≤
      (C_B ^ (4 * b) * C_D ^ 4) * L ^ (4 * b * m + 4 * r) := by
    calc
      _ ≤ (C_B * L ^ m) ^ (4 * b) * (C_D * L ^ r) ^ 4 := by gcongr
      _ = _ := by
        simp only [mul_pow, ← pow_mul]
        rw [Nat.mul_comm m (4 * b), Nat.mul_comm r 4, pow_add]
        ring
  simpa only [Nat.add_assoc] using binomialSampleCount_inv_pow_lt N (B ^ (4 * b) * D ^ 4) L C_N
    (C_B ^ (4 * b) * C_D ^ 4) n (4 * b * m + 4 * r) p hL hCN (by positivity) (by positivity)
    hN hQbound

