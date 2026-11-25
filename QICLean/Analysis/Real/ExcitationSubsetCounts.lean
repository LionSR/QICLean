/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Binary-entropy bounds for excitation subsets

For `0 ≤ p ≤ 1 / 2`, the binomial coefficient at any `r ≤ p * k` is bounded by
`exp (k * Real.binEntropy p)`. Summing over admissible cardinalities gives at most
`(k + 1) * exp (k * Real.binEntropy p)` subsets of a set with `k` elements.
The zero-copy and zero-fraction cases are included.

These are the scalar counting estimates used before `comparator:inverse-compression`
in OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, Section 7, lines 577–590 of `build/sections/07-comparators.tex`.
The parameter range `0 < τ < 1/2` is specified there at line 154; the present
bounds also include its endpoints.

The mathematical source is pinned to `openai/math` commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open scoped BigOperators

namespace Real

private theorem binomial_term_le_one {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {k r : ℕ} (hr : r ≤ k) :
    p ^ r * (1 - p) ^ (k - r) * (k.choose r : ℝ) ≤ 1 := by
  have h := Finset.single_le_sum (s := Finset.range (k + 1))
    (f := fun j => p ^ j * (1 - p) ^ (k - j) * (k.choose j : ℝ))
    (fun j _ => mul_nonneg (mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _))
      (Nat.cast_nonneg _)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  simpa only [← add_pow, show p + (1 - p) = 1 by ring, one_pow] using h

private theorem log_choose_le_mul_binEntropy_of_pos {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1 / 2)
    {k r : ℕ} (hr : (r : ℝ) ≤ p * k) :
    log (k.choose r : ℝ) ≤ k * binEntropy p := by
  have hrk : r ≤ k := by
    exact_mod_cast (hr.trans (show p * (k : ℝ) ≤ k by
      nlinarith [show (0 : ℝ) ≤ k by positivity]))
  have hterm := binomial_term_le_one hp.le (show p ≤ 1 by linarith) hrk
  have hq : 0 < 1 - p := by linarith
  have hc : (0 : ℝ) < k.choose r := by exact_mod_cast Nat.choose_pos hrk
  have hlog := log_le_log (mul_pos (mul_pos (pow_pos hp _) (pow_pos hq _)) hc) hterm
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_pow, log_pow, log_one, Nat.cast_sub hrk] at hlog
  have hmul := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hr)
    (sub_nonpos.mpr (log_le_log hp (show p ≤ 1 - p by linarith)))
  simp only [binEntropy, log_inv]
  nlinarith

/-- The logarithm of an admissible binomial coefficient is bounded by binary entropy.

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 7, `07-comparators.tex`, lines 577–578 (before `comparator:inverse-compression`).
Original proof of `Real.log_choose_le_mul_binEntropy`; no upstream Lean proof text reused.
-/
theorem log_choose_le_mul_binEntropy {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    {k r : ℕ} (hr : (r : ℝ) ≤ p * k) :
    log (k.choose r : ℝ) ≤ k * binEntropy p := by
  rcases eq_or_lt_of_le hp with hp | hp
  · have hr0 : r = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact_mod_cast (show (r : ℝ) ≤ 0 by simpa [← hp] using hr)
    simp [← hp, hr0]
  · exact log_choose_le_mul_binEntropy_of_pos hp hp1 hr

/-- Exponential form of the binary-entropy bound on an admissible binomial coefficient.

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 7, `07-comparators.tex`, lines 577–578 (before `comparator:inverse-compression`).
Original proof of `Real.choose_le_exp_mul_binEntropy`; no upstream Lean proof text reused.
-/
theorem choose_le_exp_mul_binEntropy {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    {k r : ℕ} (hr : (r : ℝ) ≤ p * k) :
    (k.choose r : ℝ) ≤ exp (k * binEntropy p) := by
  exact (le_exp_log _).trans (exp_le_exp.mpr (log_choose_le_mul_binEntropy hp hp1 hr))

/-- The sum of binomial coefficients over admissible excitation counts is bounded by
`(k + 1) * exp (k * binEntropy p)`.

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 7, `07-comparators.tex`, lines 577–590 (before `comparator:inverse-compression`).
Original proof of `Real.sum_choose_le_mul_exp_binEntropy`; no upstream Lean proof text reused.
-/
theorem sum_choose_le_mul_exp_binEntropy {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (k : ℕ) :
    (∑ r ∈ (Finset.range (k + 1)).filter (fun r : ℕ => (r : ℝ) ≤ p * k),
      (k.choose r : ℝ)) ≤ ((k : ℝ) + 1) * exp (k * binEntropy p) := by
  have h := Finset.sum_le_sum (s := (Finset.range (k + 1)).filter
    (fun r : ℕ => (r : ℝ) ≤ p * k)) (fun r hr =>
      choose_le_exp_mul_binEntropy hp hp1 (Finset.mem_filter.mp hr).2)
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  have hc := Finset.card_filter_le (Finset.range (k + 1))
    (fun r : ℕ => (r : ℝ) ≤ p * k)
  exact h.trans (mul_le_mul_of_nonneg_right (by
    exact_mod_cast (show _ ≤ k + 1 by simpa only [Finset.card_range] using hc))
    (exp_pos _).le)

end Real

namespace Finset

variable {α : Type*}

/-- Binary-entropy bound on the actual number of subsets with admissible cardinality.

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 7, `07-comparators.tex`, lines 577–590 (before `comparator:inverse-compression`).
Original proof of `Finset.card_filter_powerset_le_mul_exp_binEntropy`;
no upstream Lean proof text reused.
-/
theorem card_filter_powerset_le_mul_exp_binEntropy (s : Finset α)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    ((s.powerset.filter (fun t : Finset α => (t.card : ℝ) ≤ p * s.card)).card : ℝ) ≤
      ((s.card : ℝ) + 1) * Real.exp (s.card * Real.binEntropy p) := by
  classical
  let I := (range (s.card + 1)).filter (fun r : ℕ => (r : ℝ) ≤ p * s.card)
  have hsub : s.powerset.filter (fun t : Finset α => (t.card : ℝ) ≤ p * s.card) ⊆
      I.biUnion (fun r => s.powersetCard r) := fun t ht =>
    mem_biUnion.mpr ⟨t.card, mem_filter.mpr ⟨mem_range.mpr
      (Nat.lt_succ_of_le (card_le_card (mem_powerset.mp (mem_filter.mp ht).1))),
      (mem_filter.mp ht).2⟩,
      mem_powersetCard.mpr ⟨mem_powerset.mp (mem_filter.mp ht).1, rfl⟩⟩
  have hcard := (card_le_card hsub).trans
    (card_biUnion_le (s := I) (t := fun r => s.powersetCard r))
  simp only [card_powersetCard] at hcard
  have hc : ((s.powerset.filter (fun t : Finset α =>
      (t.card : ℝ) ≤ p * s.card)).card : ℝ) ≤
      ∑ r ∈ I, (s.card.choose r : ℝ) := by
    exact_mod_cast hcard
  exact hc.trans (Real.sum_choose_le_mul_exp_binEntropy hp hp1 s.card)

end Finset

section ReplicaComponentUniformRate

/-!
# Uniform rates over excitation subsets

The three binomial corrections in the component inverse estimate are
bounded by binary entropy. The number of good copies is at least
`(1 - τ) * k`, so a nonnegative physical entropy difference retains that
fraction of its contribution. A fixed polynomial moment loss is absorbed
into the original polynomial prefactor. All errors remain explicit.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550–590, `comparator:component-inverse`
and `comparator:inverse-compression`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace Real

/-- The exact component factors give a rate uniform in every excitation
count `r ≤ τ k`. The original two label logarithms enter through their
sum `L`; the dimensions enter through `d`. No asymptotic error is hidden.
Source: `07-comparators.tex`, lines 550–590. -/
theorem replica_component_prefactor_le_uniform
    {k r : ℕ} (hrk : r ≤ k) {τ a d g K Λ : ℝ}
    (hτ : 0 ≤ τ) (hτhalf : τ ≤ 1 / 2) (hr : (r : ℝ) ≤ τ * k)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hg : 0 ≤ g) (hK : 0 ≤ K) (hΛ : 0 ≤ Λ)
    (C S ε L : ℝ) (hL : 2 * (k : ℝ) * S - ε ≤ L) :
    ((k : ℝ) + 2) ^ C * (k.choose r : ℝ) ^ a *
        exp (-a * (L - (r : ℝ) * d - 2 * log (k.choose r : ℝ))) *
        exp (-((k - r : ℕ) : ℝ) * a * g +
          25 * ((k - r : ℕ) : ℝ) * K * a ^ 2 +
          Λ * log (((k - r : ℕ) : ℝ) + 1)) ≤
      ((k : ℝ) + 2) ^ (C + Λ) *
        exp (-(k : ℝ) * a *
          (2 * S + (1 - τ) * g - τ * d - 3 * binEntropy τ) +
          a * ε + 25 * (k : ℝ) * K * a ^ 2) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hchoose : (0 : ℝ) < k.choose r := by
    exact_mod_cast Nat.choose_pos hrk
  have hlabel := mul_le_mul_of_nonpos_left hL (neg_nonpos.mpr ha)
  have hbad := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hr hd) ha
  have hgood := mul_le_mul_of_nonpos_right
    (show (1 - τ) * (k : ℝ) ≤ (k : ℝ) - r by nlinarith only [hr])
    (neg_nonpos.mpr (mul_nonneg ha hg))
  have hbinom := mul_le_mul_of_nonneg_left
    (log_choose_le_mul_binEntropy hτ hτhalf hr)
    (show 0 ≤ 3 * a by positivity)
  have hquad := mul_le_mul_of_nonneg_right
    (show (k : ℝ) - r ≤ k by linarith only [hr0])
    (show 0 ≤ 25 * K * a ^ 2 by positivity)
  have hlog := mul_le_mul_of_nonneg_left
    (log_le_log (by positivity : 0 < (((k - r : ℕ) : ℝ) + 1))
      (show (((k - r : ℕ) : ℝ) + 1) ≤ (k : ℝ) + 2 by
        rw [Nat.cast_sub hrk]
        linarith only [hr0])) hΛ
  have hexponent :
      log (k.choose r : ℝ) * a -
          a * (L - (r : ℝ) * d - 2 * log (k.choose r : ℝ)) +
          (-((k - r : ℕ) : ℝ) * a * g +
            25 * ((k - r : ℕ) : ℝ) * K * a ^ 2 +
            Λ * log (((k - r : ℕ) : ℝ) + 1)) ≤
        log ((k : ℝ) + 2) * Λ +
          (-(k : ℝ) * a *
            (2 * S + (1 - τ) * g - τ * d - 3 * binEntropy τ) +
            a * ε + 25 * (k : ℝ) * K * a ^ 2) := by
    rw [Nat.cast_sub hrk] at hlog ⊢
    nlinarith only [hlabel, hbad, hgood, hbinom, hquad, hlog]
  rw [rpow_def_of_pos hchoose, rpow_add (by positivity : 0 < (k : ℝ) + 2),
    rpow_def_of_pos (by positivity : 0 < (k : ℝ) + 2) Λ]
  simp only [mul_assoc, ← exp_add]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by
    simpa only [sub_eq_add_neg, neg_mul, add_assoc, mul_assoc] using hexponent))
    (rpow_nonneg (by positivity : 0 ≤ (k : ℝ) + 2) C)

end Real

end ReplicaComponentUniformRate


/-!
## Exponential bounds for a binomial coefficient

The exponential series at `j` gives `j ^ j / j ! ≤ e ^ j`, hence
`v.choose j ≤ v ^ j / j ! ≤ (e v / j) ^ j` for `j ≥ 1`. If moreover `v ≤ C j`, a weight `a ≥ 0`
attached to each of the `j` chosen elements gives `v.choose j * a ^ j ≤ (e C a) ^ j`, a bound
with a ratio independent of `j`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
`08-scanner.tex`, lines 310–325.
-/

namespace Nat

/-- `v.choose j ≤ (e v / j) ^ j` for `j ≥ 1`: the factorial in `v.choose j ≤ v ^ j / j !`
is bounded below by `(j / e) ^ j`. Two-dimensional area law, `08-scanner.tex`,
lines 318–321. -/
theorem choose_le_exp_mul_div_pow (v j : ℕ) (hj : 0 < j) :
    (v.choose j : ℝ) ≤ (Real.exp 1 * v / j) ^ j := by
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hfactorial := Real.pow_div_factorial_le_exp (j : ℝ) (Nat.cast_nonneg j) j
  have hexp : Real.exp (j : ℝ) = Real.exp 1 ^ j := by
    rw [← Real.exp_nat_mul, mul_one]
  rw [hexp] at hfactorial
  calc
    (v.choose j : ℝ) ≤ (v : ℝ) ^ j / j.factorial := Nat.choose_le_pow_div j v
    _ = ((v : ℝ) / j) ^ j * ((j : ℝ) ^ j / j.factorial) := by
      symm
      rw [div_pow, ← mul_div_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hj0)]
    _ ≤ ((v : ℝ) / j) ^ j * Real.exp 1 ^ j :=
      mul_le_mul_of_nonneg_left hfactorial (by positivity)
    _ = (Real.exp 1 * v / j) ^ j := by
      rw [← mul_pow]
      congr 1
      ring

/-- If `v ≤ C j` with `j ≥ 1` and `a ≥ 0`, then `v.choose j * a ^ j ≤ (e C a) ^ j`.
Two-dimensional area law, `08-scanner.tex`, lines 310–325. -/
theorem choose_mul_pow_le_exp_mul_pow (v j : ℕ) (hj : 0 < j)
    (a C : ℝ) (ha : 0 ≤ a) (hv : (v : ℝ) ≤ C * j) :
    (v.choose j : ℝ) * a ^ j ≤ (Real.exp 1 * C * a) ^ j := by
  have hjpos : (0 : ℝ) < j := by positivity
  have hbase : Real.exp 1 * v / j ≤ Real.exp 1 * C := by
    apply (div_le_iff₀ hjpos).mpr
    calc
      Real.exp 1 * v ≤ Real.exp 1 * (C * j) :=
        mul_le_mul_of_nonneg_left hv (Real.exp_pos 1).le
      _ = Real.exp 1 * C * j := by ring
  calc
    (v.choose j : ℝ) * a ^ j ≤ (Real.exp 1 * v / j) ^ j * a ^ j :=
      mul_le_mul_of_nonneg_right (choose_le_exp_mul_div_pow v j hj) (pow_nonneg ha _)
    _ = (Real.exp 1 * v / j * a) ^ j := (mul_pow _ _ _).symm
    _ ≤ (Real.exp 1 * C * a) ^ j :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hbase ha) _

end Nat
