/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Find
import QICLean.Entropy.Classical.ProbabilityEntropy
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Entropy from finite rank-tail bounds

For a probability distribution on finitely many ordered indices, upper bounds
on its masses beyond prescribed ranks give an explicit entropy bound. The
ranks may repeat and may exceed the number of indices. The probabilities may
appear in any order.

The proof compares the distribution with positive dyadic weights, normalized
after grouping the indices by their first covering rank. One telescoping
identity expresses the resulting logarithmic cost in terms of the given tails.

This finite probability estimate supplies the entropy summation step in the
following arguments. It makes no assertion about a Hamiltonian or a choice of
low-rank approximations.

## References

* AKLV, arXiv:1301.1162v1, `1dfrustrated34.tex`, lines 1059–1075.
* Hastings, arXiv:0705.2024v4, `law16.tex`, equations `constraint` and
  `constraint2`, lines 344–390.
* ALVV, arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, proof of `thm:al-dg`,
  lines 1085–1087.

Moved from TNLean, `TNLean/MPS/AreaLaw/LowEnergyAlgorithm/LowDensity/LowDensityEntropy.lean` at
commit `021ba0bd19` (Apache-2.0).
-/

open scoped BigOperators

namespace Entropy

/-- Adjacent monotonicity, restricted to a finite interval, suffices throughout. -/
private theorem rankSchedule_mono {M : ℕ} {R : ℕ → ℕ}
    (hR : ∀ i < M, R i ≤ R (i + 1))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ M) : R i ≤ R j := by
  revert hj
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
    intro hj
    exact (ih (by omega)).trans (hR j (by omega))

/-- A finite partial sum of the dyadic probability weights. -/
private theorem sum_dyadic_weights (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), 1 / (2 : ℝ) ^ (j + 1)) =
      1 - 1 / (2 : ℝ) ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show (2 : ℝ) ^ (m + 1 + 1) = (2 : ℝ) ^ (m + 1) * 2 from pow_succ _ _]
    have hn : (2 : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    ring

/-- Entropy from finite rank-tail bounds. The ranks need not be strict, and the
probability family need not be decreasing. No positivity of the tail majorants
is assumed: it follows on the relevant indices from the tail inequalities.

Sources: AKLV, arXiv:1301.1162v1, lines1059–1075; Hastings,
arXiv:0705.2024v4, equations constraint and constraint2, lines344–390;
ALVV, arXiv:1602.08828v2, proof of thm:al-dg, lines1085–1087. -/
theorem probabilityEntropy_le_of_rankTailBounds
    {N M : ℕ} (p : Fin N → ℝ) (R : ℕ → ℕ) (t : ℕ → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (hR0 : 0 < R 0)
    (hR : ∀ i < M, R i ≤ R (i + 1))
    (hcover : N ≤ R M)
    (htail : ∀ i < M,
      (∑ a ∈ Finset.univ.filter (fun a : Fin N ↦ R i ≤ a.val), p a) ≤ t i) :
    probabilityEntropy p ≤
      Real.log (R 0 : ℝ) +
        Real.log 2 * (1 + ∑ i ∈ Finset.range M, t i) +
        ∑ i ∈ Finset.range M,
          t i * Real.log ((R (i + 1) : ℝ) / (R i : ℝ)) := by
  classical
  have hN : 0 < N := by
    by_contra h
    have hzero : N = 0 := by omega
    subst N
    simp at hsum
  have hmono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ M) : R i ≤ R j :=
    rankSchedule_mono hR hij hj
  have hpos (i : ℕ) (hi : i ≤ M) : 0 < (R i : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hR0 (hmono (Nat.zero_le i) hi)
  have hex (a : Fin N) : ∃ j : ℕ, j ≤ M ∧ a.val < R j :=
    ⟨M, le_rfl, lt_of_lt_of_le a.isLt hcover⟩
  let j : Fin N → ℕ := fun a ↦ Nat.find (hex a)
  have hj (a : Fin N) : j a ≤ M ∧ a.val < R (j a) := Nat.find_spec (hex a)
  have hfirst (a : Fin N) (i : ℕ) (hi : i < M) :
      i < j a ↔ R i ≤ a.val := by
    constructor
    · intro hij
      by_contra hn
      have hfound : j a ≤ i := Nat.find_min' (hex a) ⟨by omega, by omega⟩
      omega
    · intro hia
      by_contra hn
      have hm : R (j a) ≤ R i := hmono (by omega) (by omega)
      have ha := (hj a).2
      omega
  let w : Fin N → ℝ := fun a ↦
    1 / ((2 : ℝ) ^ (j a + 1) * (R (j a) : ℝ))
  have hw (a : Fin N) : 0 < w a := by
    dsimp [w]
    exact one_div_pos.mpr (mul_pos (pow_pos (by norm_num) _) (hpos _ (hj a).1))
  let Z : ℝ := ∑ a, w a
  have hZ : 0 < Z := by
    let a₀ : Fin N := ⟨0, hN⟩
    exact lt_of_lt_of_le (hw a₀)
      (Finset.single_le_sum (fun a _ ↦ (hw a).le) (Finset.mem_univ a₀))
  have hfiber (b : ℕ) (hb : b < M + 1) :
      (∑ a ∈ Finset.univ.filter (fun a : Fin N ↦ j a = b), w a) ≤
        1 / (2 : ℝ) ^ (b + 1) := by
    let F : Finset (Fin N) := Finset.univ.filter (fun a ↦ j a = b)
    have hcard : F.card ≤ R b := by
      calc
        F.card ≤ (Finset.range (R b)).card := by
          refine Finset.card_le_card_of_injOn Fin.val ?_ ?_
          · intro a ha
            have hja : j a = b := (Finset.mem_filter.mp ha).2
            exact Finset.mem_range.mpr (by simpa only [hja] using (hj a).2)
          · intro a _ b _ hab
            exact Fin.ext hab
        _ = R b := Finset.card_range _
    have hF : (∑ a ∈ F, w a) =
        (F.card : ℝ) * (1 / ((2 : ℝ) ^ (b + 1) * (R b : ℝ))) := by
      calc
        (∑ a ∈ F, w a) = ∑ _a ∈ F,
            1 / ((2 : ℝ) ^ (b + 1) * (R b : ℝ)) := by
          apply Finset.sum_congr rfl
          intro a ha
          have hja : j a = b := (Finset.mem_filter.mp ha).2
          simp only [w, hja]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    change (∑ a ∈ F, w a) ≤ _
    rw [hF]
    calc
      _ ≤ (R b : ℝ) * (1 / ((2 : ℝ) ^ (b + 1) * (R b : ℝ))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = 1 / (2 : ℝ) ^ (b + 1) := by
        have hr := (hpos b (by omega)).ne'
        have htwo : (2 : ℝ) ^ (b + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
        field_simp
  have hgroup : Z = ∑ b ∈ Finset.range (M + 1),
      ∑ a ∈ Finset.univ.filter (fun a : Fin N ↦ j a = b), w a := by
    calc
      Z = ∑ a : Fin N, ∑ b ∈ Finset.range (M + 1),
          if j a = b then w a else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        symm
        rw [Finset.sum_eq_single (j a)]
        · simp
        · intro b _ hb
          simp [Ne.symm hb]
        · intro hn
          exact (hn (Finset.mem_range.mpr (Nat.lt_succ_of_le (hj a).1))).elim
      _ = ∑ b ∈ Finset.range (M + 1),
          ∑ a : Fin N, if j a = b then w a else 0 := by
        rw [Finset.sum_comm]
      _ = _ := by simp only [Finset.sum_filter]
  have hZ1 : Z ≤ 1 := by
    rw [hgroup]
    calc
      _ ≤ ∑ b ∈ Finset.range (M + 1), 1 / (2 : ℝ) ^ (b + 1) :=
        Finset.sum_le_sum fun b hb ↦ hfiber b (Finset.mem_range.mp hb)
      _ = 1 - 1 / (2 : ℝ) ^ (M + 1) := sum_dyadic_weights M
      _ ≤ 1 := sub_le_self _ (by positivity)
  let q : Fin N → ℝ := fun a ↦ w a / Z
  have hq (a : Fin N) : 0 < q a := div_pos (hw a) hZ
  have hqsum : ∑ a, q a = 1 := by
    dsimp [q]
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  have hg := TNLean.Klein.gibbs_core p q
    (fun a b ↦ if a = b then 1 else 0) hp hsum hq hqsum
    (by intro a b; split_ifs <;> norm_num)
    (by intro a; simp)
    (by intro b; simp)
  have hg' : (∑ a, p a * Real.log (q a)) ≤ ∑ a, p a * Real.log (p a) := by
    simpa using hg
  let c : ℕ → ℝ := fun b ↦
    ((b + 1 : ℕ) : ℝ) * Real.log 2 + Real.log (R b : ℝ)
  have hlogq (a : Fin N) : Real.log (q a) = -c (j a) - Real.log Z := by
    change Real.log (w a / Z) = _
    rw [Real.log_div (hw a).ne' hZ.ne']
    dsimp [w, c]
    rw [one_div, Real.log_inv,
      Real.log_mul (pow_ne_zero _ (by norm_num)) (hpos _ (hj a).1).ne',
      Real.log_pow]
  have hsumlogq : (∑ a, p a * Real.log (q a)) =
      -(∑ a, p a * c (j a)) - Real.log Z := by
    simp_rw [hlogq, mul_sub, mul_neg]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.sum_mul, hsum, one_mul]
  have hentropy : probabilityEntropy p = -(∑ a, p a * Real.log (p a)) := by
    simp [probabilityEntropy, Real.negMulLog, Finset.sum_neg_distrib, neg_mul]
  have hent : probabilityEntropy p ≤ ∑ a, p a * c (j a) := by
    rw [hsumlogq] at hg'
    have hlogZ : Real.log Z ≤ 0 := Real.log_nonpos hZ.le hZ1
    rw [hentropy]
    linarith
  let d : ℕ → ℝ := fun i ↦
    Real.log 2 + Real.log ((R (i + 1) : ℝ) / (R i : ℝ))
  have hd (i : ℕ) (hi : i < M) : 0 ≤ d i := by
    change 0 ≤ Real.log 2 + Real.log ((R (i + 1) : ℝ) / (R i : ℝ))
    apply add_nonneg (Real.log_nonneg (by norm_num))
    apply Real.log_nonneg
    apply (le_div_iff₀ (hpos i (by omega))).mpr
    simpa only [one_mul] using (show (R i : ℝ) ≤ R (i + 1) by exact_mod_cast hR i hi)
  have hc (b : ℕ) (hb : b ≤ M) :
      c b = Real.log 2 + Real.log (R 0 : ℝ) + ∑ i ∈ Finset.range b, d i := by
    revert hb
    induction b with
    | zero => intro _; simp [c]
    | succ b ih =>
      intro hb
      have hstep : c (b + 1) = c b + d b := by
        dsimp [c, d]
        rw [Real.log_div (hpos (b + 1) hb).ne' (hpos b (by omega)).ne']
        push_cast
        ring
      rw [hstep, ih (by omega), Finset.sum_range_succ]
      ring
  have hcost (a : Fin N) : c (j a) =
      Real.log 2 + Real.log (R 0 : ℝ) +
        ∑ i ∈ Finset.range M, if R i ≤ a.val then d i else 0 := by
    rw [hc _ (hj a).1]
    congr 1
    have hfilter : (Finset.range M).filter (fun i ↦ i < j a) = Finset.range (j a) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      have hm := (hj a).1
      omega
    calc
      (∑ i ∈ Finset.range (j a), d i) =
          ∑ i ∈ Finset.range M, if i < j a then d i else 0 := by
        rw [← Finset.sum_filter, hfilter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [hfirst a i (Finset.mem_range.mp hi)]
  have hcostsum : (∑ a, p a * c (j a)) =
      Real.log 2 + Real.log (R 0 : ℝ) +
        ∑ i ∈ Finset.range M,
          (∑ a ∈ Finset.univ.filter (fun a : Fin N ↦ R i ≤ a.val), p a) * d i := by
    have hpoint (a : Fin N) : p a * c (j a) =
        p a * (Real.log 2 + Real.log (R 0 : ℝ)) +
          ∑ i ∈ Finset.range M, p a * (if R i ≤ a.val then d i else 0) := by
      rw [hcost, mul_add, Finset.mul_sum]
    calc
      (∑ a, p a * c (j a)) =
          ∑ a : Fin N, (p a * (Real.log 2 + Real.log (R 0 : ℝ)) +
            ∑ i ∈ Finset.range M, p a * (if R i ≤ a.val then d i else 0)) := by
        exact Finset.sum_congr rfl (fun a _ ↦ hpoint a)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        calc
          (∑ a : Fin N, p a * (if R i ≤ a.val then d i else 0)) =
              ∑ a ∈ Finset.univ.filter (fun a : Fin N ↦ R i ≤ a.val), p a * d i := by
            rw [Finset.sum_filter]
            simp only [mul_ite, mul_zero]
          _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    probabilityEntropy p ≤ ∑ a, p a * c (j a) := hent
    _ = Real.log 2 + Real.log (R 0 : ℝ) +
        ∑ i ∈ Finset.range M,
          (∑ a ∈ Finset.univ.filter (fun a : Fin N ↦ R i ≤ a.val), p a) * d i := hcostsum
    _ ≤ Real.log 2 + Real.log (R 0 : ℝ) + ∑ i ∈ Finset.range M, t i * d i := by
      apply add_le_add le_rfl
      exact Finset.sum_le_sum fun i hi ↦
        mul_le_mul_of_nonneg_right (htail i (Finset.mem_range.mp hi))
          (hd i (Finset.mem_range.mp hi))
    _ = _ := by
      dsimp [d]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      ring

end Entropy

open scoped BigOperators

namespace Real

/-- A quadratic potential telescopes the three finite dyadic moments at once.
Auxiliary to the entropy summation in ALVV, arXiv:1602.08828v2,
proof of `thm:al-dg`, lines 1085–1087. -/
theorem sum_quadratic_div_dyadic_le (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (M : ℕ) :
    (∑ i ∈ Finset.range M,
      (a * (i : ℝ) ^ 2 + b * (i : ℝ) + c) / (2 : ℝ) ^ (i + 1)) ≤
      3 * a + b + c := by
  let Q : ℕ → ℝ := fun i ↦
    (a * (i : ℝ) ^ 2 + (2 * a + b) * (i : ℝ) + (3 * a + b + c)) /
      (2 : ℝ) ^ i
  have hstep (i : ℕ) : Q i - Q (i + 1) =
      (a * (i : ℝ) ^ 2 + b * (i : ℝ) + c) / (2 : ℝ) ^ (i + 1) := by
    dsimp only [Q]
    push_cast
    simp only [show (2 : ℝ) ^ (i + 1) = (2 : ℝ) ^ i * 2 from pow_succ _ _]
    have hpow : (2 : ℝ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    ring
  have hQ : 0 ≤ Q M := by dsimp only [Q]; positivity
  calc
    _ = ∑ i ∈ Finset.range M, (Q i - Q (i + 1)) :=
      Finset.sum_congr rfl fun i _ ↦ (hstep i).symm
    _ = Q 0 - Q M := Finset.sum_range_sub' Q M
    _ ≤ Q 0 := sub_le_self _ hQ
    _ = 3 * a + b + c := by simp [Q]

end Real

namespace Entropy

/-- A cubic logarithmic rank schedule and dyadic tail losses give a finite
entropy bound with coefficient exactly one on the logarithm of the initial
rank. The ranks need not lie below the size of the probability space.
Auxiliary to ALVV, arXiv:1602.08828v2, proof of `thm:al-dg`, lines 1085–1087.
This is a finite probability estimate; it does not assert the sharper
error-dependent approximation ranks or an efficient physical construction. -/
theorem probabilityEntropy_le_of_cubic_dyadic_rank_tail_bounds
    {N : ℕ} (r B : ℕ) (hr : 1 ≤ r) (hB : 1 ≤ B) (p : Fin N → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (htail : ∀ i < N,
      (∑ a ∈ Finset.univ.filter (fun a : Fin N ↦
        r * 2 ^ (B * (i + 1) ^ 3) ≤ a.val), p a) ≤
          1 / (2 : ℝ) ^ (i + 1)) :
    probabilityEntropy p ≤ Real.log (r : ℝ) +
      26 * (B : ℝ) * Real.log 2 + 2 * Real.log 2 := by
  let R : ℕ → ℕ := fun i ↦ r * 2 ^ (B * (i + 1) ^ 3)
  have hr0 : 0 < r := by omega
  have hRpos (i : ℕ) : 0 < R i := by dsimp only [R]; positivity
  have hRreal (i : ℕ) : 0 < (R i : ℝ) := by exact_mod_cast hRpos i
  have hmono (i : ℕ) : R i ≤ R (i + 1) := by
    apply Nat.mul_le_mul_left r
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    exact Nat.mul_le_mul_left B (Nat.pow_le_pow_left (Nat.le_succ (i + 1)) 3)
  have hexponent : N ≤ B * (N + 1) ^ 3 := by
    calc
      N ≤ N + 1 := Nat.le_succ N
      _ = (N + 1) ^ 1 := (pow_one _).symm
      _ ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by decide : 1 ≤ 3)
      _ ≤ B * (N + 1) ^ 3 := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right ((N + 1) ^ 3) hB
  have hcover : N ≤ R N := by
    calc
      N ≤ 2 ^ N := (show N < 2 ^ N from Nat.lt_two_pow_self).le
      _ ≤ 2 ^ (B * (N + 1) ^ 3) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) hexponent
      _ ≤ r * 2 ^ (B * (N + 1) ^ 3) := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2 ^ (B * (N + 1) ^ 3)) hr
  have hlog (i : ℕ) : Real.log (R i : ℝ) = Real.log (r : ℝ) +
      (B : ℝ) * ((i : ℝ) + 1) ^ 3 * Real.log 2 := by
    dsimp only [R]
    rw [Nat.cast_mul, Nat.cast_pow,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlog0 : Real.log (R 0 : ℝ) = Real.log (r : ℝ) + (B : ℝ) * Real.log 2 := by
    simpa using hlog 0
  have hinc (i : ℕ) : Real.log ((R (i + 1) : ℝ) / (R i : ℝ)) =
      (B : ℝ) * Real.log 2 * (3 * (i : ℝ) ^ 2 + 9 * (i : ℝ) + 7) := by
    rw [Real.log_div (hRreal (i + 1)).ne' (hRreal i).ne', hlog (i + 1), hlog i]
    push_cast
    ring
  have hmass : (∑ i ∈ Finset.range N, 1 / (2 : ℝ) ^ (i + 1)) ≤ 1 := by
    simpa using Real.sum_quadratic_div_dyadic_le 0 0 1
      (by norm_num) (by norm_num) (by norm_num) N
  have hmoment : (∑ i ∈ Finset.range N,
      (3 * (i : ℝ) ^ 2 + 9 * (i : ℝ) + 7) / (2 : ℝ) ^ (i + 1)) ≤ 25 := by
    simpa only [show (3 : ℝ) * 3 + 9 + 7 = 25 by norm_num] using
      Real.sum_quadratic_div_dyadic_le 3 9 7
        (by norm_num) (by norm_num) (by norm_num) N
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcost : (∑ i ∈ Finset.range N,
      (1 / (2 : ℝ) ^ (i + 1)) * Real.log ((R (i + 1) : ℝ) / (R i : ℝ))) ≤
      25 * (B : ℝ) * Real.log 2 := by
    simp_rw [hinc]
    calc
      _ = ((B : ℝ) * Real.log 2) * (∑ i ∈ Finset.range N,
          (3 * (i : ℝ) ^ 2 + 9 * (i : ℝ) + 7) / (2 : ℝ) ^ (i + 1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ ≤ ((B : ℝ) * Real.log 2) * 25 :=
        mul_le_mul_of_nonneg_left hmoment (mul_nonneg (Nat.cast_nonneg B) hlog2)
      _ = 25 * (B : ℝ) * Real.log 2 := by ring
  have hraw := probabilityEntropy_le_of_rankTailBounds
    (M := N) p R (fun i ↦ 1 / (2 : ℝ) ^ (i + 1)) hp hsum (hRpos 0)
    (fun i _ ↦ hmono i) hcover htail
  calc
    probabilityEntropy p ≤ Real.log (R 0 : ℝ) +
        Real.log 2 * (1 + ∑ i ∈ Finset.range N, 1 / (2 : ℝ) ^ (i + 1)) +
        ∑ i ∈ Finset.range N,
          (1 / (2 : ℝ) ^ (i + 1)) * Real.log ((R (i + 1) : ℝ) / (R i : ℝ)) := hraw
    _ ≤ (Real.log (r : ℝ) + (B : ℝ) * Real.log 2) +
        Real.log 2 * (1 + 1) + 25 * (B : ℝ) * Real.log 2 := by
      rw [hlog0]
      exact add_le_add (add_le_add_right
        (mul_le_mul_of_nonneg_left (add_le_add_right hmass 1) hlog2) _) hcost
    _ = Real.log (r : ℝ) + 26 * (B : ℝ) * Real.log 2 + 2 * Real.log 2 := by ring

end Entropy

section ProbabilityEntropyGeometricTails

/-!
# Entropy from geometric rank tails

A finite probability distribution with geometric bounds on its mass beyond
geometric ranks has an explicit Shannon entropy bound. The proof applies the
finite rank-tail entropy estimate and sums a finite geometric progression.

## Main statements

* `Entropy.probabilityEntropy_le_of_geometricRankTailBounds`: the bound for a
  finite covering cutoff and geometric tail majorants.

## References

* AKLV, arXiv:1301.1162v1, entropy summation, lines 1059–1075.
* Hastings, arXiv:0705.2024v4, equations `constraint` and `constraint2`.
* ALVV, arXiv:1602.08828v2, proof of `thm:al-dg`.
-/

open scoped BigOperators

namespace Entropy

/-- A geometric bound on masses beyond geometric ranks gives a uniform
finite entropy estimate. The case `D = 1` is included.

Supporting entropy summation in AKLV, arXiv:1301.1162v1, lines 1059–1075;
Hastings, arXiv:0705.2024v4, equations constraint and constraint2; and ALVV,
arXiv:1602.08828v2, proof of thm:al-dg. This is a finite-probability
auxiliary, not the full source theorem. -/
theorem probabilityEntropy_le_of_geometricRankTailBounds
    {N : ℕ} (p : Fin N → ℝ) (a M D : ℕ) (θ : ℝ)
    (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, p b = 1)
    (hD : 1 ≤ D) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hcover : N ≤ D ^ (a + M))
    (htail : ∀ i < M,
      (∑ b ∈ Finset.univ.filter (fun b : Fin N ↦ D ^ (a + i) ≤ b.val), p b)
        ≤ θ ^ (i + 1)) :
    probabilityEntropy p ≤
      (a : ℝ) * Real.log (D : ℝ) +
        (Real.log 2 + θ * Real.log (D : ℝ)) / (1 - θ) := by
  classical
  have hDpos : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hden : 0 < 1 - θ := sub_pos.mpr hθ1
  have hlogD : 0 ≤ Real.log (D : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hD)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  let s : ℝ := ∑ i ∈ Finset.range M, θ ^ (i + 1)
  have hgeom :
      s = θ * (∑ i ∈ Finset.range M, θ ^ i) := by
    dsimp [s]
    simp_rw [pow_succ]
    rw [← Finset.sum_mul]
    ring
  have hgeom_product : s * (1 - θ) = θ * (1 - θ ^ M) := by
    rw [hgeom, mul_assoc, geom_sum_mul_neg]
  have hs : s ≤ θ / (1 - θ) := by
    apply (le_div_iff₀ hden).2
    rw [hgeom_product]
    have hn : 0 ≤ θ * θ ^ M := mul_nonneg hθ0 (pow_nonneg hθ0 M)
    nlinarith
  have hstart :
      Real.log (((D ^ (a + 0)) : ℕ) : ℝ) =
        (a : ℝ) * Real.log (D : ℝ) := by
    simp only [Nat.add_zero, Nat.cast_pow, Real.log_pow]
  have hratio (i : ℕ) :
      Real.log
          ((((D ^ (a + (i + 1))) : ℕ) : ℝ) /
            (((D ^ (a + i)) : ℕ) : ℝ)) =
        Real.log (D : ℝ) := by
    simp only [Nat.cast_pow]
    rw [Real.log_div (pow_ne_zero _ hDreal.ne') (pow_ne_zero _ hDreal.ne'),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hweighted :
      (∑ i ∈ Finset.range M,
        θ ^ (i + 1) *
          Real.log
            ((((D ^ (a + (i + 1))) : ℕ) : ℝ) /
              (((D ^ (a + i)) : ℕ) : ℝ))) =
        s * Real.log (D : ℝ) := by
    simp_rw [hratio]
    exact (Finset.sum_mul (Finset.range M)
      (fun i ↦ θ ^ (i + 1)) (Real.log (D : ℝ))).symm
  have hbound := probabilityEntropy_le_of_rankTailBounds (M := M)
    p (fun i ↦ D ^ (a + i)) (fun i ↦ θ ^ (i + 1)) hp hsum
    (by simpa only [Nat.add_zero] using pow_pos hDpos a)
    (by
      intro i _hi
      exact pow_le_pow_right' hD (Nat.add_le_add_left (Nat.le_succ i) a))
    hcover htail
  change probabilityEntropy p ≤
    Real.log (((D ^ (a + 0)) : ℕ) : ℝ) + Real.log 2 * (1 + s) +
      (∑ i ∈ Finset.range M,
        θ ^ (i + 1) *
          Real.log
            ((((D ^ (a + (i + 1))) : ℕ) : ℝ) /
              (((D ^ (a + i)) : ℕ) : ℝ))) at hbound
  rw [hstart, hweighted] at hbound
  calc
    probabilityEntropy p ≤
        (a : ℝ) * Real.log (D : ℝ) + Real.log 2 * (1 + s) +
          s * Real.log (D : ℝ) := hbound
    _ = (a : ℝ) * Real.log (D : ℝ) + Real.log 2 +
        s * (Real.log 2 + Real.log (D : ℝ)) := by ring
    _ ≤ (a : ℝ) * Real.log (D : ℝ) + Real.log 2 +
        (θ / (1 - θ)) * (Real.log 2 + Real.log (D : ℝ)) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_right hs (add_nonneg hlog2 hlogD)) _
    _ = (a : ℝ) * Real.log (D : ℝ) +
        (Real.log 2 + θ * Real.log (D : ℝ)) / (1 - θ) := by
      field_simp [hden.ne']
      ring

end Entropy

end ProbabilityEntropyGeometricTails

section LowDensityEntropy

section

open scoped BigOperators

namespace Real

/-- Auxiliary to the entropy estimate in ALVV, arXiv:1602.08828v2,
proof of `thm:al-dg`, lines 1085–1087. Cubic logarithmic bounds at
dyadic numerical count bases admit one integer rank schedule. This is
a scalar statement and assumes no physical change of local dimension. -/
private theorem exists_cubic_dyadic_rank_majorant
    (q r : ℕ) (g K : ℝ) (D : ℕ → ℕ)
    (hq : 2 ≤ q) (hr : 1 ≤ r) (hg : 0 < g) (hg1 : g ≤ 1)
    (hK : 0 ≤ K) (hD : ∀ i, 1 ≤ D i)
    (hlogD : ∀ i, log (D i : ℝ) ≤
      K * (1 + log ((q * 2 ^ i : ℕ) : ℝ) + log (1 / g)) ^ 3) :
    let u : ℝ := 1 + log (q : ℝ) + log (1 / g)
    ∃ B : ℕ, 1 ≤ B ∧
      (B : ℝ) ≤ 26 * K * u ^ 3 / log 2 + 2 ∧
      ∀ i : ℕ, r * D 0 ^ 24 * D i ^ 2 ≤
        r * 2 ^ (B * (i + 1) ^ 3) := by
  intro u
  have hlog2pos : 0 < log 2 := log_pos (by norm_num)
  have hlog2le : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogq : 0 ≤ log (q : ℝ) := log_natCast_nonneg q
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).2 hg1)
  have hu : 1 ≤ u := by dsimp only [u]; linarith
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogbase (i : ℕ) : log ((q * 2 ^ i : ℕ) : ℝ) =
      log (q : ℝ) + (i : ℝ) * log 2 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      log_mul hqpos.ne' (by positivity), log_pow]
  have hscale (i : ℕ) :
      1 + log ((q * 2 ^ i : ℕ) : ℝ) + log (1 / g) ≤
        u * ((i : ℝ) + 1) := by
    rw [hlogbase]
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    dsimp only [u] at hu ⊢
    nlinarith
  have hlogDi (i : ℕ) : log (D i : ℝ) ≤
      K * u ^ 3 * ((i : ℝ) + 1) ^ 3 := by
    calc
      log (D i : ℝ) ≤
          K * (1 + log ((q * 2 ^ i : ℕ) : ℝ) + log (1 / g)) ^ 3 := hlogD i
      _ ≤ K * (u * ((i : ℝ) + 1)) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply pow_le_pow_left₀ _ (hscale i) 3
        linarith [log_natCast_nonneg (q * 2 ^ i)]
      _ = K * u ^ 3 * ((i : ℝ) + 1) ^ 3 := by ring
  let x : ℝ := 26 * K * u ^ 3 / log 2
  let B : ℕ := ⌈x⌉₊ + 1
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hB : 1 ≤ B := by dsimp only [B]; omega
  have hBupper : (B : ℝ) ≤ x + 2 := by
    have hceil := (Nat.ceil_lt_add_one hx).le
    dsimp only [B]
    push_cast
    linarith
  have hcoef : 26 * K * u ^ 3 ≤ (B : ℝ) * log 2 := by
    have hxB : x ≤ (B : ℝ) := by
      have hceil := Nat.le_ceil x
      dsimp only [B]
      push_cast
      linarith
    exact (div_le_iff₀ hlog2pos).mp hxB
  refine ⟨B, hB, hBupper, ?_⟩
  intro i
  have hi : (1 : ℝ) ≤ ((i : ℝ) + 1) ^ 3 := by
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith only [hi0] : (1 : ℝ) ≤ (i : ℝ) + 1) 3
    simpa using h
  have hlog0 : log (D 0 : ℝ) ≤ K * u ^ 3 := by simpa using hlogDi 0
  have hbudget : 24 * log (D 0 : ℝ) + 2 * log (D i : ℝ) ≤
      (B : ℝ) * ((i : ℝ) + 1) ^ 3 * log 2 := by
    have hbase : K * u ^ 3 ≤ K * u ^ 3 * ((i : ℝ) + 1) ^ 3 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ K * u ^ 3)
    have hfinal := mul_le_mul_of_nonneg_right hcoef
      (by positivity : 0 ≤ ((i : ℝ) + 1) ^ 3)
    nlinarith [hlogDi i]
  have hDpos (j : ℕ) : 0 < (D j : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le (hD j))
  have hrpos : 0 < (r : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hr)
  have hlogs : log ((r * D 0 ^ 24 * D i ^ 2 : ℕ) : ℝ) ≤
      log ((r * 2 ^ (B * (i + 1) ^ 3) : ℕ) : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
    rw [log_mul (mul_pos hrpos (pow_pos (hDpos 0) _)).ne'
      (pow_pos (hDpos i) _).ne',
      log_mul hrpos.ne' (pow_pos (hDpos 0) _).ne',
      log_mul hrpos.ne' (by positivity), log_pow, log_pow, log_pow]
    push_cast
    nlinarith
  have hleftpos : 0 < ((r * D 0 ^ 24 * D i ^ 2 : ℕ) : ℝ) := by
    push_cast
    exact mul_pos (mul_pos hrpos (pow_pos (hDpos 0) _)) (pow_pos (hDpos i) _)
  have hrightpos : 0 < ((r * 2 ^ (B * (i + 1) ^ 3) : ℕ) : ℝ) := by
    push_cast
    exact mul_pos hrpos (by positivity)
  have hreal := (log_le_log_iff hleftpos hrightpos).mp hlogs
  exact_mod_cast hreal

end Real

namespace Entropy

/-- Cubic logarithmic bounds on approximation ranks and dyadic probability
tails give an entropy estimate with coefficient one on the logarithm of the
ground-space rank. This is a pure finite-probability auxiliary for ALVV,
arXiv:1602.08828v2, proof of `thm:al-dg`, lines 1085–1087. The probability
tail bounds are inputs here; no physical tail estimate is asserted. -/
theorem probabilityEntropy_le_of_logarithmic_rank_tail_bounds
    {N : ℕ} (q r : ℕ) (g K : ℝ) (D : ℕ → ℕ)
    (hq : 2 ≤ q) (hr : 1 ≤ r) (hg : 0 < g) (hg1 : g ≤ 1)
    (hK : 0 ≤ K) (hD : ∀ i, 1 ≤ D i)
    (hlogD : ∀ i, Real.log (D i : ℝ) ≤
      K * (1 + Real.log ((q * 2 ^ i : ℕ) : ℝ) + Real.log (1 / g)) ^ 3)
    (p : Fin N → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (htail : ∀ i < N,
      (∑ a ∈ Finset.univ.filter (fun a : Fin N ↦
        r * D 0 ^ 24 * D i ^ 2 ≤ a.val), p a) ≤ 1 / (2 : ℝ) ^ (i + 1)) :
    let u : ℝ := 1 + Real.log (q : ℝ) + Real.log (1 / g)
    probabilityEntropy p ≤ Real.log (r : ℝ) + 676 * K * u ^ 3 + 54 * Real.log 2 := by
  intro u
  obtain ⟨B, hB, hBupper, hmajor⟩ :=
    Real.exists_cubic_dyadic_rank_majorant q r g K D hq hr hg hg1 hK hD hlogD
  have htailB (i : ℕ) (hi : i < N) :
      (∑ a ∈ Finset.univ.filter (fun a : Fin N ↦
        r * 2 ^ (B * (i + 1) ^ 3) ≤ a.val), p a) ≤ 1 / (2 : ℝ) ^ (i + 1) := by
    have hsubset :
        Finset.univ.filter (fun a : Fin N ↦ r * 2 ^ (B * (i + 1) ^ 3) ≤ a.val) ⊆
        Finset.univ.filter (fun a : Fin N ↦ r * D 0 ^ 24 * D i ^ 2 ≤ a.val) := by
      intro a ha
      obtain ⟨hauniv, hlarge⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨hauniv, (hmajor i).trans hlarge⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun a _ _ ↦ hp a)).trans (htail i hi)
  have hraw := probabilityEntropy_le_of_cubic_dyadic_rank_tail_bounds
    r B hr hB p hp hsum htailB
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoefficient : (B : ℝ) * Real.log 2 ≤ 26 * K * u ^ 3 + 2 * Real.log 2 := by
    calc
      (B : ℝ) * Real.log 2 ≤
          (26 * K * u ^ 3 / Real.log 2 + 2) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hBupper hlog2.le
      _ = 26 * K * u ^ 3 + 2 * Real.log 2 := by
        rw [add_mul, div_mul_cancel₀ _ hlog2.ne']
  nlinarith only [hraw, hcoefficient]

end Entropy

end

end LowDensityEntropy
