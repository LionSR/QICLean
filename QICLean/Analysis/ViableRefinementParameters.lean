/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Error and common-threshold parameters for physical refinement

The internal closeness target is chosen so that the projected trial-space
energy is one half of the requested gap-scaled error. A single smaller
threshold controls both the actual viable tree and its final filter-and-trim
iterates. The nearby reference has an all-span bond at least its dimension;
this comparison is retained when checking the printed threshold inequality.

These are scalar auxiliaries for ALVV, arXiv:1602.08828v2, equation
`eq:algo-xi-dg`, lines 1800–1805, and final refinement, lines 1809–1817.
They do not construct the physical reference, tree or Ritz subspace, and do
not establish the iteration count printed in the source.
-/

namespace Real

/-- Explicit internal error and reference accuracy fit the stable
filter-and-trim recurrence and the final projected trial-space energy.
Supporting ALVV, arXiv:1602.08828v2, final refinement, lines 1809–1817;
the physical energy estimate and actual subspaces are separate. -/
theorem viable_refinement_error_parameters {A gamma eta : ℝ}
    (hgamma : 0 < gamma) (hgammaA : gamma ≤ A) (heta : 0 < eta) :
    let c := gamma / A
    let rho := eta * gamma / (2 * A + eta * gamma)
    let epsilon := c ^ 2 * rho / 32768
    0 < c ∧ c ≤ 1 ∧ 0 < rho ∧ rho < 1 ∧ rho ≤ eta / 2 ∧ c * rho ≤ eta / 2 ∧
      0 < epsilon ∧ epsilon ≤ 1 / 10000 ∧ epsilon ≤ c ^ 2 * rho / 1024 ∧
      A * rho / (1 - rho) = eta * gamma / 2 := by
  intro c rho epsilon
  have hA : 0 < A := hgamma.trans_le hgammaA
  have hden : 0 < 2 * A + eta * gamma := by positivity
  have hc : 0 < c := div_pos hgamma hA
  have hc1 : c ≤ 1 := (div_le_one hA).mpr hgammaA
  have hrho : 0 < rho := div_pos (mul_pos heta hgamma) hden
  have hrho1 : rho < 1 := (div_lt_one hden).mpr (by linarith)
  have hrhoEta : rho ≤ eta / 2 := by
    apply (div_le_iff₀ hden).mpr
    have hscaled := mul_le_mul_of_nonneg_left hgammaA heta.le
    nlinarith [mul_nonneg (sq_nonneg eta) hgamma.le]
  have hp : c * rho ≤ eta / 2 := by
    have hcontract : c * rho ≤ rho := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hrho.le
    exact hcontract.trans hrhoEta
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hc2 : c ^ 2 ≤ 1 := pow_le_one₀ hc.le hc1
  have hprod : c ^ 2 * rho ≤ 1 := by
    have hcontract : c ^ 2 * rho ≤ rho := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc2 hrho.le
    exact hcontract.trans hrho1.le
  have hepsilonSmall : epsilon ≤ 1 / 10000 := by
    dsimp only [epsilon]
    nlinarith only [hprod]
  have hepsilonBudget : epsilon ≤ c ^ 2 * rho / 1024 := by
    dsimp only [epsilon]
    nlinarith [mul_nonneg (sq_nonneg c) hrho.le]
  have hcomplement : 1 - rho = 2 * A / (2 * A + eta * gamma) := by
    dsimp only [rho]
    field_simp [hden.ne']
    ring
  refine ⟨hc, hc1, hrho, hrho1, hrhoEta, hp, hepsilon, hepsilonSmall, hepsilonBudget, ?_⟩
  rw [hcomplement]
  dsimp only [rho]
  field_simp [hA.ne', hden.ne']

private theorem inv_radius_mul_sqrt_le
    {L b B N : ℕ} (hb : 1 ≤ b) (hbB : b ≤ B) (hN : 1 ≤ N)
    {x : ℝ} (hx : x ≤ ((L : ℝ) + 1) * (b : ℝ) ^ 2) :
    (1 / (1000 * ((B * N : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))) * Real.sqrt x ≤
      1 / (1000 * (N : ℝ)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (Nat.zero_lt_one.trans_le hb)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_one.trans_le (hb.trans hbB))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_one.trans_le hN)
  have hroot0 : 0 < Real.sqrt ((L : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hroot : Real.sqrt x ≤ (b : ℝ) * Real.sqrt ((L : ℝ) + 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (L : ℝ) + 1)]
    simpa only [mul_comm] using hx
  calc
    _ ≤ (1 / (1000 * ((B * N : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))) *
        ((b : ℝ) * Real.sqrt ((L : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (b : ℝ) / (1000 * (B : ℝ) * (N : ℝ)) := by
      simp only [Nat.cast_mul]
      field_simp [hB0.ne', hN0.ne', hroot0.ne']
    _ ≤ 1 / (1000 * (N : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hbBR : (b : ℝ) ≤ B := by exact_mod_cast hbB
      nlinarith [mul_le_mul_of_nonneg_right hbBR
        (show 0 ≤ 1000 * (N : ℝ) by positivity)]

/-- One explicit positive threshold works below the tree threshold,
reserves the final reference-trimming budget, and satisfies the strict
printed threshold inequality with the actual reference bond.
Supporting ALVV, arXiv:1602.08828v2, `eq:algo-xi-dg`, lines 1800–1805.
The hypotheses `r ≤ b` and the two reference costs are retained. -/
theorem viable_refinement_radius_parameters
    {L r b Dtree Dfilter : ℕ} {p eta : ℝ}
    (hr : 1 ≤ r) (hrb : r ≤ b) (hDtree : 1 ≤ Dtree) (hDfilter : 1 ≤ Dfilter)
    (hp : 0 < p) (hpEta : p ≤ eta / 2) :
    let Dcommon := max Dtree b
    let N := Nat.ceil (100 * (Dfilter : ℝ) ^ 12 / p)
    let xi := 1 / (1000 * ((Dcommon * N : ℕ) : ℝ) * Real.sqrt ((L : ℝ) + 1))
    1 ≤ N ∧ 1 ≤ Dcommon * N ∧ 0 < xi ∧
      xi ≤ 1 / (1000 * (Dtree : ℝ) * Real.sqrt ((L : ℝ) + 1)) ∧
      xi * Real.sqrt (((L - 1 : ℕ) : ℝ) * (b : ℝ) ^ 2) ≤ p / 48 ∧
      Real.sqrt ((L : ℝ) * (r : ℝ) * (b : ℝ)) * xi <
        eta / (10000 * (Dfilter : ℝ) ^ 12) := by
  intro Dcommon N xi
  have hb : 1 ≤ b := hr.trans hrb
  have hDfilterR : (1 : ℝ) ≤ Dfilter := by exact_mod_cast hDfilter
  have hpow : (1 : ℝ) ≤ (Dfilter : ℝ) ^ 12 := one_le_pow₀ hDfilterR
  have hpow0 : 0 < (Dfilter : ℝ) ^ 12 := lt_of_lt_of_le (by norm_num) hpow
  have hNpos : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hN : 1 ≤ N := hNpos
  have hDcommon : 1 ≤ Dcommon := hDtree.trans (Nat.le_max_left Dtree b)
  have hDN : 1 ≤ Dcommon * N := by
    simpa only [one_mul] using Nat.mul_le_mul hDcommon hN
  have hDtreeProduct : Dtree ≤ Dcommon * N := by
    simpa only [mul_one] using Nat.mul_le_mul (Nat.le_max_left Dtree b) hN
  have hDtreeR : (0 : ℝ) < Dtree := by exact_mod_cast (Nat.zero_lt_one.trans_le hDtree)
  have hDNR : (0 : ℝ) < (Dcommon * N : ℕ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hDN)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hxi : 0 < xi := by dsimp only [xi]; positivity
  have hxiTree : xi ≤ 1 / (1000 * (Dtree : ℝ) * Real.sqrt ((L : ℝ) + 1)) := by
    dsimp only [xi]
    apply one_div_le_one_div_of_le (by positivity)
    have hdimR : (Dtree : ℝ) ≤ (Dcommon * N : ℕ) := by exact_mod_cast hDtreeProduct
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdimR (by norm_num : (0 : ℝ) ≤ 1000))
      (Real.sqrt_nonneg _)
  have hceil : 100 * (Dfilter : ℝ) ^ 12 / p ≤ (N : ℝ) := Nat.le_ceil _
  have hscale : 100 * (Dfilter : ℝ) ^ 12 ≤ (N : ℝ) * p :=
    (div_le_iff₀ hp).mp hceil
  have hbudget : 1 / (1000 * (N : ℝ)) ≤ p / (100000 * (Dfilter : ℝ) ^ 12) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 1000)]
  have hcuts : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) + 1 := by
    exact_mod_cast ((Nat.sub_le L 1).trans (Nat.le_succ L))
  have hreference := inv_radius_mul_sqrt_le (L := L) hb
    (show b ≤ Dcommon from Nat.le_max_right Dtree b) hN
    (mul_le_mul_of_nonneg_right hcuts (sq_nonneg (b : ℝ)))
  have hbudgetFinal : p / (100000 * (Dfilter : ℝ) ^ 12) ≤ p / 48 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpow hp.le]
  have hrbR : (r : ℝ) ≤ b := by exact_mod_cast hrb
  have hpaperRoot : (L : ℝ) * (r : ℝ) * (b : ℝ) ≤ ((L : ℝ) + 1) * (b : ℝ) ^ 2 := by
    calc
      _ ≤ (L : ℝ) * (b : ℝ) * (b : ℝ) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrbR (Nat.cast_nonneg L)) (Nat.cast_nonneg b)
      _ ≤ _ := by nlinarith [sq_nonneg (b : ℝ)]
  have hpaper := inv_radius_mul_sqrt_le (L := L) hb
    (show b ≤ Dcommon from Nat.le_max_right Dtree b) hN hpaperRoot
  have heta : 0 < eta := by linarith
  have hstrict : 1 / (1000 * (N : ℝ)) < eta / (10000 * (Dfilter : ℝ) ^ 12) := by
    calc
      _ ≤ p / (100000 * (Dfilter : ℝ) ^ 12) := hbudget
      _ ≤ (eta / 2) / (100000 * (Dfilter : ℝ) ^ 12) :=
        div_le_div_of_nonneg_right hpEta (by positivity)
      _ < _ := by
        apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [mul_pos heta hpow0]
  refine ⟨hN, hDN, hxi, hxiTree, hreference.trans (hbudget.trans hbudgetFinal), ?_⟩
  simpa only [xi, mul_comm] using hpaper.trans_lt hstrict

end Real
