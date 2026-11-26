/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Order.Interval.Finset.Fin
import QICLean.Analysis.FunctionalCalculus.TraceCFC
import Mathlib.Analysis.Matrix.PosDef
import QICLean.Spectral.Eigenvalue.TailTraceNorm
import QICLean.Analysis.TraceNorm.RectangularTraceNormAlgebra
import QICLean.Entropy.Renyi.Defs

/-!
# Rényi bounds for ordered spectral tails

Verstraete–Cirac, arXiv:cond-mat/0505140v6, Lemma 2 (`convexPRA2.tex`, lines 335–352).
The proof bounds the power sum directly at a cutoff weight and applies weighted AM–GM.
It does not require the extremizing distribution asserted in the source proof.
All logarithms are natural. The logarithmic estimate requires a positive tail; the
power estimate also includes zero tails. Order zero is treated separately by rank.

It also contains the following results.

* `Entropy.log_card_bound_of_renyi_mass`, `Entropy.renyi_mass_sub_error_le_log_card`: Rényi entropy
  and concentration on a finite set.
* `Matrix.PosSemidef.renyiEntropy_add_log_error_le_log_rank`,
  `Matrix.PosSemidef.renyiEntropy_add_log_error_le_log_rank_of_rectangularTraceNorm`: Rényi lower
  bounds for low-rank approximation.
-/

section Tail

open scoped BigOperators ComplexOrder

namespace Entropy

private theorem log_tail_le_of_cutoff {a d t h m : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hd : 0 < d) (ht : 0 < t) (hh : 0 < h)
    (hm : d * h ^ a + t * h ^ (a - 1) ≤ m) :
    Real.log t ≤ (1 - a) / a * (Real.log m / (1 - a) - Real.log (d / (1 - a))) := by
  have hb : 0 < 1 - a := sub_pos.mpr ha1
  have hg := Real.geom_mean_le_arith_mean2_weighted hb.le ha.le
    (div_nonneg (mul_nonneg hd.le (Real.rpow_nonneg hh.le a)) hb.le)
    (div_nonneg (mul_nonneg ht.le (Real.rpow_nonneg hh.le (a - 1))) ha.le)
    (show 1 - a + a = 1 by ring)
  have hg' : (d * h ^ a / (1 - a)) ^ (1 - a) *
      (t * h ^ (a - 1) / a) ^ a ≤ m := by
    convert hg.trans (le_of_eq_of_le (by field_simp) hm) using 1
  have hl := Real.log_le_log (by positivity :
    0 < (d * h ^ a / (1 - a)) ^ (1 - a) * (t * h ^ (a - 1) / a) ^ a) hg'
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow (by positivity),
    Real.log_div (by positivity) hb.ne', Real.log_div (by positivity) ha.ne',
    Real.log_mul hd.ne' (by positivity), Real.log_mul ht.ne' (by positivity),
    Real.log_rpow hh, Real.log_rpow hh] at hl
  have hla : a * Real.log a ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha.le (Real.log_nonpos ha.le ha1.le)
  rw [show (1 - a) / a * (Real.log m / (1 - a) - Real.log (d / (1 - a))) =
    (Real.log m - (1 - a) * Real.log (d / (1 - a))) / a by field_simp]
  apply (le_div_iff₀ ha).2
  rw [Real.log_div hd.ne' hb.ne']
  nlinarith only [hl, hla]

/-- Verstraete–Cirac, Lemma 2: the logarithmic tail estimate for a finite decreasing
family of nonnegative weights. Normalization is unnecessary for this power-sum form. -/
theorem log_ordered_tail_le {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hmono : Antitone p) {D : ℕ} (hD : 0 < D) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (ht : 0 < ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ D ≤ i.val), p i) :
    Real.log (∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ D ≤ i.val), p i) ≤
      (1 - a) / a * (Real.log (∑ i, p i ^ a) / (1 - a) -
        Real.log ((D : ℝ) / (1 - a))) := by
  obtain ⟨j, hj, hjp⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hp i)).mp ht
  have hDn : D < n := lt_of_le_of_lt (Finset.mem_filter.mp hj).2 j.isLt
  have hh : 0 < p ⟨D, hDn⟩ :=
    hjp.trans_le (hmono (show (⟨D, hDn⟩ : Fin n) ≤ j from (Finset.mem_filter.mp hj).2))
  apply log_tail_le_of_cutoff ha ha1 (Nat.cast_pos.mpr hD) ht hh
  have hcard : (Finset.univ.filter (fun i : Fin n ↦ i.val < D)).card = D := by
    convert Fin.card_Iio (⟨D, hDn⟩ : Fin n) using 1
    congr 1
    ext i
    simp [Fin.lt_def]
  have hpre : (D : ℝ) * p ⟨D, hDn⟩ ^ a ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ i.val < D), p i ^ a := by
    calc
      _ = ∑ _i ∈ Finset.univ.filter (fun i : Fin n ↦ i.val < D), p ⟨D, hDn⟩ ^ a :=
        by simp [hcard]
      _ ≤ _ := Finset.sum_le_sum fun i hi ↦ Real.rpow_le_rpow hh.le
        (hmono (show i ≤ (⟨D, hDn⟩ : Fin n) from (Finset.mem_filter.mp hi).2.le)) ha.le
  have hpoint (i : Fin n) (hi : D ≤ i.val) :
      p i * p ⟨D, hDn⟩ ^ (a - 1) ≤ p i ^ a := by
    rcases (hp i).eq_or_lt with hz | hz
    · simp [← hz, Real.zero_rpow ha.ne']
    · calc
        _ ≤ p i * p i ^ (a - 1) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hz (hmono hi) (sub_nonpos.mpr ha1.le)) (hp i)
        _ = _ := by rw [Real.rpow_sub_one hz.ne']; field_simp
  have htail : (∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ D ≤ i.val), p i) *
      p ⟨D, hDn⟩ ^ (a - 1) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ D ≤ i.val), p i ^ a := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi ↦ hpoint i (Finset.mem_filter.mp hi).2
  exact (add_le_add hpre htail).trans_eq (by
    simpa only [not_lt] using Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n ↦ i.val < D) (fun i ↦ p i ^ a))

/-- Verstraete–Cirac, Lemma 2 in power form, including vanishing tails. -/
theorem ordered_tail_le_rpow {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hmono : Antitone p) {D : ℕ} (hD : 0 < D) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ D ≤ i.val), p i) ≤
      ((1 - a) * Real.exp (Real.log (∑ i, p i ^ a) / (1 - a)) / D) ^ ((1 - a) / a) := by
  by_cases ht : 0 < ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ D ≤ i.val), p i
  · have hb : 0 < 1 - a := sub_pos.mpr ha1
    have hd : (0 : ℝ) < D := Nat.cast_pos.mpr hD
    rw [Real.rpow_def_of_pos (by positivity)]
    apply (Real.log_le_iff_le_exp ht).mp
    convert log_ordered_tail_le p hp hmono hD ha ha1 ht using 1
    rw [Real.log_div (by positivity) hd.ne',
        Real.log_mul hb.ne' (Real.exp_pos _).ne', Real.log_exp,
        Real.log_div hd.ne' hb.ne']
    ring
  · exact (le_of_not_gt ht).trans (Real.rpow_nonneg (by positivity) _)

/-- The order-zero case: a decreasing nonnegative family has zero tail once
its support fits within the cutoff. This uses support size, not a singular
substitution into the positive-order Rényi bound. -/
theorem ordered_tail_eq_zero_of_card_support_le {n D : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hmono : Antitone p)
    (hcard : (Finset.univ.filter (fun i ↦ p i ≠ 0)).card ≤ D) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ D ≤ i.val), p i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hpi
  have hpos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hpi)
  have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j ↦ p j ≠ 0) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hpos.trans_le (hmono (Finset.mem_Iic.mp hj))).ne'⟩
  have hc := (Finset.card_le_card hsub).trans hcard
  simp only [Fin.card_Iic] at hc
  have hi' := (Finset.mem_filter.mp hi).2
  omega

end Entropy

namespace Matrix.IsHermitian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}

/-- The trace of a real spectral function as a sum over the decreasingly ordered spectrum. -/
theorem trace_cfc_eq_sum_eigenvalues₀ (hρ : ρ.IsHermitian) (f : ℝ → ℝ) :
    (hρ.cfc f).trace.re = ∑ i, f (hρ.eigenvalues₀ i) := by
  rw [← RCLike.re_eq_complex_re, hρ.trace_cfc_eq_sum_re]
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm
    (fun i ↦ f (hρ.eigenvalues₀ i))

end Matrix.IsHermitian

namespace Matrix.PosSemidef

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}

private theorem eigenvalues₀_nonneg (hρ : ρ.PosSemidef) (i : Fin (Fintype.card ι)) :
    0 ≤ hρ.isHermitian.eigenvalues₀ i := by
  simpa [Matrix.IsHermitian.eigenvalues] using
    hρ.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))) i)

/-- Verstraete–Cirac, Lemma 2 (arXiv:cond-mat/0505140v6, lines 335–352),
with natural logarithms. For a trace-one positive operator the logarithmic power
sum divided by `1 - a` is its Rényi entropy. The estimate also holds without
trace normalization. Only the logarithmic form requires a positive tail. -/
theorem log_eigenvalue_tail_le (hρ : ρ.PosSemidef) {D : ℕ} (hD : 0 < D)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (ht : 0 < ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card ι) ↦ D ≤ i.val),
      hρ.isHermitian.eigenvalues₀ i) :
    Real.log (∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card ι) ↦ D ≤ i.val),
      hρ.isHermitian.eigenvalues₀ i) ≤
      (1 - a) / a * (Real.log (hρ.isHermitian.cfc (fun x ↦ x ^ a)).trace.re / (1 - a) -
        Real.log ((D : ℝ) / (1 - a))) := by
  rw [hρ.isHermitian.trace_cfc_eq_sum_eigenvalues₀]
  exact Entropy.log_ordered_tail_le _ hρ.eigenvalues₀_nonneg
    hρ.isHermitian.eigenvalues₀_antitone hD ha ha1 ht

/-- The power form of Verstraete–Cirac Lemma 2, retaining its factor `1 - a`.
For trace-one operators the exponentiated quantity is the exponential of the
Rényi entropy with natural logarithms. No positivity of the tail is required. -/
theorem eigenvalue_tail_le_rpow (hρ : ρ.PosSemidef) {D : ℕ} (hD : 0 < D)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card ι) ↦ D ≤ i.val),
      hρ.isHermitian.eigenvalues₀ i) ≤
      ((1 - a) * Real.exp (Real.log (hρ.isHermitian.cfc (fun x ↦ x ^ a)).trace.re /
        (1 - a)) / D) ^ ((1 - a) / a) := by
  rw [hρ.isHermitian.trace_cfc_eq_sum_eigenvalues₀]
  exact Entropy.ordered_tail_le_rpow _ hρ.eigenvalues₀_nonneg
    hρ.isHermitian.eigenvalues₀_antitone hD ha ha1

/-- At order zero, `S₀ = log rank`: retaining at least the rank leaves no
spectral tail. This statement includes rank-zero operators and cutoff zero. -/
theorem eigenvalue_tail_eq_zero_of_rank_le (hρ : ρ.PosSemidef) {D : ℕ}
    (hD : ρ.rank ≤ D) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card ι) ↦ D ≤ i.val),
      hρ.isHermitian.eigenvalues₀ i) = 0 := by
  have hrank : ρ.rank =
      (Finset.univ.filter (fun i ↦ hρ.isHermitian.eigenvalues₀ i ≠ 0)).card := by
    rw [hρ.isHermitian.rank_eq_card_non_zero_eigs, ← Fintype.card_subtype]
    exact Fintype.card_congr
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm.subtypeEquiv
        (fun _ ↦ Iff.rfl))
  exact Entropy.ordered_tail_eq_zero_of_card_support_le _ hρ.eigenvalues₀_nonneg
    hρ.isHermitian.eigenvalues₀_antitone (hrank ▸ hD)

end Matrix.PosSemidef

end Tail

section MassBound

/-!
## Rényi entropy and concentration on a finite set

For order greater than one, a set carrying mass at least `1 - δ` must have
large cardinality if the Rényi entropy is large. All logarithms are natural.

Source: Schuch, Wolf, Verstraete and Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 333–345. The displayed lower bound in the source has an
incorrect plus sign before the absolute logarithm; the preceding power-sum
inequality gives the minus sign proved here.

**Local fix (error-term sign):** the correction is documented in TNLean's
[Rényi bond-dimension sign note](https://github.com/LionSR/TNLean/commit/ebf04b6495d29691ddefac5c85dd70ca6ba3bad6#diff-83cdf7e9f9eb1a229f1f7c212c73baa355968807efb4cef898c364519490b75a).
-/

open scoped BigOperators

namespace Entropy

/-- A finite set carrying mass at least `1 - δ` has the cardinality required by
the Rényi power sum of order `α > 1`. Normalization of the entire family is
unnecessary. Source: Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2,
lines 333–345, with the corrected sign of the error term. -/
theorem log_card_bound_of_renyi_mass {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (s : Finset ι) {D : ℕ}
    (hD : 0 < D) (hcard : s.card ≤ D) {α δ : ℝ} (hα : 1 < α)
    (hδ : δ < 1) (hmass : 1 - δ ≤ ∑ i ∈ s, p i) :
    Real.log (∑ i, p i ^ α) / (1 - α) +
      α / (α - 1) * Real.log (1 - δ) ≤ Real.log D := by
  have ha : 0 < α := lt_trans zero_lt_one hα
  have hd : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have ht : 0 < 1 - δ := sub_pos.mpr hδ
  have hj := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s (f := p) hα.le
    (fun i _ ↦ hp i)
  have hpow : (1 - δ) ^ α ≤ (D : ℝ) ^ (α - 1) * ∑ i, p i ^ α := by
    refine (Real.rpow_le_rpow ht.le hmass ha.le).trans (hj.trans ?_)
    apply mul_le_mul
    · exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hcard)
        (sub_nonneg.mpr hα.le)
    · exact Finset.sum_le_univ_sum_of_nonneg (fun i ↦ Real.rpow_nonneg (hp i) α)
    · exact Finset.sum_nonneg (fun i _ ↦ Real.rpow_nonneg (hp i) α)
    · positivity
  have hsum : 0 < ∑ i, p i ^ α := by
    have hprod : 0 < (D : ℝ) ^ (α - 1) * ∑ i, p i ^ α :=
      (Real.rpow_pos_of_pos ht α).trans_le hpow
    exact pos_of_mul_pos_right hprod (Real.rpow_nonneg hd.le _)
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos ht α) hpow
  rw [Real.log_rpow ht, Real.log_mul (by positivity) hsum.ne',
    Real.log_rpow hd] at hlog
  rw [show 1 - α = -(α - 1) by ring, div_neg, div_mul_eq_mul_div, ← neg_div,
    ← add_div]
  apply (div_le_iff₀ (sub_pos.mpr hα)).mpr
  linarith

/-- The corrected absolute-logarithm form of the Rényi cardinality bound.
Source: Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2, lines 333–345. -/
theorem renyi_mass_sub_error_le_log_card {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (s : Finset ι) {D : ℕ}
    (hD : 0 < D) (hcard : s.card ≤ D) {α δ : ℝ} (hα : 1 < α)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hmass : 1 - δ ≤ ∑ i ∈ s, p i) :
    Real.log (∑ i, p i ^ α) / (1 - α) -
      α / (α - 1) * |Real.log (1 - δ)| ≤ Real.log D := by
  have hlog : Real.log (1 - δ) ≤ 0 :=
    Real.log_nonpos (sub_pos.mpr hδ1).le (by linarith)
  simpa only [abs_of_nonpos hlog, mul_neg, sub_neg_eq_add] using
    log_card_bound_of_renyi_mass p hp s hD hcard hα hδ1 hmass

end Entropy

end MassBound

section RankLowerBound

/-!
## Rényi lower bounds for low-rank approximation

The order-greater-than-one bound in SWVC08, arXiv:0705.0292v2, lines 333–345,
with the corrected sign of the logarithmic error term. Only the original
positive matrix is normalized; the Hermitian approximant may have arbitrary trace.

**Local fix (error-term sign):** the correction is documented in TNLean’s
[Rényi bond-dimension sign note](https://github.com/LionSR/TNLean/commit/ebf04b6495d29691ddefac5c85dd70ca6ba3bad6#diff-83cdf7e9f9eb1a229f1f7c212c73baa355968807efb4cef898c364519490b75a).
-/

open scoped ComplexOrder

namespace Matrix

/-- A low-rank approximation in full trace norm forces a lower bound on its
rank budget. Source: SWVC08, arXiv:0705.0292v2, Eq. (eps-lower) and lines 333–345,
with the corrected sign of the error term. -/
theorem PosSemidef.renyiEntropy_add_log_error_le_log_rank
    {n D : ℕ} {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ : σ.IsHermitian)
    (hrank : σ.rank ≤ D) {α δ : ℝ} (hα : 1 < α) (hδ : δ < 1)
    (herror : traceNorm (ρ - σ) ≤ δ) :
    renyiEntropy ρ hρ.isHermitian α + α / (α - 1) * Real.log (1 - δ) ≤ Real.log D := by
  have htail := (hρ.sum_descEigenvalue_tail_le_traceNorm hσ hrank).trans herror
  let p := hρ.isHermitian.eigenvalues₀
  have hdesc (i : Fin (Fintype.card (Fin n))) :
      hρ.isHermitian.descEigenvalue i.val = p i := by
    simp only [IsHermitian.descEigenvalue, dite_eq_left i.isLt, p]
  have hp (i) : 0 ≤ p i := by
    rw [← hdesc i]
    exact hρ.descEigenvalue_nonneg i.val
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have hsum : ∑ i, p i = 1 := by
    simpa only [← Equiv.sum_comp e, IsHermitian.eigenvalues, e,
      Equiv.symm_apply_apply, p] using posSemidef_trace_one_eigenvalues_sum_one hρ hρ1
  have htail' : ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card (Fin n)) =>
      D ≤ i.val), p i ≤ δ := by
    simp_rw [← hdesc, Finset.sum_filter]
    rw [Fin.sum_univ_eq_sum_range (fun j => if D ≤ j then hρ.isHermitian.descEigenvalue j else 0)]
    have hset : (Finset.range n).filter (fun j => D ≤ j) = Finset.Ico D n := by
      ext j
      simp [and_comm]
    simpa only [Fintype.card_fin, ← Finset.sum_filter, hset] using htail
  let s := Finset.univ.filter (fun i : Fin (Fintype.card (Fin n)) => i.val < D)
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin (Fintype.card (Fin n)) => i.val < D) p
  have hmass : 1 - δ ≤ ∑ i ∈ s, p i := by
    simp only [not_lt, hsum] at hsplit
    dsimp only [s]
    linarith
  have hcard : s.card ≤ D := by
    simpa only [s, Fin.card_filter_val_lt] using (min_le_right (Fintype.card (Fin n)) D)
  have hD : 0 < D := by
    by_contra h
    have hzero : D = 0 := by omega
    simp only [s, hzero, Nat.not_lt_zero, Finset.filter_false, Finset.sum_empty] at hmass
    linarith
  have hbound := Entropy.log_card_bound_of_renyi_mass p hp s hD hcard hα hδ hmass
  simpa only [renyiEntropy, ite_eq_right (show α ≠ 0 by linarith), ite_eq_right (ne_of_gt hα),
    hρ.isHermitian.trace_cfc_eq_sum_eigenvalues₀, p, div_eq_mul_inv, mul_comm] using hbound

/-- The Rényi rank lower bound for an arbitrary finite index set, measured in
full trace norm. Source: SWVC08, arXiv:0705.0292v2, Eq. (eps-lower) and
lines 333–345, with the corrected sign of the error term. -/
theorem PosSemidef.renyiEntropy_add_log_error_le_log_rank_of_rectangularTraceNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ} {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ : σ.IsHermitian)
    (hrank : σ.rank ≤ D) {α δ : ℝ} (hα : 1 < α) (hδ : δ < 1)
    (herror : rectangularTraceNorm (ρ - σ) ≤ δ) :
    renyiEntropy ρ hρ.isHermitian α + α / (α - 1) * Real.log (1 - δ) ≤ Real.log D := by
  let e := Fintype.equivFin ι
  have hr := hρ.submatrix e.symm
  have he : traceNorm (ρ.submatrix e.symm e.symm - σ.submatrix e.symm e.symm) ≤ δ := by
    change rectangularTraceNorm (reindex e e (ρ - σ)) ≤ δ
    simpa only [rectangularTraceNorm_reindex] using herror
  have hb := hr.renyiEntropy_add_log_error_le_log_rank
    (by simpa only [trace_submatrix_equiv] using hρ1) (hσ.submatrix e.symm)
    (by simpa only [rank_submatrix] using hrank) hα hδ he
  simpa only [renyiEntropy, ite_eq_right (show α ≠ 0 by linarith),
    ite_eq_right (ne_of_gt hα), ← IsHermitian.cfc_eq, cfc_submatrix_equiv hρ.isHermitian _ e,
    trace_submatrix_equiv] using hb

end Matrix

end RankLowerBound
