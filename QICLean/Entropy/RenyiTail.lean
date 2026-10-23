/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Order.Interval.Finset.Fin
import QICLean.Analysis.TraceCFC
import Mathlib.Analysis.Matrix.PosDef

/-!
# Rényi bounds for ordered spectral tails

Verstraete–Cirac, arXiv:cond-mat/0505140v6, Lemma 2 (`convexPRA2.tex`, lines 335–352).
The proof bounds the power sum directly at a cutoff weight and applies weighted AM–GM.
It does not require the extremizing distribution asserted in the source proof.
All logarithms are natural. The logarithmic estimate requires a positive tail; the
power estimate also includes zero tails. Order zero is treated separately by rank.
-/

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
