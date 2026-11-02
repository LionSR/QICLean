/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Scalar soft truncation

This file defines the finite exponential soft truncation used in the
one-dimensional area-law argument and proves its scalar approximation bounds.

## References

* ALVV, arXiv:1602.08828v2, lines 1152–1173.
-/

open scoped BigOperators

namespace Real

private noncomputable def softTruncationUnit (m : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, (1 - exp (-y)) ^ (j + 1) / (j + 1 : ℝ)

private theorem hasDerivAt_softTruncationUnit (m : ℕ) (y : ℝ) :
    HasDerivAt (softTruncationUnit m) (1 - (1 - exp (-y)) ^ m) y := by
  unfold softTruncationUnit
  have ha : HasDerivAt (fun z : ℝ ↦ 1 - exp (-z)) (exp (-y)) y := by
    convert (hasDerivAt_const y 1).sub
      ((Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y)) using 1 <;>
      simp only [Function.comp_def, mul_neg, mul_one, sub_neg_eq_add, zero_add]
    ext z
    rfl
  convert HasDerivAt.fun_sum (u := Finset.range m) (A := fun j z ↦
      (1 - exp (-z)) ^ (j + 1) / (j + 1 : ℝ)) (A' := fun j ↦
      (1 - exp (-y)) ^ j * exp (-y)) (fun j _ ↦ ?_) using 1
  · rw [← Finset.sum_mul]
    simpa only [sub_sub_cancel] using (geom_sum_mul_neg (1 - exp (-y)) m).symm
  · convert (ha.pow (j + 1)).div_const (j + 1 : ℝ) using 1
    field_simp
    rw [Nat.add_sub_cancel]
    push_cast
    ring

private theorem one_sub_exp_neg_bounds {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ 1 - exp (-y) ∧ 1 - exp (-y) ≤ 1 ∧ 1 - exp (-y) ≤ y := by
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy))
  constructor
  · linarith [Real.exp_pos (-y)]
  · linarith [Real.one_sub_le_exp_neg y]

private theorem softTruncationUnit_error_le (m : ℕ) (hm : 1 ≤ m) {y : ℝ} (hy : 0 ≤ y) :
    y - softTruncationUnit m y ≤ y ^ m / (m : ℝ) := by
  let q : ℝ → ℝ := fun z ↦ softTruncationUnit m z - z + z ^ m / (m : ℝ)
  have hderiv (z : ℝ) :
      HasDerivAt q (z ^ (m - 1) - (1 - exp (-z)) ^ m) z := by
    dsimp only [q]
    convert ((hasDerivAt_softTruncationUnit m z).sub (hasDerivAt_id z)).add
      (((hasDerivAt_id z).pow m).div_const (m : ℝ)) using 1
    · ext w
      simp [div_eq_mul_inv]
    · simp only [id_eq]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)]
      ring
  have hmono : MonotoneOn q (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Ici 0) (convex_Ici 0)
      (continuousOn_of_forall_continuousAt fun z _ ↦ (hderiv z).continuousAt)
    · intro z _hz
      exact (hderiv z).hasDerivWithinAt
    · intro z hz
      rw [interior_Ici] at hz
      have hz0 : 0 ≤ z := le_of_lt hz
      obtain ⟨ha0, ha1, haz⟩ := one_sub_exp_neg_bounds hz0
      apply sub_nonneg.mpr
      calc
        (1 - exp (-z)) ^ m ≤ (1 - exp (-z)) ^ (m - 1) :=
          pow_le_pow_of_le_one ha0 ha1 (Nat.sub_le m 1)
        _ ≤ z ^ (m - 1) := pow_le_pow_left₀ ha0 haz _
  have hq0 : q 0 = 0 := by
    simp [q, softTruncationUnit, Nat.ne_of_gt hm]
  have hq := hmono (by simp) hy hy
  rw [hq0] at hq
  dsimp only [q] at hq
  linarith

private theorem softTruncationUnit_nonneg (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ softTruncationUnit m y := by
  unfold softTruncationUnit
  apply Finset.sum_nonneg
  intro j _hj
  exact div_nonneg (pow_nonneg (one_sub_exp_neg_bounds hy).1 _) (by positivity)

private theorem softTruncationUnit_le_self (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    softTruncationUnit m y ≤ y := by
  let r : ℝ → ℝ := fun z ↦ z - softTruncationUnit m z
  have hderiv (z : ℝ) : HasDerivAt r ((1 - exp (-z)) ^ m) z := by
    dsimp only [r]
    convert (hasDerivAt_id z).sub (hasDerivAt_softTruncationUnit m z) using 1
    · ext w
      rfl
    · ring
  have hmono : MonotoneOn r (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Ici 0) (convex_Ici 0)
      (continuousOn_of_forall_continuousAt fun z _ ↦ (hderiv z).continuousAt)
    · intro z _hz
      exact (hderiv z).hasDerivWithinAt
    · intro z hz
      rw [interior_Ici] at hz
      exact pow_nonneg (one_sub_exp_neg_bounds (le_of_lt hz)).1 _
  have hr0 : r 0 = 0 := by simp [r, softTruncationUnit]
  have hr := hmono (by simp) hy hy
  rw [hr0] at hr
  exact sub_nonneg.mp hr

private theorem softTruncationUnit_le_log (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    softTruncationUnit m y ≤ 1 + log (m : ℝ) := by
  obtain ⟨ha0, ha1, _hay⟩ := one_sub_exp_neg_bounds hy
  calc
    softTruncationUnit m y ≤
        ∑ j ∈ Finset.range m, 1 / (j + 1 : ℝ) := by
      unfold softTruncationUnit
      apply Finset.sum_le_sum
      intro j _hj
      exact div_le_div_of_nonneg_right (pow_le_one₀ ha0 ha1) (by positivity)
    _ = (harmonic m : ℝ) := by
      simp [harmonic, div_eq_mul_inv]
    _ ≤ 1 + log (m : ℝ) := harmonic_le_one_add_log m

/-- The order-`m` scalar soft truncation at scale `t`.

This is the finite series from ALVV, arXiv:1602.08828v2, lines 1152–1173,
written as a function of the nonnegative scalar being truncated.

**Local fix (logarithmic upper bound):** the printed bound `t * log m` is
false for every order `m ≥ 1`: as `x → ∞` the truncation tends to `t * H_m`,
and the harmonic number satisfies `H_m > log m`. The corrected bound
`t * (1 + log m)` is what is proved; see
`docs/paper-gaps/alvv16_soft_truncation_log_bound.tex`. -/
noncomputable def softTruncation (t : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  t * ∑ j ∈ Finset.range m,
    (1 - exp (-(x / t))) ^ (j + 1) / (j + 1 : ℝ)

/-- The scalar soft truncation is nonnegative, lies below its input, has a
polynomial remainder, and is bounded by the corrected harmonic estimate.

ALVV, arXiv:1602.08828v2, lines 1152–1173. The paper prints the final upper
bound as `t * log m`, which is false for every order `m ≥ 1` (the limit as
`x → ∞` is `t * H_m > t * log m`); the source-faithful local
repair `t * (1 + log m)` is documented in
`docs/paper-gaps/alvv16_soft_truncation_log_bound.tex`. -/
theorem softTruncation_bounds (t : ℝ) (m : ℕ) (x : ℝ)
    (ht : 0 < t) (hm : 1 ≤ m) (hx : 0 ≤ x) :
    0 ≤ softTruncation t m x ∧
      softTruncation t m x ≤ x ∧
      x - softTruncation t m x ≤ (t / (m : ℝ)) * (x / t) ^ m ∧
      softTruncation t m x ≤ t * (1 + log (m : ℝ)) := by
  have hy : 0 ≤ x / t := div_nonneg hx ht.le
  have hnonneg := softTruncationUnit_nonneg m hy
  have hself := softTruncationUnit_le_self m hy
  have herror := softTruncationUnit_error_le m hm hy
  have hlog := softTruncationUnit_le_log m hy
  change 0 ≤ t * softTruncationUnit m (x / t) ∧
    t * softTruncationUnit m (x / t) ≤ x ∧
    x - t * softTruncationUnit m (x / t) ≤ (t / (m : ℝ)) * (x / t) ^ m ∧
    t * softTruncationUnit m (x / t) ≤ t * (1 + log (m : ℝ))
  constructor
  · exact mul_nonneg ht.le hnonneg
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hself ht.le
    convert hmul using 1
    field_simp [ht.ne']
  constructor
  · have hmul := mul_le_mul_of_nonneg_left herror ht.le
    convert hmul using 1 <;>
      field_simp [ht.ne', Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)]
  · exact mul_le_mul_of_nonneg_left hlog ht.le

private theorem softTruncationUnit_remainder_le_geometric (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y - softTruncationUnit m y ≤ y * (1 - exp (-y)) ^ m := by
  let r : ℝ → ℝ := fun z ↦ z - softTruncationUnit m z
  have hderiv (z : ℝ) : HasDerivAt r ((1 - exp (-z)) ^ m) z := by
    simpa only [r, id_eq, sub_sub_cancel] using
      (hasDerivAt_id z).fun_sub (hasDerivAt_softTruncationUnit m z)
  have hle (z : ℝ) (hz : z ∈ Set.Icc 0 y) :
      deriv r z ≤ (1 - exp (-y)) ^ m := by
    rw [(hderiv z).deriv]
    exact pow_le_pow_left₀ (one_sub_exp_neg_bounds hz.1).1
      (sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hz.2)) 1) m
  have hb := (convex_Icc (0 : ℝ) y).image_sub_le_mul_sub_of_deriv_le
    (fun z _ ↦ (hderiv z).continuousAt.continuousWithinAt)
    (fun z _ ↦ (hderiv z).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ hle z (interior_subset hz)) 0 ⟨le_rfl, hy⟩ y ⟨hy, le_rfl⟩ hy
  simpa [r, softTruncationUnit, mul_comm] using hb

/-- A geometric remainder bound for the scalar soft truncation. This is an
auxiliary consequence of the defining series in ALVV, arXiv:1602.08828v2,
lines 1152–1173. -/
lemma softTruncation_remainder_le_geometric (t : ℝ) (m : ℕ) (x : ℝ)
    (ht : 0 < t) (hx : 0 ≤ x) :
    x - softTruncation t m x ≤ x * (1 - exp (-(x / t))) ^ m := by
  have hb := mul_le_mul_of_nonneg_left
    (softTruncationUnit_remainder_le_geometric m (div_nonneg hx ht.le)) ht.le
  change x - t * softTruncationUnit m (x / t) ≤ x * (1 - exp (-(x / t))) ^ m
  simpa only [mul_sub, ← mul_assoc, mul_div_cancel₀ _ ht.ne'] using hb

/-- An exponential weight controls the soft-truncation error when its order
and scale agree. This bound is independent of the input scalar; it can be
integrated against a spectral measure with a controlled exponential moment.
It is an auxiliary estimate for the soft truncation defined in ALVV,
arXiv:1602.08828v2, lines 1152–1173. -/
lemma softTruncation_remainder_le_exp (m : ℕ) (hm : 0 < m)
    (theta x : ℝ) (htheta : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    (hx : 0 ≤ x) :
    x - softTruncation (m : ℝ) m x ≤
      (2 / theta) * exp (theta * x - theta * m / 2) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hw (s : ℝ) (hs : 0 < s) (z : ℝ) : z ≤ (1 / s) * exp (s * z) := by
    rw [one_div_mul_eq_div, le_div_iff₀ hs]
    nlinarith [Real.add_one_le_exp (s * z)]
  by_cases hxm : x ≤ (m : ℝ)
  · have hr : 1 - exp (-(x / (m : ℝ))) ≤ exp (-theta / 2) := by
      have hs := Real.exp_le_exp.mpr (neg_le_neg ((div_le_one hmR).mpr hxm))
      linarith [Real.exp_neg_one_gt_d9, Real.add_one_le_exp (-theta / 2)]
    have hp := pow_le_pow_left₀ (one_sub_exp_neg_bounds (div_nonneg hx hmR.le)).1 hr m
    rw [← Real.exp_nat_mul] at hp
    refine (softTruncation_remainder_le_geometric (m : ℝ) m x hmR hx).trans ?_
    refine (mul_le_mul_of_nonneg_left hp hx).trans ?_
    refine (mul_le_mul_of_nonneg_right (hw theta htheta x)
      (Real.exp_pos ((m : ℝ) * (-theta / 2))).le).trans ?_
    rw [mul_assoc, ← Real.exp_add,
      show theta * x + (m : ℝ) * (-theta / 2) = theta * x - theta * m / 2 by ring]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by norm_num) htheta.le)
      (Real.exp_pos _).le
  · refine (sub_le_self x (softTruncation_bounds (m : ℝ) m x hmR hm hx).1).trans ?_
    refine (hw (theta / 2) (half_pos htheta) x).trans ?_
    rw [div_div_eq_mul_div, one_mul]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
      (div_nonneg (by norm_num) htheta.le)
    nlinarith [mul_le_mul_of_nonneg_left (lt_of_not_ge hxm).le htheta.le]

/-- Soft truncation is increasing on the nonnegative half-line. This follows
term by term from the finite series in ALVV, arXiv:1602.08828v2,
lines 1152–1173. -/
lemma monotoneOn_softTruncation (t : ℝ) (m : ℕ) (ht : 0 < t) :
    MonotoneOn (softTruncation t m) (Set.Ici 0) := by
  intro x hx y _hy hxy
  unfold softTruncation
  apply mul_le_mul_of_nonneg_left _ ht.le
  apply Finset.sum_le_sum
  intro j _hj
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀
    (one_sub_exp_neg_bounds (div_nonneg hx ht.le)).1
    (sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_right hxy ht.le))) 1) _

/-- Below half the scale, the geometric remainder is uniformly small.
Auxiliary to ALVV, arXiv:1602.08828v2, lines 1152–1173. -/
private theorem softTruncation_remainder_le_half (t : ℝ) (m : ℕ) (x : ℝ)
    (ht : 0 < t) (hx : 0 ≤ x) (hxc : x ≤ t / 2) :
    x - softTruncation t m x ≤ (t / 2) * (1 / 2 : ℝ) ^ m := by
  refine (softTruncation_remainder_le_geometric t m x ht hx).trans ?_
  apply mul_le_mul hxc ?_
    (pow_nonneg (one_sub_exp_neg_bounds (div_nonneg hx ht.le)).1 _) (by positivity)
  apply pow_le_pow_left₀
    (one_sub_exp_neg_bounds (div_nonneg hx ht.le)).1
  have hdiv : x / t ≤ 1 / 2 := (div_le_iff₀ ht).mpr (by linarith)
  exact (one_sub_exp_neg_bounds (div_nonneg hx ht.le)).2.2.trans hdiv

/-- Soft truncation lies above hard truncation at half its scale, up to an
exponentially small scalar error. This is an auxiliary corrected estimate for
ALVV, arXiv:1602.08828v2, lines 1152–1173; it does not assert the printed
uniform energy estimate in equation `eq:exp-approx-0`. -/
lemma softTruncation_hard_bounds (t : ℝ) (m : ℕ) (x : ℝ)
    (ht : 0 < t) (hm : 1 ≤ m) (hx : 0 ≤ x) :
    min x (t / 2) - (t / 2) * (1 / 2 : ℝ) ^ m ≤ softTruncation t m x ∧
      softTruncation t m x ≤ x := by
  refine ⟨?_, (softTruncation_bounds t m x ht hm hx).2.1⟩
  by_cases hxc : x ≤ t / 2
  · simpa only [min_eq_left hxc] using
      (sub_le_comm.mp (softTruncation_remainder_le_half t m x ht hx hxc))
  · simpa only [min_eq_right (le_of_not_ge hxc)] using
      (sub_le_comm.mp (softTruncation_remainder_le_half t m (t / 2) ht
        (half_pos ht).le le_rfl)).trans
        (monotoneOn_softTruncation t m ht (half_pos ht).le hx (le_of_not_ge hxc))

end Real
