/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SoftFamilyCalibration

/-! # Scalar order estimates for the calibrated soft family

The denominator of the geometric cutoff is independent of the width and length.
The nested logarithm in its numerator can be bounded by ordinary logarithms of
the heat weight and error budget. For fixed local dimension and positive width
coefficient, the resulting scalar size and bond dimension ceilings have logarithms
of degree at most 36 and 104 in one plus the logarithm of the length. -/

namespace Real

private theorem soft_half_le_log_one_add {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    x / 2 ≤ log (1 + x) := by
  refine le_trans ?_ (le_log_one_add_of_nonneg hx)
  apply (le_div_iff₀ (by positivity : 0 < x + 2)).mpr
  have h := mul_nonpos_of_nonneg_of_nonpos hx (show x - 2 ≤ 0 by linarith only [hx'])
  nlinarith only [h]

/-- Linearize the nested logarithm in the actual natural cluster order.
The natural ceiling and lower cutoff together cost at most one. -/
theorem soft_cluster_order_le_log_budget {b W xi : ℝ} (hb : 0 < b) (hb' : b < 1)
    (hxi : 0 < xi) (hW : xi ≤ W) {N : ℕ} (hN : 1 ≤ N) :
    let r := max 1 ⌈(log (max 1 ((N : ℝ) ^ 2)) - log (log (1 + xi / W))) / (-log b)⌉₊
    (r : ℝ) ≤ 1 + (2 * log N + log 2 + log W - log xi) / (-log b) := by
  intro r
  have hp := hxi.trans_le hW
  have hd := neg_pos.mpr (log_neg hb hb')
  have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hsmall := soft_half_le_log_one_add (div_nonneg hxi.le hp.le)
    ((div_le_one hp).2 hW)
  have hlog := log_le_log (by positivity : 0 < xi / W / 2) hsmall
  rw [log_div (by positivity) (by norm_num), log_div hxi.ne' hp.ne'] at hlog
  have hnum : 0 ≤ 2 * log N + log 2 + log W - log xi := by
    linarith only [log_nonneg hNr, log_nonneg (by norm_num : (1:ℝ) ≤ 2), log_le_log hxi hW]
  dsimp only [r]
  rw [max_eq_right (one_le_pow₀ hNr), log_pow, Nat.cast_max, Nat.cast_one]
  push_cast
  have hquot := div_le_div_of_nonneg_right
    (show 2 * log N - log (log (1 + xi / W)) ≤ 2 * log N + log 2 + log W - log xi by
      linarith only [hlog]) hd.le
  have hz := div_nonneg hnum hd.le
  apply max_le (by linarith only [hz])
  by_cases hn : 0 ≤ (2 * log N - log (log (1 + xi / W))) / (-log b)
  · linarith only [Nat.ceil_lt_add_one hn, hquot]
  · rw [Nat.ceil_eq_zero.mpr (le_of_not_ge hn), Nat.cast_zero]
    linarith only [hz]

/-- Exact logarithmic cost of the low-density error allocation, including its cap. -/
theorem soft_error_log_budget {D M g : ℝ} (hD : 0 < D) (hM : 0 < M) (hg : 0 < g) :
    let tau := 1 / (D ^ 24 * M ^ 10)
    let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
    (-log xi) = max 0 (24 * log D + 10 * log M - 2 * log g + log 20000 + log (M + g + 8)) := by
  intro tau xi
  let z := tau * g ^ 2 / (20000 * (M + g + 8))
  have ht : 0 < tau := by dsimp [tau]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have he : -log z = 24 * log D + 10 * log M - 2 * log g + log 20000 + log (M + g + 8) := by
    dsimp only [z, tau]
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by norm_num) (by positivity), one_div, log_inv,
      log_mul (by positivity) (by positivity)]
    simp only [log_pow, Nat.cast_ofNat]
    ring
  change -log (min 1 z) = _
  rw [← he]
  by_cases hz1 : 1 ≤ z
  · rw [min_eq_left hz1, log_one, neg_zero, max_eq_left (neg_nonpos.mpr (log_nonneg hz1))]
  · rw [min_eq_right (le_of_not_ge hz1), max_eq_right (neg_nonneg.mpr
      (log_nonpos hz.le (le_of_not_ge hz1)))]

private theorem soft_cluster_base_lt_one : 2 * (exp (1 / 3 : ℝ) - 1) < 1 := by
  have h : exp (1 / 3 : ℝ) ^ 3 < 3 := by
    rw [← exp_nat_mul]
    norm_num
    exact exp_one_lt_three
  by_contra! hbad
  have hp : (3 / 2 : ℝ) ^ 3 ≤ exp (1 / 3 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) _
  linarith

/-- Specialize the cutoff estimate at the very scale meeting the soft calibration
threshold. The remaining terms expose the logarithms of the heat weight and budget. -/
theorem exists_soft_scale_cluster_order (q N : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N)
    {μ : ℝ} (hμ : 0 < μ) (hw : μ / (3 * log N) ≤ 1) :
    let w := μ / (3 * log N)
    let g := w ^ 2 / 2
    ∃ u : ℕ, 2 ≤ u ∧ softFamilyThreshold q g 24 10 10 ≤ u ∧
      (u : ℝ) ≤ ((64 * (5000000 + 1440 * (q : ℝ))) ^ 2 + 2) * (1 + w⁻¹) ^ 4 ∧
      let ell := u ^ 8
      let m := u ^ 10
      let k := u ^ 16
      let t := 3 * (m : ℝ)
      let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
      let M := 3 * t * (1 + log m) + 4 * (ell : ℝ) + 34
      let tau := 1 / ((D : ℝ) ^ 24 * M ^ 10)
      let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
      let b := 2 * (exp (1 / 3 : ℝ) - 1)
      let W := t * 2 ^ (m + 1)
      let r := max 1 ⌈(log (max 1 ((N : ℝ) ^ 2)) - log (log (1 + xi / W))) / (-log b)⌉₊
      (r : ℝ) ≤ 1 + (2 * log N + log 2 + log t + (m + 1 : ℕ) * log 2 +
        max 0 (24 * log D + 10 * log M - 2 * log g + log 20000 + log (M + g + 8))) / (-log b) := by
  intro w g
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hlog := log_pos hNr
  have hw0 : 0 < w := div_pos hμ (by positivity)
  have hg : 0 < g := by dsimp [g]; positivity
  obtain ⟨u, hu, hth, hub⟩ := exists_soft_family_scale_half_sq q hq hw0 hw
  refine ⟨u, hu, hth, hub, ?_⟩
  intro ell m k t D M tau xi b W r
  obtain ⟨_, hm, _, _, _, _, hD, hM, _, _, hxi, hxi1, _⟩ :=
    soft_family_calibration_of_threshold q hq g hg 24 10 10 u hu hth
  change 2 ≤ m at hm
  change 0 < xi at hxi
  change xi ≤ 1 at hxi1
  have ht : 1 ≤ t := by
    dsimp only [t]
    have hmR : 2 ≤ (m : ℝ) := by exact_mod_cast hm
    linarith only [hmR]
  have ht0 := zero_lt_one.trans_le ht
  have hW : xi ≤ W := hxi1.trans (one_le_mul_of_one_le_of_one_le ht (one_le_pow₀ (by norm_num)))
  have hb : 0 < b := by
    dsimp [b]
    have := (one_lt_exp_iff).2 (by norm_num : 0 < (1 / 3 : ℝ))
    linarith
  have h := soft_cluster_order_le_log_budget hb soft_cluster_base_lt_one hxi hW
    (show 1 ≤ N by omega)
  change (r : ℝ) ≤ 1 + (2 * log N + log 2 + log W - log xi) / (-log b) at h
  change 1 ≤ D at hD
  change 1 ≤ M at hM
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hcost := soft_error_log_budget hDpos (zero_lt_one.trans_le hM) hg
  change -log xi = _ at hcost
  rw [sub_eq_add_neg, hcost] at h
  simpa only [W, log_mul ht0.ne' (by positivity : (2:ℝ) ^ (m + 1) ≠ 0), log_pow,
    add_assoc] using h

private theorem soft_scale_le_log_four {μ L H : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L)
    (hH : 0 ≤ H) {u : ℕ} (hu : (u : ℝ) ≤ H * (1 + (μ / (3 * L))⁻¹) ^ 4) :
    (u : ℝ) ≤ (H * (1 + 3 / μ) ^ 4) * (1 + L) ^ 4 := by
  have h₁ : 0 ≤ 3 / μ := by positivity
  have h₂ : 1 + (μ / (3 * L))⁻¹ ≤ (1 + 3 / μ) * (1 + L) := by
    rw [inv_div]
    nlinarith only [h₁, hL, show 3 * L / μ = (3 / μ) * L by ring]
  apply hu.trans
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h₂ _) hH

/-- Translate the inverse-width bound for any given calibration witness into
length bounds for its soft order and filter degree. -/
theorem soft_orders_le_log_powers {μ L H : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L)
    (hH : 0 ≤ H) {u : ℕ} (hu : (u : ℝ) ≤ H * (1 + (μ / (3 * L))⁻¹) ^ 4) :
    let A := H * (1 + 3 / μ) ^ 4
    ((u ^ 10 : ℕ) : ℝ) ≤ A ^ 10 * (1 + L) ^ 40 ∧
      ((u ^ 16 : ℕ) : ℝ) ≤ A ^ 16 * (1 + L) ^ 64 := by
  intro A
  have hscale := soft_scale_le_log_four hμ hL hH hu
  constructor <;> push_cast
  · exact (pow_le_pow_left₀ (Nat.cast_nonneg u) hscale 10).trans_eq (by rw [mul_pow, ← pow_mul])
  · exact (pow_le_pow_left₀ (Nat.cast_nonneg u) hscale 16).trans_eq (by rw [mul_pow, ← pow_mul])

/-- For the TN member-bond expression, order and soft-order bounds of degree
40 and a filter-degree bound of degree 64 yield the scalar exponent 104. -/
theorem soft_member_bond_le_exp {r m k q : ℕ} (hr : 1 ≤ r) (hq : 1 ≤ q)
    {X A K : ℝ} (hX : 1 ≤ X) (hA : 1 ≤ A)
    (hrX : (r : ℝ) ≤ A * X ^ 40) (hmX : (m : ℝ) ≤ A * X ^ 40)
    (hkX : (k : ℝ) ≤ K * X ^ 64) :
    let B := ((r ^ 2 * q ^ r) * 2) * (m + 1)
    ((max 1 B : ℕ) : ℝ) ^ (2 * k) ≤ exp ((2 * K * (6 + log q) * A) * X ^ 104) := by
  intro B
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hB0 : 0 < B := by dsimp [B]; positivity
  rw [max_eq_right hB0, ← exp_log (by positivity : 0 < (B : ℝ) ^ (2 * k))]
  apply exp_le_exp.mpr
  rw [log_pow]
  have hform : log (B : ℝ) =
      2 * log r + r * log q + log 2 + log ((m : ℝ) + 1) := by
    dsimp only [B]
    push_cast
    rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by norm_num),
      log_mul (by positivity) (by positivity), log_pow, log_pow]
    norm_num
  have hAX : 1 ≤ A * X ^ 40 := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hX)
  have hlogq := log_nonneg (by exact_mod_cast hq : 1 ≤ (q : ℝ))
  have hlogB : log (B : ℝ) ≤ (6 + log q) * A * X ^ 40 := by
    rw [hform]
    nlinarith only [log_le_sub_one_of_pos hr0, log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ)),
      log_le_sub_one_of_pos (by positivity : 0 < (m : ℝ) + 1), hrX, hmX, hAX,
      mul_le_mul_of_nonneg_right hrX hlogq]
  push_cast
  calc
    _ ≤ (2 * (K * X ^ 64)) * ((6 + log q) * A * X ^ 40) :=
      mul_le_mul (by linarith only [hkX]) hlogB (log_nonneg (by exact_mod_cast hB0 : 1 ≤ (B : ℝ)))
        (by nlinarith only [hkX, (Nat.cast_nonneg k : (0:ℝ) ≤ k)])
    _ = _ := by ring

private theorem soft_member_costs {q u : ℕ} {g : ℝ} (hq : 2 ≤ q) (hu : 2 ≤ u)
    (hg : 0 < g) (hth : softFamilyThreshold q g 24 10 10 ≤ u) :
    let ell := u ^ 8
    let m := u ^ 10
    let k := u ^ 16
    let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
    let t := 3 * (m : ℝ)
    let M := 3 * t * (1 + log m) + 4 * (ell : ℝ) + 34
    log D ≤ (u : ℝ) ^ 9 ∧ log 2 + log t + (m + 1 : ℕ) * log 2 +
      max 0 (24 * log D + 10 * log M - 2 * log g + log 20000 + log (M + g + 8))
        ≤ 20100 * m := by
  intro ell m k D t M
  obtain ⟨_, _, _, _, _, _, hD, hM, hupper, hbudget⟩ :=
    soft_family_log_budgets_of_threshold q hq g hg 24 10 10 u hu hth
  have hu0 : 0 < u := by omega
  have hv : 1 ≤ (u : ℝ) := by exact_mod_cast (by omega : 1 ≤ u)
  have hdiv : u ^ 16 / u ^ 8 = u ^ 8 := by
    rw [show u ^ 16 = u ^ 8 * u ^ 8 by ring, Nat.mul_div_cancel_left _ (pow_pos hu0 _)]
  have hDf : (D : ℝ) =
      ((u : ℝ) ^ 26 + 1) * ((q : ℝ) * (u : ℝ) ^ 16) ^ (40 * u ^ 8) := by
    dsimp only [D, m, k, ell]
    rw [show u ^ 10 * u ^ 16 = u ^ 26 by ring, hdiv,
      show 36 * u ^ 8 + 4 * u ^ 8 = 40 * u ^ 8 by ring]
    push_cast
    rfl
  have hMf : M = 9 * (u : ℝ) ^ 10 * (1 + 10 * log (u : ℝ)) + 4 * (u : ℝ) ^ 8 + 34 := by
    dsimp only [M, t, m, ell]
    push_cast
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [← hDf] at hD hbudget
  rw [← hMf] at hM hupper hbudget
  norm_num only [Nat.cast_ofNat] at hbudget
  have hd := log_nonneg hD
  have he := log_nonneg hM
  have ha := abs_nonneg (log (g / 2000000))
  have hab := neg_le_abs (log (g / 2000000))
  rw [log_div hg.ne' (by norm_num)] at hab ha hbudget
  have hlg := log_nonneg (by norm_num : (1:ℝ) ≤ 2000000)
  have hm : (m : ℝ) = (u : ℝ) ^ 10 := by simp [m]
  have hv9 : (u : ℝ)^9 ≤ m := hm ▸ pow_le_pow_right₀ hv (by decide)
  have hv1 : (u : ℝ) ≤ m := hm ▸ (by simpa using pow_le_pow_right₀ hv (by decide : 1 ≤ 10))
  have h12 := one_le_pow₀ hv (n := 12)
  have hplus := log_le_log (by linarith : 0 < M + g + 8)
    (show M + g + 8 ≤ 4 * (u : ℝ)^12 by linarith only [hupper, h12])
  rw [log_mul (by norm_num) (by positivity), log_pow] at hplus
  norm_num only [Nat.cast_ofNat] at hplus
  have hlogu := log_le_sub_one_of_pos (zero_lt_one.trans_le hv)
  have hlog4 := log_le_sub_one_of_pos (by norm_num : 0 < (4 : ℝ))
  have hlog2 := log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
  have h20 := log_le_sub_one_of_pos (by norm_num : 0 < (20000 : ℝ))
  have ht := log_le_sub_one_of_pos (by dsimp [t]; positivity : 0 < t)
  change log t ≤ 3 * (m : ℝ) - 1 at ht
  have hm2 : 0 ≤ (m : ℝ) + 1 := by positivity
  have hl2 := mul_le_mul_of_nonneg_left hlog2 hm2
  push_cast
  constructor
  · linarith only [hbudget, ha, hd, he, hg, pow_nonneg (zero_le_one.trans hv) 9]
  · rw [add_max]
    apply max_le <;> linarith only [ht, hl2, hlog2, hbudget, hv9, hv1, hv, hd, he, hg,
      hplus, hlogu, hlog4, h20, hab, hlg, ha]

/-- Uniform scalar bounds for the cardinality ceiling and the member-bond ceiling
of the low-density family. Both estimates use the witness meeting the calibration
threshold. Geometric hypotheses needed to construct the physical family are separate. -/
theorem exists_soft_family_scalar_growth (q : ℕ) (hq : 2 ≤ q) {μ : ℝ} (hμ : 0 < μ) :
    ∃ Csize Cbond : ℝ, ∀ N : ℕ, 2 ≤ N → μ / (3 * log N) ≤ 1 →
      let w := μ / (3 * log N)
      let g := w ^ 2 / 2
      let X := 1 + log N
      ∃ u : ℕ, 2 ≤ u ∧ softFamilyThreshold q g 24 10 10 ≤ u ∧
        let ell := u ^ 8
        let m := u ^ 10
        let k := u ^ 16
        let t := 3 * (m : ℝ)
        let D := (m * k + 1) * (q * k) ^ (36 * ell + 4 * (k / ell))
        let M := 3 * t * (1 + log m) + 4 * (ell : ℝ) + 34
        let tau := 1 / ((D : ℝ) ^ 24 * M ^ 10)
        let xi := min 1 (tau * g ^ 2 / (20000 * (M + g + 8)))
        let b := 2 * (exp (1 / 3 : ℝ) - 1)
        let W := t * 2 ^ (m + 1)
        let r := max 1 ⌈(log (max 1 ((N : ℝ) ^ 2)) - log (log (1 + xi / W))) / (-log b)⌉₊
        let B := ((r ^ 2 * q ^ r) * 2) * (m + 1)
        (D : ℝ) ≤ exp (Csize * X ^ 36) ∧
          ((max 1 B : ℕ) : ℝ) ^ (2 * k) ≤ exp (Cbond * X ^ 104) := by
  let H := (64 * (5000000 + 1440 * (q : ℝ))) ^ 2 + 2
  let A := H * (1 + 3 / μ) ^ 4
  let b := 2 * (exp (1 / 3 : ℝ) - 1)
  let d := -log b
  let R := max (A ^ 10) (1 + (2 + 20100 * A ^ 10) / d)
  have hb : 0 < b := by
    have := one_lt_exp_iff.mpr (by norm_num : 0 < (1 / 3 : ℝ))
    dsimp [b]
    linarith
  have hd : 0 < d := neg_pos.mpr (log_neg hb soft_cluster_base_lt_one)
  have hA : 0 ≤ A := by dsimp [A, H]; positivity
  have hR : 1 ≤ R := by
    apply le_trans _ (le_max_right _ _)
    exact le_add_of_nonneg_right (by positivity)
  refine ⟨A ^ 9, 2 * A ^ 16 * (6 + log q) * R, ?_⟩
  intro N hN hw w g X
  have hL := log_pos (by exact_mod_cast (show 1 < N by omega) : (1 : ℝ) < N)
  have hX : 1 ≤ X := le_add_of_nonneg_right hL.le
  have hw0 : 0 < w := div_pos hμ (by positivity)
  have hg : 0 < g := by dsimp [g]; positivity
  obtain ⟨u, hu, hth, hub, horder⟩ := exists_soft_scale_cluster_order q N hq hN hμ hw
  refine ⟨u, hu, hth, ?_⟩
  intro ell m k t D M tau xi base W r B
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hscale : (u : ℝ) ≤ A * X ^ 4 := soft_scale_le_log_four hμ hL.le hH hub
  obtain ⟨hm, hk⟩ := soft_orders_le_log_powers hμ hL.le hH hub
  change (m : ℝ) ≤ A ^ 10 * X ^ 40 at hm
  change (k : ℝ) ≤ A ^ 16 * X ^ 64 at hk
  obtain ⟨hsize, hcost⟩ := soft_member_costs hq hu hg hth
  change log (D : ℝ) ≤ (u : ℝ) ^ 9 at hsize
  have hX40 := one_le_pow₀ hX (n := 40)
  have hLX : log N ≤ X ^ 40 := by
    have hh : X ≤ X ^ 40 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1 ≤ 40)
    exact (le_add_of_nonneg_left zero_le_one : log N ≤ X).trans hh
  have hn : 2 * log N + (log 2 + log t + (m + 1 : ℕ) * log 2 +
      max 0 (24 * log D + 10 * log M - 2 * log g + log 20000 + log (M + g + 8)))
      ≤ (2 + 20100 * A ^ 10) * X ^ 40 := by
    change _ ≤ 20100 * (m : ℝ) at hcost
    rw [add_mul, mul_assoc]
    exact add_le_add (mul_le_mul_of_nonneg_left hLX (by norm_num))
      (hcost.trans (mul_le_mul_of_nonneg_left hm (by norm_num)))
  have hr : (r : ℝ) ≤ 1 + ((2 + 20100 * A ^ 10) * X ^ 40) / d := by
    apply horder.trans
    apply add_le_add_right
    apply div_le_div_of_nonneg_right _ hd.le
    change 2 * log N + log 2 + log t + (m + 1 : ℕ) * log 2 +
      max 0 (24 * log D + 10 * log M - 2 * log g + log 20000 + log (M + g + 8)) ≤ _
    simpa only [add_assoc] using hn
  have hrR : (r : ℝ) ≤ R * X ^ 40 := by
    apply hr.trans
    calc
      _ ≤ (1 + (2 + 20100 * A ^ 10) / d) * X ^ 40 := by
        rw [add_mul 1, one_mul, div_mul_eq_mul_div]
        exact add_le_add_left hX40 _
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  constructor
  · by_cases hD : D = 0
    · simpa [hD] using (exp_pos (A ^ 9 * X ^ 36)).le
    rw [← exp_log (by exact_mod_cast Nat.pos_of_ne_zero hD : 0 < (D : ℝ))]
    apply exp_le_exp.mpr
    exact hsize.trans ((pow_le_pow_left₀ (Nat.cast_nonneg u) hscale 9).trans_eq
      (by rw [mul_pow, ← pow_mul]))
  · exact soft_member_bond_le_exp (le_max_left ..) (by omega : 1 ≤ q) hX hR hrR
      (hm.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))) hk

end Real
