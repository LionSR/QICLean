/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GammaRatio
import QICLean.Representation.HookFormula

/-!
# The common replica label function

Fix `d ≥ 1` and `t ≥ 0`. For a part vector `λ : Fin d → ℕ` with `k = ∑ λ_i` and shifted parts
`l_i = λ_i + d - 1 - i` (rows indexed from `0`), the area-law paper (*A two-dimensional area
law from a global spectral gap*, `05-replicas.tex`, equation `replicas:w-definition`,
lines 287–298) defines

`c = d + (1 + t) binom(d, 2)`,
`w_k(λ) = Γ(c)/Γ(c + t k) ∏_i Γ(1 + t l_i)/Γ(1 + t (d - 1 - i))`.

The replica metric of a subsystem is `W_{Q,k} = ∑_λ w_k(λ) π^λ_{Q,k}`, with the label padded
to the full dimension `d` on every subsystem. This file proves the scalar properties of the
label function used in Lemma 6.2 (`replicas:metric`, lines 305–335):

* positivity and `w_0 = 1` (line 299: `W_{Q,0} = I`);
* the exact marked ratio (equation `replicas:ratio-eigenvalue`, lines 403–409): adding a box
  in row `i` multiplies the weight by
  `r_{λ,i} = Γ(c + t(k - 1))/Γ(c + t k) · Γ(1 + t l_i)/Γ(1 + t(l_i - 1))`,
  where `k` and `l_i` refer to the enlarged label;
* the entropy asymptotics `log w_k(λ) = -t k H(λ/k) + O_{d,t}(log(k + 2))` (lines 395–400),
  from `log Γ(1 + u) = u log u - u + O(log(u + 2))`.

The proof is written from the paper; no Lean source was adapted.

## Main declarations

* `Real.abs_log_Gamma_one_add_sub_le` — `|log Γ(1 + u) - (u log u - u)| ≤ 3 log(u + 2) + 3`.
* `Partition.replicaConst`, `Partition.replicaWeight`, `Partition.replicaRatio`.
* `Partition.replicaWeight_pos`, `Partition.replicaWeight_zero`.
* `Partition.replicaWeight_update_succ` — the exact marked ratio.
* `Partition.exists_abs_log_replicaWeight_add_le` — the entropy asymptotics.
-/

open Real Finset

namespace Real

/-- `u log u - u` changes by at most `log(u + 2) + 2` between `⌊u⌋` and `u`. -/
private theorem abs_mul_log_sub_floor_le {u : ℝ} (hu : 0 ≤ u) :
    |(u * log u - u) - ((⌊u⌋₊ : ℝ) * log ⌊u⌋₊ - ⌊u⌋₊)| ≤ log (u + 2) + 2 := by
  set n := ⌊u⌋₊
  have hn : (n : ℝ) ≤ u := Nat.floor_le hu
  have hn1 : u < n + 1 := Nat.lt_floor_add_one u
  have hlog2 : 0 ≤ log (u + 2) := log_nonneg (by linarith)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at hn1 ⊢
    simp only [Nat.cast_zero, zero_mul, sub_zero, sub_self] at hn1 ⊢
    -- `u ∈ [0, 1)`, so `u log u ∈ [u - 1, 0]`.
    have hlow : u - 1 ≤ u * log u := by
      rcases hu.eq_or_lt with rfl | hu'
      · simp
      have := one_sub_inv_le_log_of_pos hu'
      have h := mul_le_mul_of_nonneg_left this hu'.le
      rwa [mul_sub, mul_one, mul_inv_cancel₀ hu'.ne'] at h
    have hup : u * log u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu
      (log_nonpos hu (by linarith))
    rw [abs_le]; constructor <;> linarith
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    have hu0 : 0 < u := lt_of_lt_of_le hn0 hn
    -- `n (log u - log n) ∈ [0, u - n]`.
    have hdiff_up : (n : ℝ) * (log u - log n) ≤ u - n := by
      rw [← log_div hu0.ne' hn0.ne']
      have := log_le_sub_one_of_pos (div_pos hu0 hn0)
      have h := mul_le_mul_of_nonneg_left this hn0.le
      rwa [mul_sub, mul_one, mul_div_cancel₀ _ hn0.ne'] at h
    have hdiff_lo : 0 ≤ (n : ℝ) * (log u - log n) :=
      mul_nonneg hn0.le (sub_nonneg.mpr (log_le_log hn0 hn))
    have hlogu0 : 0 ≤ log u := log_nonneg (le_trans (by exact_mod_cast hpos) hn)
    have hlogu : log u ≤ log (u + 2) := log_le_log hu0 (by linarith)
    have hs : 0 ≤ u - n := by linarith
    have hs1 : u - n ≤ 1 := by linarith
    have hslog : (u - n) * log u ≤ log (u + 2) := by nlinarith
    have hslog0 : 0 ≤ (u - n) * log u := mul_nonneg hs hlogu0
    have hid : (u * log u - u) - ((n : ℝ) * log n - n) =
        (n : ℝ) * (log u - log n) + (u - n) * log u - (u - n) := by ring
    rw [hid, abs_le]; constructor <;> linarith

/-- **Stirling-type estimate for the Gamma function** (`05-replicas.tex`, line 395):
`log Γ(1 + u) = u log u - u + O(log(u + 2))`, in the explicit form
`|log Γ(1 + u) - (u log u - u)| ≤ 3 log(u + 2) + 3` for `u ≥ 0`. -/
theorem abs_log_Gamma_one_add_sub_le {u : ℝ} (hu : 0 ≤ u) :
    |log (Gamma (1 + u)) - (u * log u - u)| ≤ 3 * log (u + 2) + 3 := by
  set n := ⌊u⌋₊
  have hn : (n : ℝ) ≤ u := Nat.floor_le hu
  have hn1 : u < n + 1 := Nat.lt_floor_add_one u
  set s := u - n with hs_def
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 := by linarith
  set x : ℝ := n + 1 with hx_def
  have hx1 : 1 ≤ x := by simp only [hx_def]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hx0 : 0 < x := by linarith
  have hxs : 1 + u = x + s := by simp only [hx_def, hs_def]; ring
  have hGx : Gamma x = n.factorial := by simp only [hx_def]; exact Gamma_nat_eq_factorial n
  have hGx0 : 0 < Gamma x := Gamma_pos_of_pos hx0
  have hGxs0 : 0 < Gamma (x + s) := Gamma_pos_of_pos (by linarith)
  set R := Gamma (x + s) / Gamma x with hR_def
  have hRpos : 0 < R := div_pos hGxs0 hGx0
  have hlogx0 : 0 ≤ log x := log_nonneg hx1
  have hlogxs0 : 0 ≤ log (x + s) := log_nonneg (by linarith)
  have hlogx : log x ≤ log (u + 2) := log_le_log hx0 (by linarith)
  have hlogxs : log (x + s) ≤ log (u + 2) := log_le_log (by linarith) (by linarith)
  have hlogR_up : log R ≤ log (u + 2) := by
    have h := log_le_log hRpos (Gamma_add_div_Gamma_le_rpow hx0 hs0 hs1)
    rw [log_rpow hx0] at h
    nlinarith
  have hlogR_lo : -log (u + 2) ≤ log R := by
    have hp : 0 < (x + s) ^ (1 - s) := rpow_pos_of_pos (by linarith) _
    have h := log_le_log (div_pos hx0 hp) (div_rpow_le_Gamma_add_div_Gamma hx0 hs0 hs1)
    rw [log_div hx0.ne' hp.ne', log_rpow (by linarith)] at h
    nlinarith
  have hlogG : log (Gamma (1 + u)) = log R + log n.factorial := by
    rw [hxs, ← hGx, ← log_mul hRpos.ne' hGx0.ne', hR_def, div_mul_cancel₀ _ hGx0.ne']
  have hst1 := log_factorial_sub_nonneg n
  have hst2 := log_factorial_sub_le n
  have hn2 : log ((n : ℝ) + 2) ≤ log (u + 2) := log_le_log (by positivity) (by linarith)
  have hg := abs_le.mp (abs_mul_log_sub_floor_le hu)
  rw [hlogG, abs_le]
  constructor <;> linarith [hg.1, hg.2]

/-- `log(α K + β + 2) ≤ log(α + β + 2) + log(K + 2)` for `α, β, K ≥ 0`. -/
theorem log_mul_add_add_two_le {α β K : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hK : 0 ≤ K) :
    log (α * K + β + 2) ≤ log (α + β + 2) + log (K + 2) := by
  rw [← log_mul (by positivity) (by positivity)]
  exact log_le_log (by positivity) (by nlinarith)

end Real

namespace Partition

variable {d : ℕ} {t : ℝ}

/-- The constant `c = d + (1 + t) binom(d, 2)` of the replica label function
(`05-replicas.tex`, line 289). -/
noncomputable def replicaConst (d : ℕ) (t : ℝ) : ℝ := d + (1 + t) * (d.choose 2 : ℕ)

/-- The common replica label function (`05-replicas.tex`, equation `replicas:w-definition`):
`w_k(λ) = Γ(c)/Γ(c + t k) ∏_i Γ(1 + t l_i)/Γ(1 + t (d - 1 - i))`, where `k = ∑ λ_i` and
`l_i = λ_i + d - 1 - i` (rows from `0`). -/
noncomputable def replicaWeight (t : ℝ) (p : Fin d → ℕ) : ℝ :=
  Gamma (replicaConst d t) / Gamma (replicaConst d t + t * (∑ i, p i : ℕ)) *
    ∏ i, Gamma (1 + t * shiftedPart p i) / Gamma (1 + t * (d - 1 - i : ℕ))

/-- The marked ratio `r = Γ(c + t(k - 1))/Γ(c + t k) · Γ(1 + t l)/Γ(1 + t(l - 1))`
(`05-replicas.tex`, equation `replicas:ratio-eigenvalue`). -/
noncomputable def replicaRatio (d : ℕ) (t k l : ℝ) : ℝ :=
  Gamma (replicaConst d t + t * (k - 1)) / Gamma (replicaConst d t + t * k) *
    (Gamma (1 + t * l) / Gamma (1 + t * (l - 1)))

theorem one_le_replicaConst (hd : 0 < d) (ht : 0 ≤ t) : 1 ≤ replicaConst d t := by
  unfold replicaConst
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have : 0 ≤ (1 + t) * (d.choose 2 : ℕ) := by positivity
  linarith

/-- For `d = 1` the constant is `c = 1`; for `d ≥ 2` it is at least `2`. -/
theorem replicaConst_eq_one_or_two_le (hd : 0 < d) (ht : 0 ≤ t) :
    replicaConst d t = 1 ∨ 2 ≤ replicaConst d t := by
  rcases Nat.lt_or_ge d 2 with h | h
  · left
    obtain rfl : d = 1 := by omega
    simp [replicaConst]
  · right
    unfold replicaConst
    have : (2 : ℝ) ≤ d := by exact_mod_cast h
    have : 0 ≤ (1 + t) * (d.choose 2 : ℕ) := by positivity
    linarith

private theorem Gamma_one_add_mul_pos (ht : 0 ≤ t) (n : ℕ) : 0 < Gamma (1 + t * n) :=
  Gamma_pos_of_pos (by positivity)

private theorem Gamma_replicaConst_add_pos (hd : 0 < d) (ht : 0 ≤ t) (n : ℕ) :
    0 < Gamma (replicaConst d t + t * n) :=
  Gamma_pos_of_pos (by linarith [one_le_replicaConst hd ht, mul_nonneg ht n.cast_nonneg])

/-- **Lemma 6.2, positivity of the label function**: `w_k(λ) > 0`. -/
theorem replicaWeight_pos (hd : 0 < d) (ht : 0 ≤ t) (p : Fin d → ℕ) :
    0 < replicaWeight t p := by
  unfold replicaWeight
  refine mul_pos (div_pos (Gamma_pos_of_pos (by linarith [one_le_replicaConst hd ht]))
    (Gamma_replicaConst_add_pos hd ht _)) (prod_pos fun i _ => div_pos ?_ ?_)
  · exact Gamma_one_add_mul_pos ht _
  · exact Gamma_one_add_mul_pos ht _

/-- `w_0 = 1` (`05-replicas.tex`, line 299: `W_{Q,0} = I`). -/
theorem replicaWeight_zero (hd : 0 < d) (ht : 0 ≤ t) :
    replicaWeight t (0 : Fin d → ℕ) = 1 := by
  unfold replicaWeight
  have hc := Gamma_pos_of_pos (by linarith [one_le_replicaConst hd ht] : 0 < replicaConst d t)
  simp only [Pi.zero_apply, sum_const_zero, Nat.cast_zero, mul_zero, add_zero,
    div_self hc.ne', one_mul]
  refine prod_eq_one fun i _ => ?_
  simp only [shiftedPart, Pi.zero_apply, zero_add]
  exact div_self (Gamma_one_add_mul_pos ht _).ne'

theorem shiftedPart_update_succ (p : Fin d → ℕ) (i : Fin d) :
    shiftedPart (Function.update p i (p i + 1)) =
      Function.update (shiftedPart p) i (shiftedPart p i + 1) := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp only [shiftedPart, Function.update_self]
    omega
  · simp [shiftedPart, Function.update_of_ne hj]

/-- **Exact marked ratio** (`05-replicas.tex`, equation `replicas:ratio-eigenvalue`):
adding a box in row `i` multiplies the label function by `r_{λ,i}`, evaluated at the number
of copies `k` and shifted part `l_i` of the enlarged label. -/
theorem replicaWeight_update_succ (hd : 0 < d) (ht : 0 ≤ t) (p : Fin d → ℕ) (i : Fin d) :
    replicaWeight t (Function.update p i (p i + 1)) =
      replicaRatio d t (∑ j, p j + 1 : ℕ) (shiftedPart p i + 1 : ℕ) * replicaWeight t p := by
  obtain ⟨k, hk_def⟩ : ∃ k, ∑ j, p j = k := ⟨_, rfl⟩
  have hsum : ∑ j, Function.update p i (p i + 1) j = k + 1 := by
    rw [Finset.sum_update_of_mem (mem_univ i), ← hk_def,
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem (mem_univ i) p]
    ring
  set F : Fin d → ℕ → ℝ := fun j n => Gamma (1 + t * n) / Gamma (1 + t * (d - 1 - j : ℕ))
  have hprod : ∏ j, F j (shiftedPart (Function.update p i (p i + 1)) j) =
      Gamma (1 + t * (shiftedPart p i + 1 : ℕ)) / Gamma (1 + t * shiftedPart p i) *
        ∏ j, F j (shiftedPart p j) := by
    rw [shiftedPart_update_succ, Fintype.prod_eq_mul_prod_compl i,
      Fintype.prod_eq_mul_prod_compl i (fun j => F j (shiftedPart p j))]
    simp only [Function.update_self]
    rw [prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (by simpa using hj)]]
    simp only [F]
    have h1 := Gamma_one_add_mul_pos ht (shiftedPart p i)
    field_simp
  unfold replicaWeight replicaRatio
  rw [hsum, hk_def]
  change _ * ∏ j, F j _ = _ * (_ * ∏ j, F j _)
  rw [hprod]
  have hk := Gamma_replicaConst_add_pos hd ht k
  have hl := Gamma_one_add_mul_pos ht (shiftedPart p i)
  have hc := Gamma_pos_of_pos (by linarith [one_le_replicaConst hd ht] : 0 < replicaConst d t)
  have hk1 := Gamma_replicaConst_add_pos hd ht (k + 1)
  have e1 : ((k + 1 : ℕ) : ℝ) - 1 = k := by push_cast; ring
  have e2 : ((shiftedPart p i + 1 : ℕ) : ℝ) - 1 = shiftedPart p i := by push_cast; ring
  rw [e1, e2]
  field_simp

/-- `(y + a) log(y + a) - (y + a)` differs from `y log y - y` by at most
`a (log(y + a + 2) + 1)`, when `a = 0` or `a ≥ 1`. -/
private theorem abs_mul_log_add_sub_le {y a : ℝ} (hy0 : 0 ≤ y) (ha : a = 0 ∨ 1 ≤ a) :
    |((y + a) * log (y + a) - (y + a)) - (y * log y - y)| ≤ a * (log (y + a + 2) + 1) := by
  rcases ha with rfl | ha1
  · simp
  have hlogya : 0 ≤ log (y + a) := log_nonneg (by linarith)
  have hlogya2 : log (y + a) ≤ log (y + a + 2) := log_le_log (by linarith) (by linarith)
  have hmul : a * log (y + a) ≤ a * log (y + a + 2) :=
    mul_le_mul_of_nonneg_left hlogya2 (by linarith)
  have hmul0 : 0 ≤ a * log (y + a) := mul_nonneg (by linarith) hlogya
  rcases hy0.eq_or_lt with rfl | hy
  · simp only [zero_add, zero_mul, log_zero, sub_zero, sub_self] at hmul hmul0 ⊢
    rw [abs_le]; constructor <;> linarith
  have hd_up : y * (log (y + a) - log y) ≤ a := by
    rw [← log_div (by linarith) hy.ne']
    have := log_le_sub_one_of_pos (div_pos (by linarith : 0 < y + a) hy)
    have h := mul_le_mul_of_nonneg_left this hy.le
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hy.ne'] at h
    linarith
  have hd_lo : 0 ≤ y * (log (y + a) - log y) :=
    mul_nonneg hy.le (sub_nonneg.mpr (log_le_log hy (by linarith)))
  have hid : ((y + a) * log (y + a) - (y + a)) - (y * log y - y) =
      y * (log (y + a) - log y) + a * log (y + a) - a := by ring
  rw [hid, abs_le]; constructor <;> linarith

/-- Row bound: `0 ≤ l log l - λ log λ ≤ d (log(d + 3) + log(K + 2) + 1)` when `l = λ + m`,
`m ≤ d` and `l ≤ K + d`. -/
private theorem row_mul_log_bounds {pi mi d : ℕ} {K : ℝ} (hK0 : 0 ≤ K) (hm : mi ≤ d)
    (hl : ((pi + mi : ℕ) : ℝ) ≤ K + d) :
    0 ≤ ((pi + mi : ℕ) : ℝ) * log (pi + mi : ℕ) - (pi : ℝ) * log pi ∧
      ((pi + mi : ℕ) : ℝ) * log (pi + mi : ℕ) - (pi : ℝ) * log pi ≤
        d * (log (d + 3) + log (K + 2) + 1) := by
  have h := mul_log_add_sub_bounds pi mi
  refine ⟨h.1, h.2.trans ?_⟩
  have hm' : (mi : ℝ) ≤ d := by exact_mod_cast hm
  have hlog0 : 0 ≤ log ((pi + mi : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hd3 : 0 ≤ log ((d : ℝ) + 3) := log_nonneg (by linarith [(d.cast_nonneg : (0:ℝ) ≤ d)])
  have hK2 : 0 ≤ log (K + 2) := log_nonneg (by linarith)
  have hlogl : log ((pi + mi : ℕ) : ℝ) ≤ log (d + 3) + log (K + 2) := by
    rcases Nat.eq_zero_or_pos (pi + mi) with h0 | h0
    · rw [h0]; simp only [Nat.cast_zero, log_zero]; linarith
    have h1 : log ((pi + mi : ℕ) : ℝ) ≤ log (1 * K + d + 2) :=
      log_le_log (by exact_mod_cast h0) (by linarith)
    have h2 := log_mul_add_add_two_le (α := 1) (β := d) zero_le_one d.cast_nonneg hK0
    have h3 : (1 : ℝ) + d + 2 = d + 3 := by ring
    rw [h3] at h2
    linarith
  have h0' : 0 ≤ log ((pi + mi : ℕ) : ℝ) + 1 := by linarith
  calc (mi : ℝ) * (log ((pi + mi : ℕ) : ℝ) + 1) ≤ d * (log ((pi + mi : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hm' h0'
    _ ≤ d * (log (d + 3) + log (K + 2) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) d.cast_nonneg

/-- The logarithm of the label function, expanded. -/
private theorem log_replicaWeight_eq (hd : 0 < d) (ht : 0 ≤ t) (p : Fin d → ℕ) :
    log (replicaWeight t p) =
      log (Gamma (replicaConst d t)) - log (Gamma (replicaConst d t + t * (∑ i, p i : ℕ))) +
        ∑ i, log (Gamma (1 + t * shiftedPart p i)) -
          ∑ i : Fin d, log (Gamma (1 + t * (d - 1 - (i : ℕ) : ℕ))) := by
  have hGc := Gamma_pos_of_pos (by linarith [one_le_replicaConst hd ht] : 0 < replicaConst d t)
  have hGcK := Gamma_replicaConst_add_pos hd ht (∑ i, p i)
  have hGl : ∀ i, 0 < Gamma (1 + t * shiftedPart p i) := fun i => Gamma_one_add_mul_pos ht _
  have hGm : ∀ i : Fin d, 0 < Gamma (1 + t * (d - 1 - (i : ℕ) : ℕ)) :=
    fun i => Gamma_one_add_mul_pos ht _
  unfold replicaWeight
  rw [log_mul (div_pos hGc hGcK).ne' (prod_pos fun i _ => div_pos (hGl i) (hGm i)).ne',
    log_div hGc.ne' hGcK.ne', log_prod (fun i _ => (div_pos (hGl i) (hGm i)).ne')]
  simp only [log_div (hGl _).ne' (hGm _).ne', sum_sub_distrib]
  ring

/-- **Lemma 6.2, entropy asymptotics of the label function** (`05-replicas.tex`,
lines 395–400): `log w_k(λ) = -t k H(λ/k) + O_{d,t}(log(k + 2))`, uniformly in the part
vector `λ`. -/
theorem exists_abs_log_replicaWeight_add_le (hd : 0 < d) (ht : 0 < t) :
    ∃ C, ∀ p : Fin d → ℕ,
      |log (replicaWeight t p) + t * entropyTerm p| ≤ C * log ((∑ i, p i : ℕ) + 2) := by
  set c := replicaConst d t
  have hc1 : 1 ≤ c := one_le_replicaConst hd ht.le
  set a := c - 1
  have ha0 : 0 ≤ a := by linarith
  have ha : a = 0 ∨ 1 ≤ a := by
    rcases replicaConst_eq_one_or_two_le hd ht.le with h1 | h2
    · left; simp only [a, c] at h1 ⊢; linarith
    · right; simp only [a]; linarith
  set m : Fin d → ℕ := fun i => d - 1 - i
  set M : ℝ := ∑ i, (m i : ℝ)
  set A : ℝ := log (Gamma c) - ∑ i, log (Gamma (1 + t * m i))
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hla3 : 0 ≤ log (t + a + 3) := log_nonneg (by linarith)
  have hla2 : 0 ≤ log (t + a + 2) := log_nonneg (by linarith)
  have hltd : 0 ≤ log (t + t * d + 2) :=
    log_nonneg (by nlinarith [(d.cast_nonneg : (0 : ℝ) ≤ d)])
  have hld3 : 0 ≤ log ((d : ℝ) + 3) := log_nonneg (by linarith [(d.cast_nonneg : (0 : ℝ) ≤ d)])
  -- The bound has the form `P + Q log(k + 2)`.
  set P : ℝ := |A + t * M * log t - t * M| + (3 * log (t + a + 2) + 3) +
    a * (log (t + a + 2) + 1) + d * (3 * log (t + t * d + 2) + 3) +
    t * (d * (d * (log (d + 3) + 1)))
  set Q : ℝ := 3 + a + 3 * d + t * (d * d)
  have hP0 : 0 ≤ P := by positivity
  refine ⟨P / log 2 + Q, fun p => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, ∑ i, p i = k := ⟨_, rfl⟩
  rw [hk]
  set K : ℝ := (k : ℝ)
  have hK0 : 0 ≤ K := k.cast_nonneg
  set L := log (K + 2)
  have hL2 : log 2 ≤ L := log_le_log (by norm_num) (by linarith)
  have hLnn : 0 ≤ L := by linarith
  set l := shiftedPart p
  have hl_le : ∀ i, (l i : ℝ) ≤ K + d := fun i => by
    have := shiftedPart_le p i
    rw [hk] at this
    change ((shiftedPart p i : ℕ) : ℝ) ≤ (k : ℝ) + d
    exact_mod_cast this
  have hl_nat : ∀ i, l i = p i + m i := fun i => rfl
  have hl_eq : ∀ i, (l i : ℝ) = p i + m i := fun i => by rw [hl_nat]; push_cast; ring
  -- Stirling for each Gamma value.
  set g : ℝ → ℝ := fun u => u * log u - u
  have hB : |log (Gamma (c + t * K)) - g (t * K + a)| ≤ 3 * log (t * K + a + 2) + 3 := by
    have h := abs_log_Gamma_one_add_sub_le (u := t * K + a) (by positivity)
    have he : 1 + (t * K + a) = c + t * K := by simp only [a]; ring
    rwa [he] at h
  have hshift : |g (t * K + a) - g (t * K)| ≤ a * (log (t * K + a + 2) + 1) :=
    abs_mul_log_add_sub_le (by positivity) ha
  have hmullog : ∀ x : ℝ, 0 ≤ x → g (t * x) = t * x * log t + t * (x * log x) - t * x := by
    intro x hx
    rcases hx.eq_or_lt with rfl | hx
    · simp [g]
    simp only [g]
    rw [log_mul ht.ne' hx.ne']
    ring
  have hgK := hmullog K hK0
  have hgl : ∑ i, g (t * l i) =
      t * log t * ∑ i, (l i : ℝ) + t * ∑ i, ((l i : ℝ) * log (l i)) - t * ∑ i, (l i : ℝ) := by
    rw [sum_congr rfl fun i _ => hmullog (l i) (l i).cast_nonneg, sum_sub_distrib,
      sum_add_distrib, mul_sum, mul_sum, mul_sum]
    congr 2
    exact sum_congr rfl fun i _ => by ring
  have hsuml : ∑ i, (l i : ℝ) = K + M := by
    simp only [hl_eq, sum_add_distrib, M, K, ← hk, Nat.cast_sum]
  have hent := entropyTerm_eq p
  rw [hk] at hent
  have hlogw := log_replicaWeight_eq hd ht.le p
  rw [hk] at hlogw
  -- The total error decomposition.
  set S1 := ∑ i, log (Gamma (1 + t * l i))
  set S3 := ∑ i, g (t * l i)
  set S4 := ∑ i, ((l i : ℝ) * log (l i))
  set S5 := ∑ i, ((p i : ℝ) * log (p i))
  have hX : log (replicaWeight t p) + t * entropyTerm p =
      (A + t * M * log t - t * M) - (log (Gamma (c + t * K)) - g (t * K + a)) -
        (g (t * K + a) - g (t * K)) + (S1 - S3) + t * (S4 - S5) := by
    rw [hlogw, hent, hgK, hgl, hsuml]
    simp only [A, S1, S4, S5, K]
    ring
  -- Bounds for the sums over rows.
  have hS13 : |S1 - S3| ≤ d * (3 * (log (t + t * d + 2) + L) + 3) := by
    rw [show S1 - S3 = ∑ i, (log (Gamma (1 + t * l i)) - g (t * l i)) from
      (sum_sub_distrib _ _).symm]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hbound : ∀ i, |log (Gamma (1 + t * l i)) - g (t * l i)| ≤
        3 * (log (t + t * d + 2) + L) + 3 := by
      intro i
      refine (abs_log_Gamma_one_add_sub_le (by positivity)).trans ?_
      have h1 : log (t * l i + 2) ≤ log (t * K + t * d + 2) :=
        log_le_log (by positivity) (by nlinarith [hl_le i])
      have h2 := log_mul_add_add_two_le (α := t) (β := t * d) ht.le (by positivity) hK0
      linarith
    refine (sum_le_sum fun i _ => hbound i).trans ?_
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hS45 : 0 ≤ S4 - S5 ∧ S4 - S5 ≤ d * (d * (log (d + 3) + L + 1)) := by
    rw [show S4 - S5 = ∑ i, (((l i : ℕ) : ℝ) * log (l i) - (p i : ℝ) * log (p i)) from
      (sum_sub_distrib _ _).symm]
    have hb : ∀ i, 0 ≤ ((l i : ℕ) : ℝ) * log (l i) - (p i : ℝ) * log (p i) ∧
        ((l i : ℕ) : ℝ) * log (l i) - (p i : ℝ) * log (p i) ≤ d * (log (d + 3) + L + 1) := by
      intro i
      rw [hl_nat]
      exact row_mul_log_bounds hK0 (by simp only [m]; omega) (by rw [← hl_nat]; exact hl_le i)
    refine ⟨sum_nonneg fun i _ => (hb i).1, (sum_le_sum fun i _ => (hb i).2).trans ?_⟩
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Remaining logarithms.
  have hlog_a3 : log (t * K + a + 2) ≤ log (t + a + 2) + L :=
    log_mul_add_add_two_le ht.le ha0 hK0
  have hBound : |log (replicaWeight t p) + t * entropyTerm p| ≤ P + Q * L := by
    rw [hX]
    have h1 := abs_le.mp hB
    have h2 := abs_le.mp hshift
    have h3 := abs_le.mp hS13
    obtain ⟨h4, h5⟩ := hS45
    have h6 : t * (S4 - S5) ≤ t * (d * (d * (log (d + 3) + L + 1))) :=
      mul_le_mul_of_nonneg_left h5 ht.le
    have h7 : 0 ≤ t * (S4 - S5) := mul_nonneg ht.le h4
    have hAabs := abs_le.mp (le_refl |A + t * M * log t - t * M|)
    have ha_mul : a * (log (t * K + a + 2) + 1) ≤ a * (log (t + a + 2) + L + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) ha0
    rw [abs_le]
    simp only [P, Q]
    constructor <;> linarith
  calc |log (replicaWeight t p) + t * entropyTerm p| ≤ P + Q * L := hBound
    _ ≤ P / log 2 * L + Q * L := by
        have : P ≤ P / log 2 * L := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
          exact mul_le_mul_of_nonneg_left hL2 hP0
        linarith
    _ = (P / log 2 + Q) * L := by ring

end Partition
