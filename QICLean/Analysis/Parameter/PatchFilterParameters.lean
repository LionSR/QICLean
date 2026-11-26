/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The filter exponent of the patch energy estimate

The total filter weight of the patch construction is
`κ = min (1 / 2) (√(Δ / (1024 * C_E)))` with energy coefficient
`C_E = 36 q² J`. It is at most one half, its quadratic energy `C_E κ²` is at
most one 1024th of the gap, and it is positive when `C_E` and the gap are.
The value depends only on `q`, `J` and `Δ`, so it is fixed before all later
geometric and variational data.

This scalar result does not prove an energy bound for a filtered vector.
In the patch argument it is applied after that bound has been established.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 338–343,
`eq:patch-kappa-choice`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace Real

/-- The filter exponent `κ = min {1/2, √(Δ / (1024 C_E))}` of the patch
construction, with `C_E = 36 q² J`. It depends only on the local dimension,
the interaction bound and the gap.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 338–343,
`eq:patch-kappa-choice`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
noncomputable def patchFilterExponent (q : ℕ) (J Δ : ℝ) : ℝ :=
  min (1 / 2) (Real.sqrt (Δ / (1024 * (36 * (q : ℝ) ^ 2 * J))))

/-- The filter exponent is at most one half (`03-patches.tex`, line 342). -/
theorem patchFilterExponent_le_half (q : ℕ) (J Δ : ℝ) :
    patchFilterExponent q J Δ ≤ 1 / 2 :=
  min_le_left _ _

/-- The filter exponent is positive when the energy coefficient `36 q² J` and
the gap are positive (`03-patches.tex`, lines 340–343). -/
theorem patchFilterExponent_pos {q : ℕ} {J Δ : ℝ}
    (hC : 0 < 36 * (q : ℝ) ^ 2 * J) (hΔ : 0 < Δ) :
    0 < patchFilterExponent q J Δ :=
  lt_min (by norm_num) (Real.sqrt_pos.mpr (div_pos hΔ (by positivity)))

/-- The filter exponent is positive for a nonzero local dimension and positive
interaction bound and gap (`03-patches.tex`, lines 340–343). -/
theorem patchFilterExponent_pos_of_pos {q : ℕ} {J Δ : ℝ}
    (hq : 0 < q) (hJ : 0 < J) (hΔ : 0 < Δ) :
    0 < patchFilterExponent q J Δ :=
  patchFilterExponent_pos (by positivity) hΔ

/-- Every parameter between zero and the filter exponent has quadratic energy
`36 q² J κ²` at most one 1024th of the gap. A zero energy coefficient is
allowed.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 338–365,
`eq:patch-kappa-choice` and `eq:patch-marginal-closeness`. -/
theorem mul_sq_le_div_1024_of_le_patchFilterExponent {q : ℕ} {J Δ κ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 ≤ Δ) (hκ : 0 ≤ κ) (hle : κ ≤ patchFilterExponent q J Δ) :
    36 * (q : ℝ) ^ 2 * J * κ ^ 2 ≤ Δ / 1024 := by
  have hC : 0 ≤ 36 * (q : ℝ) ^ 2 * J := by positivity
  rcases hC.eq_or_lt with hC | hC
  · rw [← hC, zero_mul]
    positivity
  · have hsq : κ ^ 2 ≤ Δ / (1024 * (36 * (q : ℝ) ^ 2 * J)) :=
      (pow_le_pow_left₀ hκ (hle.trans (min_le_right _ _)) 2).trans_eq
        (Real.sq_sqrt (by positivity))
    rw [div_mul_eq_div_div, le_div_iff₀' hC] at hsq
    exact hsq

/-- The filter exponent itself has quadratic energy at most one 1024th of the
gap (`03-patches.tex`, lines 338–343). -/
theorem mul_patchFilterExponent_sq_le {q : ℕ} {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 ≤ Δ) :
    36 * (q : ℝ) ^ 2 * J * patchFilterExponent q J Δ ^ 2 ≤ Δ / 1024 :=
  mul_sq_le_div_1024_of_le_patchFilterExponent hJ hΔ
    (le_min (by norm_num) (Real.sqrt_nonneg _)) le_rfl

end Real

/-!
# An explicit logarithmic radius for patch approximation

The radius exponent is fixed by the entropy constant, the geometric size
constant, the desired accuracy, and the total filter weight. At every size
at least two, the resulting logarithmic radius exceeds the initial scale
and makes the logarithmic remainder bound at most minus the accuracy times
the logarithm of the size. A logarithmic number of cylinders is absorbed
by increasing the polynomial exponent by one.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 534–563 and 595–603,
`eq:patch-explicit-radius` and `eq:patch-distance-to-cylinders`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace Real

/-- The radius exponent depends on the fixed constants and the accuracy,
before the system size or patch center is chosen.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 540–547,
`eq:patch-explicit-radius`. -/
noncomputable def regularizedPatchRadiusExponent (C₀ B₀ p κ : ℝ) : ℝ :=
  4 / 3 * (C₀ * (B₀ + 1 / Real.log 2) + 1 + 2 * p / κ)

/-- The explicit logarithmic radius exceeds the starting scale and makes the
source logarithmic remainder estimate at most minus `p * log L`.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 534–563,
`eq:patch-all-tail-log` and `eq:patch-explicit-radius`. -/
theorem regularizedPatchRadiusExponent_bounds
    {C₀ B₀ p κ L u : ℝ} (hC₀ : 0 ≤ C₀) (hB₀ : 0 ≤ B₀)
    (hp : 0 ≤ p) (hκ : 0 < κ) (hL : 2 ≤ L) (hu : u ≤ B₀ * Real.log L) :
    let R₀ := regularizedPatchRadiusExponent C₀ B₀ p κ
    0 < R₀ ∧ C₀ * (1 + u) ≤ R₀ * Real.log L ∧
      κ / 2 * (C₀ * (1 + u) + Real.log 2 - 3 * (R₀ * Real.log L) / 4) ≤
        -p * Real.log L := by
  intro R₀
  let A := C₀ * (B₀ + 1 / Real.log 2)
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log L := Real.log_le_log (by norm_num) hL
  have hlogL : 0 ≤ Real.log L := hlogtwo.le.trans hlog
  have hunit : (1 : ℝ) ≤ Real.log L / Real.log 2 :=
    (le_div_iff₀ hlogtwo).mpr (by simpa using hlog)
  have hbase : C₀ * (1 + u) ≤ A * Real.log L := by
    calc
      _ ≤ C₀ * (B₀ * Real.log L + Real.log L / Real.log 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hC₀
      _ = _ := by dsimp [A]; ring
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hquot : 0 ≤ 2 * p / κ := div_nonneg (by positivity) hκ.le
  have hR₀ : R₀ = 4 / 3 * (A + 1 + 2 * p / κ) := rfl
  have hpos : 0 < R₀ := by rw [hR₀]; nlinarith
  have hdom : A ≤ R₀ := by rw [hR₀]; nlinarith
  refine ⟨hpos, hbase.trans (mul_le_mul_of_nonneg_right hdom hlogL), ?_⟩
  calc
    _ ≤ κ / 2 * (A * Real.log L + Real.log L - 3 * (R₀ * Real.log L) / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = -p * Real.log L := by
      rw [hR₀]
      field_simp [hκ.ne']
      ring

/-- A logarithmic cylinder count costs one further power of the system size.
The estimate holds for every real exponent.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 595–603. -/
theorem mul_rpow_le_succ_rpow_of_le_log {B₀ L α : ℝ} {m : ℕ}
    (hB₀ : 0 ≤ B₀) (hL : 2 ≤ L)
    (hm : (m : ℝ) ≤ B₀ / 2 * Real.log L + 1) :
    (m : ℝ) * L ^ α ≤ (1 + B₀ / 2) * L ^ (α + 1) := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hL
  have hcoef : B₀ / 2 * Real.log L + 1 ≤ (1 + B₀ / 2) * L := by
    have h := mul_le_mul_of_nonneg_left (Real.log_le_self hLpos.le)
      (show 0 ≤ B₀ / 2 by positivity)
    nlinarith
  calc
    _ ≤ (B₀ / 2 * Real.log L + 1) * L ^ α :=
      mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hLpos.le α)
    _ ≤ ((1 + B₀ / 2) * L) * L ^ α :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hLpos.le α)
    _ = _ := by rw [Real.rpow_add_one hLpos.ne']; ring

end Real
