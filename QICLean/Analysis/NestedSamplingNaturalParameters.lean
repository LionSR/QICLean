/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.NestedSamplingParameters
import QICLean.Analysis.ViableSubspaceBootstrap

/-!
# The natural half-size sample for nested targets

The sample dimension is the actual natural quotient, rather than an
independently supplied real parameter. The count comparison and calibrated
suppression then imply both numerical sampling conditions. This supports
ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines 1112–1128.

**Local fix (strict decrease and complex sphere nets):** The half-size
quotient permits an image of dimension at most half the lower viable
dimension. The corrected complex-sphere exponent is retained. See
`docs/paper-gaps/alvv16_low_density_sampling.tex` and
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

namespace Real

/-- The actual natural sample size satisfies the strict failure bound and
the final error budget at a bad-to-good dyadic dimension comparison.
This is a numerical auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128; it does not construct the physical
family or identify its target spaces. -/
theorem nested_sampling_natural_conditions {D Dnext r p Q t : ℕ} {Delta : ℝ}
    (hlogD : 100 ≤ log (D : ℝ)) (hr : 1 ≤ r) (ht : t ≤ r)
    (hcount : log (Dnext : ℝ) ≤ (13 / 6) * log (D : ℝ))
    (hbad : r * D ^ 3 < p) (hpQ : p ≤ Q) (hupper : Q ≤ r * Dnext ^ 3)
    (htrade : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000) :
    let s : ℕ := p / (2 * D ^ 2)
    let alpha : ℝ := (1 - 1 / 25) * (s : ℝ) / (8 * (Q : ℝ))
    8 ≤ D ∧ 4 * D ^ 2 ≤ p ∧ 1 ≤ s ∧ 0 < alpha ∧
      (1 + 2 / sqrt alpha) ^ (2 * t) * Q * exp (-((s : ℝ) / 16)) < 1 ∧
      Delta / alpha ^ 2 ≤ 1 / 400 := by
  intro s alpha
  have hDne : D ≠ 0 := by
    intro hz
    norm_num [hz] at hlogD
  have hDn : 0 < D := Nat.pos_of_ne_zero hDne
  have hD0 : (0 : ℝ) < D := Nat.cast_pos.mpr hDn
  have hDR : (8 : ℝ) ≤ D := by
    have hb := log_le_sub_one_of_pos hD0
    linarith only [hlogD, hb]
  have hD8 : 8 ≤ D := by exact_mod_cast hDR
  have hp4 : 4 * D ^ 2 ≤ p := by
    calc
      4 * D ^ 2 ≤ D * D ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = D ^ 3 := by ring
      _ ≤ r * D ^ 3 := by
        have hb := Nat.mul_le_mul_right (D ^ 3) hr
        simpa only [one_mul] using hb
      _ ≤ p := hbad.le
  have hden : 0 < 2 * D ^ 2 := by positivity
  have hs1 : 1 ≤ s := (Nat.le_div_iff_mul_le hden).mpr (by nlinarith only [hp4])
  have hpn : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hbad
  have hQn : 0 < Q := hpn.trans_le hpQ
  have hQ0 : (0 : ℝ) < Q := Nat.cast_pos.mpr hQn
  have hs0 : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
  have hnext : Dnext ≠ 0 := by
    intro hz
    have hb : Q ≤ 0 := by simpa [hz] using hupper
    omega
  have hnext0 : (0 : ℝ) < Dnext := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnext)
  have hfloor := Submodule.bootstrap_sample_floor_lower_bound D p (by omega) hp4
  have hps : (p : ℝ) ≤ 4 * (D : ℝ) ^ 2 * (s : ℝ) := by
    have hb := (div_le_iff₀ (by positivity : 0 < 4 * (D : ℝ) ^ 2)).mp hfloor
    change (p : ℝ) ≤ (s : ℝ) * (4 * (D : ℝ) ^ 2) at hb
    nlinarith only [hb]
  have hbadR : (r : ℝ) * (D : ℝ) ^ 3 < p := by exact_mod_cast hbad
  have hupperR : (Q : ℝ) ≤ (r : ℝ) * (Dnext : ℝ) ^ 3 := by exact_mod_cast hupper
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have htR : (t : ℝ) ≤ r := by exact_mod_cast ht
  have halpha : alpha = 3 * (s : ℝ) / (25 * (Q : ℝ)) := by
    dsimp only [alpha]
    ring
  have hnumeric := nested_sampling_conditions hDR hlogD hnext0 hrR htR hQ0 hs0
    hcount hbadR hupperR hps htrade
  refine ⟨hD8, hp4, hs1, ?_, ?_⟩
  · dsimp only [alpha]
    positivity
  · simpa only [halpha] using hnumeric

end Real
