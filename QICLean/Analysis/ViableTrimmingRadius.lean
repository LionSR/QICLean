/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A uniform radius for collective trimming

One positive radius controls every number of internal cuts up to the
chain length, with the squared whole-exterior reference bond retained.
This supports ALVV, arXiv:1602.08828v2, `lem:trimming`, lines 660–697,
and the degenerate-ground-space merge analysis, lines 1801–1805.
-/

namespace Real

/-- A single radius reserves at most `1/250` of the viability error at any
interval, including an interval with no internal cuts. The squared reference
bond is retained explicitly. Supporting ALVV, arXiv:1602.08828v2,
`lem:trimming`, lines 660–697, and the merge analysis, lines 1801–1805. -/
theorem viable_node_trimming_radius_budget {L cuts D : ℕ} (hcuts : cuts ≤ L) (hD : 1 ≤ D) :
    let xi := 1 / (1000 * (D : ℝ) * Real.sqrt ((L : ℝ) + 1))
    0 < xi ∧ 4 * xi * Real.sqrt ((cuts : ℝ) * (D : ℝ) ^ 2) ≤ 1 / 250 := by
  intro xi
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hroot0 : 0 < Real.sqrt ((L : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hxi : 0 < xi := by dsimp only [xi]; positivity
  refine ⟨hxi, ?_⟩
  have hcutsR : (cuts : ℝ) ≤ (L : ℝ) + 1 := by
    exact_mod_cast (hcuts.trans (Nat.le_succ L))
  have hroot : Real.sqrt ((cuts : ℝ) * (D : ℝ) ^ 2) ≤
      (D : ℝ) * Real.sqrt ((L : ℝ) + 1) := by
    calc
      _ = (D : ℝ) * Real.sqrt (cuts : ℝ) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg cuts), Real.sqrt_sq hD0.le, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcutsR) hD0.le
  calc
    _ ≤ 4 * xi * ((D : ℝ) * Real.sqrt ((L : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = 1 / 250 := by
      dsimp only [xi]
      field_simp
      ring

end Real
