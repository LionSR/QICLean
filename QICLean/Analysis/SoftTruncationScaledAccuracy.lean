/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SoftTruncationAccuracy

/-!
# A compatible order for soft truncation at three times its order

The logarithmic order controls both the reverse physical cutoff and the residual while leaving
all heat times strictly below the cluster threshold. Supporting the corrected moment route to
ALVV, arXiv:1602.08828v2, `lem:exp-approx` and `lem:exp-approx-eff`, lines 1195–1268.
-/

namespace Real

/-- One explicit order controls the correction, the reverse cutoff and the requested residual
when scale is three times order. This is the case `c = 3` of
`Real.softTruncation_scaled_order_bounds_of_le`. Supporting the corrected moment route to ALVV,
arXiv:1602.08828v2, `lem:exp-approx` and `lem:exp-approx-eff`, lines 1195–1268. -/
lemma exists_softTruncation_scaled_order_of_residual_budget
    (eta rho : ℝ) (heta : 0 ≤ eta) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ∃ m : ℕ, m = ⌈12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * log (80 / rho)⌉₊ ∧
      0 < m ∧ 10 ≤ (3 * (m : ℝ)) / 2 ∧
      let alpha := (3 * (m : ℝ)) / 2 * (1 / 2 : ℝ) ^ m
      0 ≤ alpha ∧ alpha ≤ 3 / 4 ∧ 17 + eta + alpha ≤ (3 * (m : ℝ)) / 2 ∧
      80 * exp ((17 + eta + alpha) / 8 - (3 * (m : ℝ)) / 16) ≤ rho := by
  have hmcast : 12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * log (80 / rho) ≤
      (⌈12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * log (80 / rho)⌉₊ : ℝ) := Nat.le_ceil _
  exact ⟨_, rfl, softTruncation_scaled_order_bounds_of_le 3 eta rho
    ⌈12 + (2 / 3 : ℝ) * eta + (16 / 3 : ℝ) * log (80 / rho)⌉₊ (by norm_num) heta hrho
    hrho1 (by linarith only [hmcast])⟩

end Real
