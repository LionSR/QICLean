/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Module

/-! # Matrix lower bounds under averaging and identity extension

Adding the complementary term `1 - S` preserves a lower bound at most one.
For a projection and a metric supported on its range, this is extension by
the identity on the complementary subspace.

A whole-space lower bound and a lower bound on a distinguished projection
are then averaged before applying logarithms or weighted matrix means.
The metric need not commute with the distinguished projection.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*
  (September 24, 2026), `07-comparators.tex`, lines 603–621,
  in the proof of `comparator:tree-log-lower`.
-/

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Finite n] [DecidableEq n]

/-- Averaging a whole-space floor and a projection bound gives the two-sector
comparison used before evaluating the mean tree. No commutation or projection
hypothesis is needed for the averaging itself.

Area-law paper, `07-comparators.tex`, lines 603–615. -/
theorem floor_pin_le {A P : Matrix n n ℂ} {b c : ℝ}
    (hfloor : (2 * b) • (1 : Matrix n n ℂ) ≤ A) (hpin : c • P ≤ A) :
    b • (1 - P) + (b + c / 2) • P ≤ A := by
  let := Fintype.ofFinite n
  have h := smul_le_smul_of_nonneg_left (add_le_add hfloor hpin)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  convert h using 1 <;> module

/-- Adding the complementary term preserves a floor at most one. For a
projection and a metric supported on its range, this is identity extension.
This is the complementary-sector step of the area-law lower comparison,
`07-comparators.tex`, lines 454–476. -/
theorem identity_extension_floor {T S : Matrix n n ℂ} {c : ℝ}
    (hS : S ≤ (1 : Matrix n n ℂ)) (hc : c ≤ 1) (hfloor : c • S ≤ T) :
    c • (1 : Matrix n n ℂ) ≤ T + (1 - S) := by
  let := Fintype.ofFinite n
  have h := add_le_add hfloor
    (smul_le_smul_of_nonneg_right hc (sub_nonneg.mpr hS))
  convert h using 1 <;> module

end Matrix
