/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Two-sided residuals of a nearby operator

If an operator `M'` has two small residuals `‖M' ψ - z φ‖ ≤ ε` and `‖M'* φ - z ψ‖ ≤ ε` on unit
vectors `ψ, φ`, then every operator `M` with `‖M - M'‖ ≤ δ` has both residuals at most
`δ + ε`. This passes the two-sided Gaussian filter of the information reset to its localized
approximation.

Moved from TNLean, `TNLean/Lattice/RegionalReset.lean` at commit `e41c3b63`
(`norm_two_sided_le_of_norm_sub_le`), with vectors in `EuclideanSpace`.

## Main results

* `Matrix.norm_two_sided_le_of_norm_sub_le`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, proof of Lemma 3.3 (`lem:reset`), `02-information.tex`, lines 498–564,
  `eq:info-local-two-sided`.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Two-sided residuals of a nearby operator.** If `‖M - M'‖ ≤ δ` and `M'` has residuals
`‖M' ψ - z φ‖ ≤ ε` and `‖M'* φ - z ψ‖ ≤ ε` on unit vectors `ψ, φ`, then `M` has both residuals
at most `δ + ε`. Polynomial PEPS approximation, `02-information.tex`, lines 498–564. -/
theorem norm_two_sided_le_of_norm_sub_le {M M' : Matrix n n ℂ} {ψ φ : EuclideanSpace ℂ n}
    {z : ℂ} {δ ε : ℝ} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hM : ‖M - M'‖ ≤ δ)
    (hfwd : ‖toEuclideanLin M' ψ - z • φ‖ ≤ ε) (hrev : ‖toEuclideanLin M'ᴴ φ - z • ψ‖ ≤ ε) :
    ‖toEuclideanLin M ψ - z • φ‖ ≤ δ + ε ∧ ‖toEuclideanLin Mᴴ φ - z • ψ‖ ≤ δ + ε := by
  have hop (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
      ‖toEuclideanLin A x‖ ≤ ‖A‖ * ‖x‖ := by
    have h := (toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm x
    rw [l2_opNorm_toEuclideanCLM] at h
    exact h
  have hsplit (A A' : Matrix n n ℂ) (x w : EuclideanSpace ℂ n) :
      ‖toEuclideanLin A x - w‖ ≤ ‖toEuclideanLin (A - A') x‖ + ‖toEuclideanLin A' x - w‖ := by
    rw [map_sub, LinearMap.sub_apply]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  constructor
  · refine (hsplit M M' ψ _).trans (add_le_add ((hop _ ψ).trans ?_) hfwd)
    rw [hψ, mul_one]
    exact hM
  · refine (hsplit Mᴴ M'ᴴ φ _).trans (add_le_add ((hop _ φ).trans ?_) hrev)
    rw [hφ, mul_one, ← conjTranspose_sub, l2_opNorm_conjTranspose]
    exact hM

end Matrix
