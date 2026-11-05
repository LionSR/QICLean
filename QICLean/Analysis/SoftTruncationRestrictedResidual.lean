/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SoftTruncationHardResidual

/-!
# Soft and hard residuals restricted to a subspace

The pointwise vector comparison gives the operator-norm comparison on every subspace,
without a small global error assumption. This auxiliary supports ALVV,
arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

/-- Restriction to an arbitrary subspace preserves the soft-to-hard residual estimate.
Auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem PosSemidef.norm_softTruncation_residual_domRestrict_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (t : ℝ) (m : ℕ) (T : ℝ)
    (ht : 0 < t) (hm : 1 ≤ m) (hT : 0 ≤ T)
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    ‖(toEuclideanCLM (𝕜 := ℂ) (n := ι)
      (A - cfc (Real.softTruncation t m) A)).domRestrict S‖ ≤
      ‖(toEuclideanCLM (𝕜 := ℂ) (n := ι) (A - energyTruncation A T)).domRestrict S‖ +
        (t / (m : ℝ)) * (T / t) ^ m := by
  let E := (t / (m : ℝ)) * (T / t) ^ m
  let F := (toEuclideanCLM (𝕜 := ℂ) (n := ι)
    (A - cfc (Real.softTruncation t m) A)).domRestrict S
  let B := (toEuclideanCLM (𝕜 := ℂ) (n := ι)
    (A - energyTruncation A T)).domRestrict S
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  change ‖F‖ ≤ ‖B‖ + E
  refine F.opNorm_le_bound (add_nonneg (norm_nonneg B) hE) ?_
  intro v
  have hv : ‖F v‖ ≤ ‖B v‖ + E * ‖v‖ :=
    hA.norm_softTruncation_residual_apply_le t m T ht hm hT (v : EuclideanSpace ℂ ι)
  calc
    ‖F v‖ ≤ ‖B v‖ + E * ‖v‖ := hv
    _ ≤ ‖B‖ * ‖v‖ + E * ‖v‖ := _root_.add_le_add (B.le_opNorm v) (le_refl (E * ‖v‖))
    _ = (‖B‖ + E) * ‖v‖ := (add_mul _ _ _).symm

end Matrix
