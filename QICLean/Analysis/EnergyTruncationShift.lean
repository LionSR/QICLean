/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CfcScalarShift
import QICLean.Analysis.EnergyTruncation

/-!
# Upper spectral clipping under a scalar energy shift

Centering the energy translates the hard cutoff by the same scalar. This identity supports
the energy-centered regional truncations in ALVV, arXiv:1602.08828v2,
Definition `def:hard-trunc`, lines 873–886.
-/

open scoped MatrixOrder ComplexOrder

namespace Matrix

/-- Subtracting a real scalar from a Hermitian matrix translates the hard cutoff.
Auxiliary to ALVV, arXiv:1602.08828v2, Definition `def:hard-trunc`, lines 873–886. -/
theorem IsHermitian.energyTruncation_sub_smul_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (e T : ℝ) :
    energyTruncation (A - (e : ℂ) • 1) T =
      energyTruncation A (e + T) - (e : ℂ) • 1 := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  rw [energyTruncation, hA.cfc_sub_smul_one (fun x : ℝ ↦ min x T) e]
  have hmin : (fun x : ℝ ↦ min (x - e) T) =
      (fun x : ℝ ↦ min x (e + T) - e) := by
    funext x
    simpa only [add_sub_cancel_left] using min_sub_sub_right x (e + T) e
  rw [hmin, cfc_sub _ _ A (hc _) (hc _), cfc_const e A hA.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  rfl

end Matrix
