/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ShiftedDensityTruncation
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Scalar-shift derivatives of positive matrix powers

Real powers of a positive semidefinite matrix shifted by a positive scalar
identity are differentiable with respect to the scalar shift. The proof keeps
the eigenbasis of the original matrix fixed. The matrix may be singular, and
the finite index type may be empty.

These are supporting facts for OpenAI, *Polynomial PEPS approximation of
gapped square-grid ground states*, September 24, 2026, `03-patches.tex`,
lines 425–451. No variation in a noncommuting matrix direction is asserted.
-/

/-
Original scalar-shift derivative and contraction facts supporting OpenAI,
Polynomial PEPS approximation of gapped square-grid ground states, September 24, 2026,
03-patches.tex lines 425–451, eq:patch-uniform-local-lipschitz.
No noncommuting matrix derivative, minimum-envelope estimate, regulator-growth
theorem, or completion of Proposition 4.1 is asserted; no upstream Lean proof text reused.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Filter Topology

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The derivative with respect to a positive scalar identity shift.
The base matrix need only be positive semidefinite. -/
theorem PosSemidef.hasDerivAt_add_smul_one_rpow (hA : A.PosSemidef) {b : ℝ}
    (hb : 0 < b) (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (A + s • 1) ^ r)
      (r • (A + b • 1) ^ (r - 1)) b := by
  let U : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let d : ℝ → n → ℂ := fun s i ↦ ((hA.isHermitian.eigenvalues i + s) ^ r : ℝ)
  let d' : n → ℂ := fun i ↦ (r * (hA.isHermitian.eigenvalues i + b) ^ (r - 1) : ℝ)
  have hd : HasDerivAt d d' b := by
    apply hasDerivAt_pi.mpr
    intro i
    have hpos : 0 < hA.isHermitian.eigenvalues i + b :=
      add_pos_of_nonneg_of_pos (hA.eigenvalues_nonneg i) hb
    simpa [d, d'] using
      (((hasDerivAt_id b).const_add (hA.isHermitian.eigenvalues i)).rpow_const
        (Or.inl hpos.ne')).ofReal_comp
  let L : (n → ℂ) →L[ℝ] Matrix n n ℂ :=
    (diagonalLinearMap n ℝ ℂ).toContinuousLinearMap
  have hD := L.hasFDerivAt.comp_hasDerivAt b hd
  have hU := (hD.const_mul U).mul_const (star U)
  have heq : (fun s ↦ U * diagonal (d s) * star U) =ᶠ[𝓝 b]
      (fun s : ℝ ↦ (A + s • 1) ^ r) := by
    filter_upwards [eventually_gt_nhds hb] with s hs
    rw [hA.add_smul_one_rpow_eq_cfc hs, hA.isHermitian.cfc_eq,
      IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  have hderiv : U * diagonal d' * star U = r • (A + b • 1) ^ (r - 1) := by
    rw [hA.add_smul_one_rpow_eq_cfc hb, hA.isHermitian.cfc_eq,
      IsHermitian.cfc, Unitary.conjStarAlgAut_apply, ← smul_mul_assoc, ← mul_smul_comm,
      ← diagonal_smul]
    congr 2
    ext i
    simp [d', Function.comp_def, Complex.real_smul, diagonal_apply]
  exact hderiv ▸ hU.congr_of_eventuallyEq heq.symm

/-- Exponentially decaying regularization has the scalar chain-rule derivative. -/
theorem PosSemidef.hasDerivAt_add_exp_neg_smul_one_rpow (hA : A.PosSemidef)
    (R r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (A + Real.exp (-s) • 1) ^ r)
      ((-r * Real.exp (-R)) • (A + Real.exp (-R) • 1) ^ (r - 1)) R := by
  simpa [Function.comp_def, smul_smul, mul_comm] using
    (hA.hasDerivAt_add_smul_one_rpow (Real.exp_pos (-R)) r).scomp R
      (hasDerivAt_id R).neg.exp

/-- The positive shift times the inverse power is a contraction for every
positive semidefinite matrix, without a trace normalization. -/
theorem PosSemidef.l2_opNorm_smul_add_smul_one_rpow_neg_one_le (hA : A.PosSemidef)
    {b : ℝ} (hb : 0 < b) :
    ‖b • (A + b • 1) ^ (-1 : ℝ)‖ ≤ 1 := by
  rw [hA.add_smul_one_rpow_eq_cfc hb,
    ← cfc_const_mul b (fun t : ℝ ↦ (t + b) ^ (-1 : ℝ)) A
      (A.finite_real_spectrum.continuousOn _)]
  refine norm_cfc_le zero_le_one fun t ht ↦ ?_
  have ht0 := spectrum_nonneg_of_nonneg hA.nonneg ht
  have hpos : 0 < t + b := add_pos_of_nonneg_of_pos ht0 hb
  rw [Real.rpow_neg_one, Real.norm_of_nonneg (mul_nonneg hb.le (inv_nonneg.mpr hpos.le))]
  exact (mul_inv_le_iff₀ hpos).mpr (by linarith)

end Matrix
