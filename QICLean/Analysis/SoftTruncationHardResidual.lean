/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CfcVectorNormOrder
import QICLean.Analysis.EnergyTruncation
import QICLean.Analysis.SoftTruncation

/-!
# Soft residuals controlled by hard residuals of the same matrix

At any nonnegative hard cutoff, the soft remainder is bounded by the hard remainder plus
an explicit uniform low-band error. Functional calculus then gives the corresponding
vector-norm estimate without a global small-norm assumption on the truncation error.
This is a one-direction auxiliary for ALVV, arXiv:1602.08828v2, `lem:exp-approx`,
lines 1195–1255. It does not assert the printed uniform energy estimate, a reverse
spectral comparison, or the final efficient-filter theorem.
-/

namespace Real

/-- The soft residual is bounded by a hard residual and the existing polynomial remainder
at the hard cutoff. The order and independent scale remain explicit. Auxiliary to ALVV,
arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem softTruncation_remainder_le_hard_remainder
    (t : ℝ) (m : ℕ) (T x : ℝ) (ht : 0 < t) (hm : 1 ≤ m)
    (hT : 0 ≤ T) (hx : 0 ≤ x) :
    0 ≤ x - softTruncation t m x ∧
      x - softTruncation t m x ≤ x - min x T + (t / (m : ℝ)) * (T / t) ^ m := by
  have hb := softTruncation_bounds t m x ht hm hx
  refine ⟨sub_nonneg.mpr hb.2.1, ?_⟩
  by_cases hxT : x ≤ T
  · rw [min_eq_left hxT, sub_self, zero_add]
    exact hb.2.2.1.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg hx ht.le)
        (div_le_div_of_nonneg_right hxT ht.le) m) (by positivity))
  · have hTx : T ≤ x := (lt_of_not_ge hxT).le
    rw [min_eq_right hTx]
    have hmono := monotoneOn_softTruncation t m ht hT hx hTx
    have hband := (softTruncation_bounds t m T ht hm hT).2.2.1
    linarith only [hmono, hband]

end Real

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

/-- The soft residual on any vector is bounded by the hard residual of the same positive
matrix, plus an explicit uniform low-band error. This does not assume that the residual
has small global operator norm. Auxiliary to ALVV, arXiv:1602.08828v2,
`lem:exp-approx`, lines 1195–1255. -/
theorem PosSemidef.norm_softTruncation_residual_apply_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (t : ℝ) (m : ℕ) (T : ℝ)
    (ht : 0 < t) (hm : 1 ≤ m) (hT : 0 ≤ T) (v : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)
        (A - cfc (Real.softTruncation t m) A) v‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (A - energyTruncation A T) v‖ +
        ((t / (m : ℝ)) * (T / t) ^ m) * ‖v‖ := by
  let E := (t / (m : ℝ)) * (T / t) ^ m
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hc (u : ℝ → ℝ) : ContinuousOn u (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn u
  have hcomp := norm_cfc_apply_le_of_nonneg_le (A := A)
    (fun x ↦ x - Real.softTruncation t m x) (fun x ↦ x - min x T + E)
    (fun x hx ↦ (Real.softTruncation_remainder_le_hard_remainder
      t m T x ht hm hT (spectrum_nonneg_of_nonneg hA.nonneg hx)).1)
    (fun x hx ↦ (Real.softTruncation_remainder_le_hard_remainder
      t m T x ht hm hT (spectrum_nonneg_of_nonneg hA.nonneg hx)).2) v
  have hid := cfc_id' ℝ A hA.isHermitian.isSelfAdjoint
  have hconst : cfc (fun _ : ℝ ↦ E) A = (E : ℂ) • 1 := by
    rw [cfc_const E A hA.isHermitian.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  rw [cfc_sub _ _ A (hc _) (hc _), hid,
    cfc_add A (fun x : ℝ ↦ x - min x T) (fun _ : ℝ ↦ E) (hc _) (hc _),
    cfc_sub _ _ A (hc _) (hc _), hid, hconst] at hcomp
  change ‖toEuclideanCLM (𝕜 := ℂ) (n := ι) (A - cfc (Real.softTruncation t m) A) v‖ ≤ _
  refine hcomp.trans ?_
  rw [map_add, _root_.add_apply]
  refine (norm_add_le _ _).trans ?_
  rw [map_smul, _root_.smul_apply, map_one, one_apply_eq_self, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
  exact le_refl _

end Matrix
