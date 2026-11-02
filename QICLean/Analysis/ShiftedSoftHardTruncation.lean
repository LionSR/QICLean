/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SoftHardTruncation

/-!
# Soft truncation with an approximate energy origin

The soft truncation in ALVV, arXiv:1602.08828v2, Definition `def:soft-trunc`,
lines 1178–1185, uses an energy estimate within ten units below the regional
ground energy. The affine comparison proved here makes that ten-unit loss
explicit in the threshold of the hard comparator. It is an auxiliary order
comparison, rather than the physical spectral-subspace approximation.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

/-- Increasing the cutoff increases the hard truncation of a fixed matrix.
Auxiliary to ALVV, arXiv:1602.08828v2, Definition `def:hard-trunc`,
lines 873–886. -/
lemma monotone_energyTruncation
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Monotone (energyTruncation A) := by
  intro s t hst
  exact cfc_mono (fun x _hx ↦ min_le_min_left x hst)

/-- Shifting the energy origin translates the hard cutoff by the same amount.
Auxiliary to ALVV, arXiv:1602.08828v2, Definitions `def:hard-trunc` and
`def:soft-trunc`, lines 873–886 and 1178–1185. -/
lemma IsHermitian.energyTruncation_sub_smul_one
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (r t : ℝ) :
    energyTruncation (A - (r : ℂ) • 1) t =
      energyTruncation A (r + t) - (r : ℂ) • 1 := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  have hid : cfc (fun x : ℝ ↦ x - r) A = A - (r : ℂ) • 1 := by
    rw [cfc_sub _ _ A (hc _) (hc _), cfc_id' ℝ A hA.isSelfAdjoint,
      cfc_const r A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  rw [energyTruncation, ← hid, ← cfc_comp (fun x : ℝ ↦ min x t)
    (fun x : ℝ ↦ x - r) A hA.isSelfAdjoint]
  have hconst : (r : ℂ) • (1 : Matrix n n ℂ) = cfc (fun _ : ℝ ↦ r) A := by
    rw [cfc_const r A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  rw [energyTruncation, hconst, ← cfc_sub _ _ A (hc _) (hc _)]
  congr 1
  funext x
  simpa only [Function.comp_apply, add_sub_cancel_left] using
    (min_sub_sub_right x (r + t) r)

/-- A soft truncation with an energy origin at most ten units below `r`
dominates the hard cap at `r + t / 2 - 10`, up to the same exponentially
small scalar error. Auxiliary to ALVV, arXiv:1602.08828v2,
Definition `def:soft-trunc`, lines 1178–1185. Positivity of the shifted
matrix is explicit; no spectral-subspace comparison is concluded. -/
lemma IsHermitian.softTruncation_shifted_hard_bounds
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (r r' t : ℝ) (m : ℕ)
    (hpos : (A - (r' : ℂ) • 1).PosSemidef) (hrr' : r - 10 ≤ r')
    (ht : 0 < t) (hm : 1 ≤ m) :
    energyTruncation A (r + t / 2 - 10) -
        (((t / 2) * (1 / 2 : ℝ) ^ m : ℝ) : ℂ) • 1 ≤
      (r' : ℂ) • 1 + cfc (Real.softTruncation t m) (A - (r' : ℂ) • 1) ∧
    (r' : ℂ) • 1 + cfc (Real.softTruncation t m) (A - (r' : ℂ) • 1) ≤ A := by
  obtain ⟨hl, hu⟩ := hpos.softTruncation_hard_bounds t m ht hm
  rw [hA.energyTruncation_sub_smul_one r' (t / 2), sub_right_comm] at hl
  have hcut := monotone_energyTruncation A
    (show r + t / 2 - 10 ≤ r' + t / 2 by linarith)
  constructor
  · refine (sub_le_sub_right hcut _).trans ?_
    exact sub_le_iff_le_add'.mp hl
  · exact le_sub_iff_add_le'.mp hu

end Matrix
