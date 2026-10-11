/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchurSurprisal

/-! # Supported spectral tails of Schur labels

OpenAI area-law manuscript, `07-comparators.tex`, lines 332–343. The lower
spectral cutoff is the sum of the actual Schur-label projections. Comparison
with surprisal uses the support of the density matrix and permits a kernel.
-/

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]

/-- The spectral projection onto Schur labels with logarithmic dimension at
most `a`. OpenAI area-law manuscript, `07-comparators.tex`, lines 332–343. -/
def labelCutoff (φ : G →* Equiv.Perm X) (a : ℝ) : Matrix X X ℂ :=
  labelObservable φ fun l ↦ if Real.log l.dim ≤ a then 1 else 0

/-- Supported Schur-label tails are bounded by the actual surprisal tails.
OpenAI area-law manuscript, `07-comparators.tex`, lines 339–343, using
Lemma 6.1(5). Zero eigenvalues contribute no mass. -/
theorem re_trace_mul_one_sub_labelCutoff_le (φ : G →* Equiv.Perm X)
    {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hinv : ∀ g, Commute (permOp φ g) ρ) (a : ℝ) :
    (ρ * (1 - labelCutoff φ a)).trace.re ≤
      (ρ * hρ.isHermitian.cfc (fun u ↦ if a < -Real.log u then 1 else 0)).trace.re := by
  let R := isOrthogonalResolution_joint hρ hinv
  have hρR : ρ = R.hom (fun p ↦ ((p.1 : ℝ) : ℂ)) := by
    simpa only [Matrix.IsHermitian.cfc_id, id_eq, R] using
      (joint_hom_fst hρ hinv id).symm
  have horder : (R.hom (fun p ↦ (((p.1 : ℝ) *
      ((if a < -Real.log p.1 then 1 else 0) -
        (1 - if Real.log p.2.dim ≤ a then 1 else 0)) : ℝ) : ℂ))).PosSemidef := by
    refine R.posSemidef_hom_of_ne_zero (isHermitian_joint hρ hinv) fun p hp ↦ ?_
    by_cases hu : (p.1 : ℝ) = 0
    · simp [hu]
    · have hu' : 0 < (p.1 : ℝ) :=
        lt_of_le_of_ne (eigenvalue_nonneg hρ p.1) (Ne.symm hu)
      have hlog := Real.log_le_log
        (mul_pos hu' (by exact_mod_cast p.2.dim_pos))
        (mul_dim_le_one_of_ne_zero hρ hinv htr p hp)
      rw [Real.log_mul hu (by exact_mod_cast p.2.dim_pos.ne'), Real.log_one] at hlog
      split_ifs <;> nlinarith
  have heq : (fun p : hρ.isHermitian.eigenvalueSet × IrrepLabel G ↦
      (((p.1 : ℝ) * ((if a < -Real.log p.1 then 1 else 0) -
        (1 - if Real.log p.2.dim ≤ a then 1 else 0)) : ℝ) : ℂ)) =
      (fun p ↦ ((p.1 : ℝ) : ℂ)) *
        ((fun p ↦ ((if a < -Real.log p.1 then 1 else 0 : ℝ) : ℂ)) -
          (1 - fun p ↦ ((if Real.log p.2.dim ≤ a then 1 else 0 : ℝ) : ℂ))) := by
    funext p
    push_cast
    rfl
  rw [heq, map_mul, map_sub, map_sub, map_one] at horder
  rw [← hρR, joint_hom_fst hρ hinv (fun u ↦ if a < -Real.log u then 1 else 0),
    joint_hom_snd hρ hinv (fun l ↦ if Real.log l.dim ≤ a then 1 else 0)] at horder
  simpa only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg, labelCutoff]
    using (Complex.nonneg_iff.mp horder.trace_nonneg).1

end PermutationRepresentation
