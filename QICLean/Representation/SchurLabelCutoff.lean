/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchurLabelTails
import QICLean.Analysis.ShiftedDensityTruncation
import QICLean.Analysis.OrthogonalResolutionCfc

/-! # The closed spectral cutoff of the Schur-label observable

The finite sum of selected label projections is exactly the closed spectral
cutoff used in the rough upper comparison.

## References

* OpenAI area-law manuscript, `07-comparators.tex`, lines 332–354.
-/

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]

/-- The finite label sum is the closed lower spectral cutoff, including labels
exactly at the threshold. OpenAI area-law manuscript, `07-comparators.tex`,
lines 332–354. -/
theorem labelCutoff_eq_spectralProjectionGE (φ : G →* Equiv.Perm X) (a : ℝ) :
    labelCutoff φ a = Matrix.spectralProjectionGE (-labelEntropy φ) (-a) := by
  classical
  let R := isOrthogonalResolution_labelProj φ
  have hneg : -labelEntropy φ = R.hom (fun l ↦ ((-Real.log l.dim : ℝ) : ℂ)) := by
    simp only [Matrix.IsOrthogonalResolution.hom_apply, labelEntropy,
      labelObservable, Finset.sum_neg_distrib, neg_smul, Complex.ofReal_neg]
  rw [Matrix.spectralProjectionGE, hneg,
    Matrix.IsOrthogonalResolution.cfc_hom R (isHermitian_labelProj φ)]
  simp only [neg_le_neg_iff, labelCutoff, labelObservable,
    Matrix.IsOrthogonalResolution.hom_apply]

end PermutationRepresentation
