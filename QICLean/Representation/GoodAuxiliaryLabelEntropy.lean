/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BadCopyLabelDimension
import QICLean.Representation.GroupedLabelEntropy

/-!
# A whole-space bound for the good auxiliary label observable

For the actual copy-permutation action on a finite coordinate tensor power,
the bad label observable is bounded by the number of bad copies times the
logarithm of the one-copy dimension. Together with the subgroup label
inequality, this bounds the whole observable above by the good observable
plus an explicit scalar multiple of the identity.

This is the operator input to *A two-dimensional area law from a global
spectral gap*, `07-comparators.tex`, lines 481–493, equation
`comparator:good-auxiliary`. The actual physical excitation projection,
preservation of whole-copy auxiliary labels, and the whole-label threshold
are separate assertions. No commutation with the band metric is asserted.
The formulas use the total real logarithm, with \(\log 0=0\); empty
coordinate sets and zero copy groups remain included.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open Matrix PermutationRepresentation
open scoped MatrixOrder

namespace TensorPower

variable {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    {C : Type*} [Fintype C] [DecidableEq C]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:good-auxiliary, lines 481–493.
-/

/-- The actual bad-copy label observable is bounded by the bad-copy ambient
logarithmic dimension. Hence the whole-copy observable is at most the
good-copy observable plus the bad-copy dimension and binomial correction.
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 481–493, equation `comparator:good-auxiliary`. This is a whole-space
operator inequality, before selecting a physical excitation component. -/
theorem copyPerm_groupedCopies_labelEntropy_bounds :
    labelEntropy ((copyPerm C k).comp (groupHom₂ e)) ≤
        ((r : ℝ) * Real.log (Fintype.card C) : ℂ) • 1 ∧
      labelEntropy (copyPerm C k) ≤
        labelEntropy ((copyPerm C k).comp (groupHom₁ e)) +
          ((r : ℝ) * Real.log (Fintype.card C) + Real.log (k.choose r) : ℂ) • 1 := by
  classical
  have hLog : ∀ (β : IrrepLabel (Equiv.Perm (Fin r))),
      labelProj ((copyPerm C k).comp (groupHom₂ e)) β ≠ 0 →
      Real.log β.dim ≤ (r : ℝ) * Real.log (Fintype.card C) := by
    intro β hβ
    have hd : (β.dim : ℝ) ≤ (Fintype.card C : ℝ) ^ r := by
      exact_mod_cast groupHom₂_labelProj_dim_le e β hβ
    simpa only [Real.log_pow] using Real.log_le_log (Nat.cast_pos.mpr β.dim_pos) hd
  let R := isOrthogonalResolution_labelProj ((copyPerm C k).comp (groupHom₂ e))
  have hConst : R.hom (fun _ => ((r : ℝ) * Real.log (Fintype.card C) : ℂ)) =
      ((r : ℝ) * Real.log (Fintype.card C) : ℂ) • 1 := by
    rw [IsOrthogonalResolution.hom_apply, ← Finset.smul_sum, R.sum_eq]
  have hBad : labelEntropy ((copyPerm C k).comp (groupHom₂ e)) ≤
      ((r : ℝ) * Real.log (Fintype.card C) : ℂ) • 1 := by
    rw [Matrix.le_iff, ← hConst, labelEntropy, labelObservable_eq_hom, ← map_sub]
    simpa only [Pi.sub_def, Complex.ofReal_sub, Complex.ofReal_mul] using
      R.posSemidef_hom_of_ne_zero (fun β => isHermitian_labelProj _ β)
        (f := fun β => (r : ℝ) * Real.log (Fintype.card C) - Real.log β.dim)
        (fun β hβ => sub_nonneg.mpr (hLog β hβ))
  refine ⟨hBad, ?_⟩
  have hWhole := (groupedCopies_labelEntropy_bounds e (copyPerm C k)).2
  rw [add_smul, ← add_assoc]
  refine hWhole.trans ?_
  simpa only [Matrix.le_iff, add_sub_add_right_eq_sub, add_sub_add_left_eq_sub] using hBad

end TensorPower
