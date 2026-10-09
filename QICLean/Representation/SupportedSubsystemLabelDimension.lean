/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SubsystemLabelCoordinates
import QICLean.Representation.IsotypicDimension

/-!
# Dimensions of labels occurring on an actual physical subsystem

A label whose projector is nonzero has dimension at most that of the
representation space. For an actual subsystem copy action, the canonical
regional coordinate split removes the complementary multiplicity before
this bound is applied. Thus an occurring label has dimension at most the
regional one-copy dimension raised to the copy number.

The argument includes empty coordinate sets and zero copies. A nonzero
projector supplies exactly the support needed by the dimension estimate;
no nonemptiness, normalization or full-rank premise is introduced.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `05-replicas.tex`, Lemma 6.1(3), lines 105–111,
  and `07-comparators.tex`, lines 356–365, `comparator:actual-cutoffs`,
  manuscript revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation
open scoped Kronecker

noncomputable section

namespace PermutationRepresentation

variable {G Y : Type*} [Group G] [Fintype G] [Fintype Y] [DecidableEq Y]

/-- The dimension of a label occurring in an actual permutation
representation is bounded by its coordinate dimension. This is the
supported dimension step in the nested-label comparison of
`07-comparators.tex`, lines 356–365; it uses the invariant-subspace
dimension theorem of `05-replicas.tex`, lines 223–226. -/
theorem dim_le_card_of_labelProj_ne_zero (φ : G →* Equiv.Perm Y)
    (l : IrrepLabel G) (hl : labelProj φ l ≠ 0) : l.dim ≤ Fintype.card Y := by
  let W := LinearMap.range (Matrix.toLin' (labelProj φ l))
  have hW : ∀ g, ∀ w ∈ W, permOp φ g *ᵥ w ∈ W := by
    intro g w hw
    obtain ⟨v, rfl⟩ := hw
    refine ⟨permOp φ g *ᵥ v, ?_⟩
    simp only [Matrix.toLin'_apply, mulVec_mulVec]
    rw [(commute_labelProj_permOp φ l g).eq]
  have hfix : ∀ w ∈ W, labelProj φ l *ᵥ w = w := by
    intro w hw
    obtain ⟨v, rfl⟩ := hw
    simp only [Matrix.toLin'_apply, mulVec_mulVec, labelProj_mul_self]
  have hne : W ≠ ⊥ := by
    rw [Ne, LinearMap.range_eq_bot, ← map_zero Matrix.toLin', Matrix.toLin'.injective.eq_iff]
    exact hl
  calc
    l.dim ≤ Module.finrank ℂ W := dim_le_finrank_of_invariant φ l hW hfix hne
    _ ≤ Module.finrank ℂ (Y → ℂ) := W.finrank_le
    _ = Fintype.card Y := by simp

end PermutationRepresentation

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  (k : ℕ) (B : Finset F)

/-- An occurring label of the actual B-subsystem action has dimension at
most `(dim H_B)^k`, independently of all complementary coordinates.
Source: `07-comparators.tex`, lines 356–365, together with the merge
dimension inequalities in `05-replicas.tex`, lines 105–111. -/
theorem dim_le_pow_card_of_subsystem_labelProj_ne_zero
    (l : IrrepLabel (Equiv.Perm (Fin k)))
    (hl : labelProj (subsystemPerm k ι B) l ≠ 0) :
    l.dim ≤ Fintype.card (FiniteProduct.Configuration ι B) ^ k := by
  classical
  have hregional : labelProj (copyPerm (FiniteProduct.Configuration ι B) k) l ≠ 0 := by
    intro hz
    apply hl
    ext x y
    have h := congrArg
      (fun M ↦ M (subsystemSplitEquiv ι k B x) (subsystemSplitEquiv ι k B y))
      (labelProj_subsystemPerm_submatrix ι k B l)
    simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply, hz,
      Matrix.kronecker_zero, Matrix.zero_apply] using h
  calc
    l.dim ≤ Fintype.card (Fin k → FiniteProduct.Configuration ι B) :=
      dim_le_card_of_labelProj_ne_zero
        (copyPerm (FiniteProduct.Configuration ι B) k) l hregional
    _ = Fintype.card (FiniteProduct.Configuration ι B) ^ k := by simp

end TensorPower
