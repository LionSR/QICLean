/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.GroupedCopies
import QICLean.Representation.TensorPowerAction

/-!
# Dimensions of labels occurring on the bad copies

A label which occurs for the permutations of a specified group of \(r\) copies
has dimension at most \(d^r\), even when the representation is considered on the
whole space of \(k\) copies. This is the bad-copy dimension bound used in
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 490–493, equation `comparator:good-auxiliary`.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open Matrix PermutationRepresentation

namespace TensorPower

variable {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    {C : Type*} [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
private theorem bad_copy_perm_condition (σ : Equiv.Perm (Fin r)) (x y : Fin k → C) :
    copyPerm C k (groupHom₂ e σ) y = x ↔
    (fun i : Fin m => x (e (Sum.inl i))) = (fun i => y (e (Sum.inl i))) ∧
    copyPerm C r σ (fun i => y (e (Sum.inr i))) = (fun i => x (e (Sum.inr i))) := by
  have hgood (i : Fin m) : ((copyPerm C k).comp (groupHom₂ e)) σ y (e (Sum.inl i)) =
      y (e (Sum.inl i)) := by
    simp [MonoidHom.coe_comp, copyPerm_apply, groupHom₂, youngHom,
      Equiv.permCongrHom, Equiv.permCongr_def, Equiv.Perm.one_def]
  have hbad (i : Fin r) : ((copyPerm C k).comp (groupHom₂ e)) σ y (e (Sum.inr i)) =
      copyPerm C r σ (fun i => y (e (Sum.inr i))) i := by
    simp [MonoidHom.coe_comp, copyPerm_apply, groupHom₂, youngHom,
      Equiv.permCongrHom, Equiv.permCongr_def]
  constructor
  · exact fun h => ⟨funext (fun i => (congrFun h (e (Sum.inl i))).symm.trans (hgood i)),
      funext (fun i => (hbad i).symm.trans (congrFun h (e (Sum.inr i))))⟩
  · rintro ⟨hg, hb⟩
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    cases j with
    | inl i => exact (hgood i).trans (congrFun hg i).symm
    | inr i => exact (hbad i).trans (congrFun hb i)

private theorem bad_copy_labelProj_entry (β : IrrepLabel (Equiv.Perm (Fin r)))
    (x y : Fin k → C) :
    labelProj ((copyPerm C k).comp (groupHom₂ e)) β x y =
      if (fun i : Fin m => x (e (Sum.inl i))) = (fun i => y (e (Sum.inl i))) then
        labelProj (copyPerm C r) β (fun i => x (e (Sum.inr i)))
          (fun i => y (e (Sum.inr i))) else 0 := by
  classical
  by_cases hg : (fun i : Fin m => x (e (Sum.inl i))) = (fun i => y (e (Sum.inl i)))
  all_goals simp [labelProj, groupAlgebraRep_eq_sum, Matrix.sum_apply, Matrix.smul_apply,
    permOp_apply_apply, bad_copy_perm_condition, hg]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:good-auxiliary, lines 490–493.
-/

/-- A label occurring in the actual bad-copy action on the whole copy space has
dimension at most the dimension of the bad-copy tensor power.
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 490–493, equation `comparator:good-auxiliary`. The good-copy factors remain
in the representation space; their multiplicity does not enter the bound. -/
theorem groupHom₂_labelProj_dim_le (β : IrrepLabel (Equiv.Perm (Fin r)))
    (hβ : labelProj ((copyPerm C k).comp (groupHom₂ e)) β ≠ 0) :
    β.dim ≤ Fintype.card C ^ r := by
  classical
  have hr : labelProj (copyPerm C r) β ≠ 0 := by
    intro hz
    apply hβ
    ext x y
    simp [bad_copy_labelProj_entry e β, hz]
  let W := LinearMap.range (Matrix.toLin' (labelProj (copyPerm C r) β))
  have hW : ∀ g, ∀ w ∈ W, permOp (copyPerm C r) g *ᵥ w ∈ W := by
    intro g w hw
    obtain ⟨v, rfl⟩ := hw
    refine ⟨permOp (copyPerm C r) g *ᵥ v, ?_⟩
    simp only [Matrix.toLin'_apply, mulVec_mulVec]
    rw [(commute_labelProj_permOp (copyPerm C r) β g).eq]
  have hfix : ∀ w ∈ W, labelProj (copyPerm C r) β *ᵥ w = w := by
    intro w hw
    obtain ⟨v, rfl⟩ := hw
    simp only [Matrix.toLin'_apply, mulVec_mulVec, labelProj_mul_self]
  have hne : W ≠ ⊥ := by
    rw [Ne, LinearMap.range_eq_bot, ← map_zero Matrix.toLin', Matrix.toLin'.injective.eq_iff]
    exact hr
  calc
    β.dim ≤ Module.finrank ℂ W := dim_le_finrank_of_invariant (copyPerm C r) β hW hfix hne
    _ ≤ Module.finrank ℂ ((Fin r → C) → ℂ) := W.finrank_le
    _ = Fintype.card C ^ r := by simp

end TensorPower
