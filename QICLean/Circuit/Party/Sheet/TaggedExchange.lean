/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Sheet.BoundedChanges

/-!
# Relabelling the tags in a two-sheet exchange

An exchange across a region moves both the sites in the region and the tags of the holes
lying in the region. Split the tags of each party on each sheet into outside and inside
factors. The relabelling exchanges the inside factors and leaves the outside factors at
their original places. Each tag keeps its owner.

This is the relabelling of Lemma 6.6 of the polynomial-PEPS manuscript (September 24,
2026), `05-frames.tex`, lines 485–497. The tags of an encoded frame admit the required
split when every hole lies entirely inside or entirely outside the region.
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit.Party.Sheet

/-- The output-to-input identification for the two pairs of outside and inside tag bases.
The first component of each pair is the outside tag. -/
def swapInsideTags (O₁ I₁ O₂ I₂ : Type) :
    ((O₁ × I₂) × (O₂ × I₁)) ≃ ((O₁ × I₁) × (O₂ × I₂)) where
  toFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
  invFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable {ι P : Type} [Fintype ι] [DecidableEq ι] [DecidableEq P] {q : ℕ}
  (S₁ S₂ : Sheet ι P) (Y : Finset ι) (O₁ I₁ O₂ I₂ : P → Type)
  [∀ p, Fintype (O₁ p)] [∀ p, DecidableEq (O₁ p)]
  [∀ p, Fintype (I₁ p)] [∀ p, DecidableEq (I₁ p)]
  [∀ p, Fintype (O₂ p)] [∀ p, DecidableEq (O₂ p)]
  [∀ p, Fintype (I₂ p)] [∀ p, DecidableEq (I₂ p)]

/-- Relabel both sheets as well as the tags of the holes inside the exchange region.
Source: polynomial-PEPS, Lemma 6.6, `05-frames.tex`, lines 485–497. -/
noncomputable def taggedRenameWord :
    Word (fun p ↦ ((O₁ p × I₁ p) × (O₂ p × I₂ p)) × (S₁.system q p × S₂.system q p))
      (fun p ↦ ((O₁ p × I₂ p) × (O₂ p × I₁ p)) ×
        ((swapIn S₁ S₂ Y).system q p × (swapIn S₂ S₁ Y).system q p)) :=
  PartyCircuit.relabel fun p ↦
    (swapInsideTags (O₁ p) (I₁ p) (O₂ p) (I₂ p)).prodCongr (swapInEquiv S₁ S₂ Y p)

/-- The tagged relabelling has no pair source. -/
theorem sourceCount_taggedRenameWord :
    (taggedRenameWord (q := q) S₁ S₂ Y O₁ I₁ O₂ I₂).sourceCount = 0 :=
  rfl

/-- The change of tag and site coordinates is an allowed word. -/
theorem isAllowed_taggedRenameWord :
    (taggedRenameWord (q := q) S₁ S₂ Y O₁ I₁ O₂ I₂).IsAllowed :=
  Word.isAllowed_relabel _

/-- In tag and site coordinates, the tagged relabelling is the tensor product of the
inside-tag permutation with the relabelling of the two sheets. -/
theorem op_taggedRenameWord [Fintype P] :
    (taggedRenameWord (q := q) S₁ S₂ Y O₁ I₁ O₂ I₂).op =
      reindex (Equiv.arrowProdEquivProdArrow P _ _).symm
        (Equiv.arrowProdEquivProdArrow P _ _).symm
        ((Equiv.piCongrRight fun p ↦ swapInsideTags (O₁ p) (I₁ p) (O₂ p) (I₂ p)).toPEquiv.toMatrix
          ⊗ₖ (renameWord (q := q) S₁ S₂ Y).op) := by
  rw [taggedRenameWord, renameWord, Word.op, Word.op, PartyCircuit.op_relabel,
    PartyCircuit.op_relabel]
  ext y x
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  have h :
      (Equiv.piCongrRight (fun p ↦
        (swapInsideTags (O₁ p) (I₁ p) (O₂ p) (I₂ p)).prodCongr
          (swapInEquiv S₁ S₂ Y p)) y = x) ↔
      (∀ p, swapInsideTags (O₁ p) (I₁ p) (O₂ p) (I₂ p) (y p).1 = (x p).1) ∧
      (∀ p, swapInEquiv S₁ S₂ Y p (y p).2 = (x p).2) := by
    constructor
    · intro hxy
      exact ⟨fun p ↦ congrArg Prod.fst (congrFun hxy p),
        fun p ↦ congrArg Prod.snd (congrFun hxy p)⟩
    · rintro ⟨ht, hs⟩
      exact funext fun p ↦ Prod.ext (ht p) (hs p)
  simp only [Equiv.arrowProdEquivProdArrow_apply, Equiv.piCongrRight_apply, funext_iff] at h ⊢
  rw [if_congr h rfl rfl]
  split_ifs <;> simp_all

end QuantumCircuit.Party.Sheet
