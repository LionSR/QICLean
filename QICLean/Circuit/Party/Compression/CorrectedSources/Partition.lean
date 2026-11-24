/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.CorrectedSources.SelectivePreparation
import QICLean.Circuit.Party.Compression.PartialExpansion.CorrectedCost
import QICLean.Circuit.Party.Compression.PartialExpansion.Residual
import QICLean.Circuit.Party.Compression.PhysicalReadout.Sides

/-!
# The corrected and crossing sources as free inputs

For a set `S` of source positions of a source circuit, with affected parties
`correctedMask w S`, the *free slots* of the partial expansion are the corrected positions
(those of `S`) and the crossing positions (one endpoint affected, the other not). Every other
slot has both endpoints on the same side of the affected parties. Preparing only those slots in
advance, with the vectors of a branch, and then running the residual of the branch, splits into
two local contractions across the two sides, uniformly in the branch and chosen before any free
vector is supplied.

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.correctedFreeSlots`.

## Main results

* `QuantumCircuit.Party.SourceCircuit.correctedFreeSlots_eq_true_iff`,
  `QuantumCircuit.Party.SourceCircuit.exists_correctedFreeSlot`,
  `QuantumCircuit.Party.SourceCircuit.correctedFreeSlots_internal`.
* `QuantumCircuit.Party.SourceCircuit.exists_corrected_source_partition`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 409–434.
-/

noncomputable section

open ManyBody

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type}

open Classical in
/-- The free slots: the corrected positions and every position crossing the boundary of the
affected parties. Source: Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def correctedFreeSlots (w : SourceCircuit X Y) (S : Finset w.sourceLocations) :
    Fin (partialSlots (correctedMask w S) w).length → Bool :=
  fun i ↦ decide ((partialSlotEquiv (correctedMask w S) w i).1 ∈ S ∨
    correctedMask w S (w.endpoints (partialSlotEquiv (correctedMask w S) w i).1).1 ≠
      correctedMask w S (w.endpoints (partialSlotEquiv (correctedMask w S) w i).1).2)

omit [Fintype P] in
/-- The free mask depends only on the original positions and their endpoint sides. Source:
Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem correctedFreeSlots_eq_true_iff (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (i : Fin (partialSlots (correctedMask w S) w).length) :
    correctedFreeSlots w S i = true ↔
      (partialSlotEquiv (correctedMask w S) w i).1 ∈ S ∨
        correctedMask w S (w.endpoints (partialSlotEquiv (correctedMask w S) w i).1).1 ≠
          correctedMask w S (w.endpoints (partialSlotEquiv (correctedMask w S) w i).1).2 := by
  classical
  simp only [correctedFreeSlots, decide_eq_true_eq]

omit [Fintype P] in
/-- Every corrected position is represented by a free slot. Source: Theorem 5.2,
`04-compression.tex`, lines 409–434. -/
theorem exists_correctedFreeSlot (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (e : w.sourceLocations) (he : e ∈ S) :
    ∃ i : Fin (partialSlots (correctedMask w S) w).length,
      (partialSlotEquiv (correctedMask w S) w i).1 = e ∧ correctedFreeSlots w S i = true := by
  have hl : correctedMask w S (w.endpoints e).1 = true := by
    simp only [correctedMask, decide_eq_true_eq, GateIncidence.mem_correctedParties]
    exact ⟨e, he, Or.inl rfl⟩
  let j := (partialSlotEquiv (correctedMask w S) w).symm ⟨e, Or.inl hl⟩
  have hj : (partialSlotEquiv (correctedMask w S) w j).1 = e :=
    congrArg Subtype.val ((partialSlotEquiv (correctedMask w S) w).apply_symm_apply _)
  exact ⟨j, hj, (correctedFreeSlots_eq_true_iff w S j).mpr (Or.inl (hj.symm ▸ he))⟩

omit [Fintype P] in
/-- Every slot prepared in advance has both endpoints on the same side of the affected parties.
Source: Theorem 5.2, `04-compression.tex`, lines 409–417. -/
theorem correctedFreeSlots_internal (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (i : Fin (partialSlots (correctedMask w S) w).length) (hi : correctedFreeSlots w S i = false) :
    ((partialSlots (correctedMask w S) w).get i).left.isSome =
      ((partialSlots (correctedMask w S) w).get i).right.isSome := by
  have hnot : ¬ correctedFreeSlots w S i = true := by simp [hi]
  rw [correctedFreeSlots_eq_true_iff] at hnot
  rw [(partialSlot_spec (correctedMask w S) w i).1, (partialSlot_spec (correctedMask w S) w i).2,
    isSome_affectedOwner, isSome_affectedOwner]
  exact not_not.mp (not_or.mp hnot).2

/-- **The corrected and crossing sources are common free inputs of all branches.** Preparing the
other slots with the vectors of a branch, then running the residual of the branch, is tensor
partitioned across the two sides of the affected parties; the free slots do not depend on the
branch. Source: Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem exists_corrected_source_partition [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (w : SourceCircuit X Y)
    (hw : w.IsLocalContractive) (S : Finset w.sourceLocations) :
    ∀ ξ : Choices (correctedMask w S) w,
      Word.IsTensorPartitioned (fun o : Option {p // correctedMask w S p = true} ↦ o.isSome)
        (PartyCircuit.comp
          (SourceInventory.prepareSelected (partialSlots (correctedMask w S) w)
            (partialSlotBases (correctedMask w S) w) (correctedFreeSlots w S)
            (fun i _ ↦ partialSlotVector (correctedMask w S) w ξ i)
            (blockSystem (affectedOwner (correctedMask w S)) X))
          (partialResidual (correctedMask w S) w ξ)) := fun ξ ↦
  (Word.exists_selective_partition _ _ _ _ _
    (fun i _ ↦ norm_partialSlotVector _ w ξ i) (correctedFreeSlots_internal w S) _
    (partialResidual (correctedMask w S) w ξ) (isAllowed_partialResidual _ w hw ξ)
    (sources_partialResidual _ w ξ)).1

end QuantumCircuit.Party.SourceCircuit
