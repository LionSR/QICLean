/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.CorrectedSources.FreeSlotCoordinates
import QICLean.Circuit.Party.Compression.CorrectedSources.InputFrames
import Mathlib.Logic.Equiv.Set

/-!
# The product vector in the free source slots

For a corrected term, the free-source input is the tensor product of the
corrected frame columns and the exact crossing vectors. The identity is
entrywise in the original slot coordinates.

Source: polynomial-PEPS, Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

open Matrix ManyBody

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [DecidableEq P] {X Y : P → Type}
  (w : SourceCircuit X Y) (S : Finset w.sourceLocations)

local notation "mask" => correctedMask w S
local notation "slots" => selectedPartialSlots mask w S
local notation "cross" => crossingSlots w S
local notation "basis" => partialSlotBases mask w
local notation "Free" => {i // correctedFreeSlots w S i = true}

/-- Label a free slot as corrected or crossing, retaining its original index. -/
noncomputable def correctedFreeSlotEquiv : Free ≃ (slots : Type) ⊕ (cross : Type) :=
  (Equiv.subtypeEquivRight (fun i ↦
    (correctedFreeSlots_eq_true_iff_mem_union w S i).trans (by simp [Finset.mem_union]))).trans
    (Equiv.Set.union (by
      exact Set.disjoint_left.mpr fun _ hi hj ↦
        Finset.disjoint_left.mp (disjoint_selectedPartialSlots_crossingSlots w S) hi hj))

variable
  (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
  (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)

/-- When the free-slot preparation is read in its slot coordinates, a branch
input is a corrected frame column times the exact crossing vector. -/
theorem product_partialSchmidtSourceVectors (ξ : Choices mask w)
    (u : PartialSchmidtCoordinates mask w S)
    (x : ∀ i : Free, (basis).left i × (basis).right i) :
    let a := fun i : slots ↦ x ((correctedFreeSlotEquiv w S).symm (.inl i))
    let b := fun i : cross ↦ x ((correctedFreeSlotEquiv w S).symm (.inr i))
    (∏ i : Free, partialSchmidtSourceVectors mask w S E F ξ u i (x i)) =
      w.correctedSourceFrame S E F ξ a u *
        w.sourceCrossingVector S ξ
          ((fun i ↦ (w.crossingSlotEquiv S i (b i)).1),
            (fun i ↦ (w.crossingSlotEquiv S i (b i)).2)) := by
  intro a b
  have hsplit := Fintype.prod_equiv (correctedFreeSlotEquiv w S).symm
    (fun j ↦ partialSchmidtSourceVectors mask w S E F ξ u ((correctedFreeSlotEquiv w S).symm j)
      (x ((correctedFreeSlotEquiv w S).symm j)))
    (fun i : Free ↦ partialSchmidtSourceVectors mask w S E F ξ u i (x i))
    (fun _ ↦ rfl)
  rw [← hsplit, Fintype.prod_sum_type]
  congr 1
  · exact (w.correctedSourceFrame_apply S E F ξ u a).symm
  · have hslot (i : cross) : (i : Fin (partialSlots mask w).length) ∉ slots := fun hi ↦
      Finset.disjoint_left.mp (disjoint_selectedPartialSlots_crossingSlots w S) hi i.2
    change (∏ i : cross, partialSchmidtSourceVectors mask w S E F ξ u i (b i)) = _
    simp only [partialSchmidtSourceVectors, dite_eq_right (hslot _)]
    let e := ((Equiv.piCongrRight (w.crossingSlotEquiv S)).trans
      (Equiv.arrowProdEquivProdArrow _ _ _))
    change (∏ i : cross, partialSlotVector mask w ξ i (b i)) =
      productVector (fun i : cross ↦ (partialSlotVector mask w ξ i).ofLp)
        (e.symm (e b))
    exact congrArg (productVector (fun i : cross ↦ (partialSlotVector mask w ξ i).ofLp))
      (e.symm_apply_apply b).symm

local notation "Z" => blockSystem (affectedOwner mask) X

/-- Preparing the free slots on a base input multiplies the corrected and
crossing factors by its unchanged coefficient. -/
theorem prepareFreeSlots_partialSchmidt_mulVec [Fintype P]
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (ξ : Choices mask w)
    (u : PartialSchmidtCoordinates mask w S) (ψ : Config Z → ℂ)
    (y : Config (SourceInventory.freeSlotSystem (partialSlots mask w) basis
      (correctedFreeSlots w S) Z)) :
    let t := SourceInventory.freeSlotColumnEquiv (partialSlots mask w) basis
      (correctedFreeSlots w S) Z y
    let a := fun i : slots ↦ t.1 ((w.correctedFreeSlotEquiv S).symm (.inl i))
    let b := fun i : cross ↦ t.1 ((w.correctedFreeSlotEquiv S).symm (.inr i))
    ((SourceInventory.prepareFreeSlots (partialSlots mask w) basis (correctedFreeSlots w S)
      (partialSchmidtSourceVectors mask w S E F ξ u) Z).op *ᵥ ψ) y =
      w.correctedSourceFrame S E F ξ a u *
        w.sourceCrossingVector S ξ
          ((fun i ↦ (w.crossingSlotEquiv S i (b i)).1),
            (fun i ↦ (w.crossingSlotEquiv S i (b i)).2)) * ψ t.2 := by
  intro t a b
  rw [SourceInventory.op_prepareFreeSlots]
  simp only [Matrix.mulVec, dotProduct, prepMatrix_apply, ite_mul, zero_mul, Fintype.sum_ite_eq]
  exact congrArg (· * ψ t.2) (w.product_partialSchmidtSourceVectors S E F ξ u t.1)


end QuantumCircuit.Party.SourceCircuit
