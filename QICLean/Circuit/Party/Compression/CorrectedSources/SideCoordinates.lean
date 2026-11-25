/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.CorrectedSources.InputVectors

/-!
# Coordinates of the free source slots on the two sides of the affected parties

For a set `S` of source positions with affected parties `correctedMask w S`, a configuration of
the free-slot system consists of the pairs of coordinates of the corrected slots, the two
coordinates of every crossing slot, and a base configuration. Grouped by the two sides of the
affected parties (`freeSideCoordinates`), the affected side holds the pairs of the corrected
slots, the affected coordinates of the crossing slots and the affected base configuration; the
exterior side holds the exterior coordinates of the crossing slots and the exterior base
configuration. The side coordinates determine the configuration, the affected ones depend only
on the configuration of the affected parties, and the exterior ones only on the configuration of
the exterior.

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.freeSideCoordinates`.

## Main results

* `QuantumCircuit.Party.pairFactorConfigEquiv_fst_congr`,
  `QuantumCircuit.Party.SourceInventory.freeSlotColumnEquiv_fst_congr` and their companions: a
  slot coordinate is read at one endpoint of the slot.
* `QuantumCircuit.Party.SourceCircuit.crossingSlotEquiv_congr`.
* `QuantumCircuit.Party.SourceCircuit.correctedMask_meets`,
  `QuantumCircuit.Party.SourceCircuit.isSome_selectedPartialSlot`,
  `QuantumCircuit.Party.SourceCircuit.isSome_crossingSlot`.
* `QuantumCircuit.Party.SourceCircuit.freeSideCoordinates_injective`,
  `QuantumCircuit.Party.SourceCircuit.freeSideCoordinates_fst_congr`,
  `QuantumCircuit.Party.SourceCircuit.freeSideCoordinates_snd_congr`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 342–364 and 409–434.
-/

open Matrix ManyBody

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Slot coordinates read at the endpoints -/

section PairFactor

variable {p q : P} (hpq : p ≠ q) (A B : Type)

/-- The first coordinate of a configuration of the fresh factors is read at the first party. -/
theorem pairFactorConfigEquiv_fst_congr {g g' : Config (pairFactor hpq A B)} (h : g p = g' p) :
    (pairFactorConfigEquiv hpq A B g).1 = (pairFactorConfigEquiv hpq A B g').1 := by
  change cast _ (g p) = cast _ (g' p)
  rw [h]

/-- The second coordinate of a configuration of the fresh factors is read at the second
party. -/
theorem pairFactorConfigEquiv_snd_congr {g g' : Config (pairFactor hpq A B)} (h : g q = g' q) :
    (pairFactorConfigEquiv hpq A B g).2 = (pairFactorConfigEquiv hpq A B g').2 := by
  change cast _ (g q) = cast _ (g' q)
  rw [h]

end PairFactor

namespace SourceInventory

variable (R : SourceInventory P) (B : SlotBases R.length) (f : Fin R.length → Bool)
  (Z : P → Type)

/-- The left coordinate of a free slot is read at the left endpoint of the slot. -/
theorem freeSlotColumnEquiv_fst_congr {y y' : Config (freeSlotSystem R B f Z)}
    (j : {i // f i = true}) (h : y (R.get j).left = y' (R.get j).left) :
    ((freeSlotColumnEquiv R B f Z y).1 j).1 = ((freeSlotColumnEquiv R B f Z y').1 j).1 := by
  rw [freeSlotColumnEquiv_eq_siteEquiv, freeSlotColumnEquiv_eq_siteEquiv]
  exact pairFactorConfigEquiv_fst_congr _ _ _ (by rw [h])

/-- The right coordinate of a free slot is read at the right endpoint of the slot. -/
theorem freeSlotColumnEquiv_snd_congr {y y' : Config (freeSlotSystem R B f Z)}
    (j : {i // f i = true}) (h : y (R.get j).right = y' (R.get j).right) :
    ((freeSlotColumnEquiv R B f Z y).1 j).2 = ((freeSlotColumnEquiv R B f Z y').1 j).2 := by
  rw [freeSlotColumnEquiv_eq_siteEquiv, freeSlotColumnEquiv_eq_siteEquiv]
  exact pairFactorConfigEquiv_snd_congr _ _ _ (by rw [h])

/-- The base coordinate of a party is read at the party. -/
theorem freeSlotColumnEquiv_base_congr {y y' : Config (freeSlotSystem R B f Z)} (q : P)
    (h : y q = y' q) :
    (freeSlotColumnEquiv R B f Z y).2 q = (freeSlotColumnEquiv R B f Z y').2 q := by
  rw [freeSlotColumnEquiv_eq_siteEquiv, freeSlotColumnEquiv_eq_siteEquiv]
  change (freeSlotSiteEquiv R B f Z q (y q)).2 = (freeSlotSiteEquiv R B f Z q (y' q)).2
  rw [h]

end SourceInventory

/-! ### The two sides of a crossing slot -/

namespace SourceCircuit

variable {X Y : P → Type} (w : SourceCircuit X Y) (S : Finset w.sourceLocations)

local notation "mask" => correctedMask w S
local notation "slots" => selectedPartialSlots mask w S
local notation "cross" => crossingSlots w S
local notation "basis" => partialSlotBases mask w
local notation "Free" => {i // correctedFreeSlots w S i = true}

/-- The two coordinates of a crossing slot on the affected and on the exterior side each depend
on one of its two endpoint coordinates only: the affected coordinate is the left one when the
left endpoint is affected, and the right one otherwise. Source: Theorem 5.2,
`04-compression.tex`, lines 409–434. -/
theorem crossingSlotEquiv_congr (i : cross) (x x' : (basis).left i × (basis).right i) :
    ((mask (w.endpoints (partialSlotEquiv mask w i).1).1 = true → x.1 = x'.1) →
      (mask (w.endpoints (partialSlotEquiv mask w i).1).1 = false → x.2 = x'.2) →
        (w.crossingSlotEquiv S i x).1 = (w.crossingSlotEquiv S i x').1) ∧
    ((mask (w.endpoints (partialSlotEquiv mask w i).1).1 = true → x.2 = x'.2) →
      (mask (w.endpoints (partialSlotEquiv mask w i).1).1 = false → x.1 = x'.1) →
        (w.crossingSlotEquiv S i x).2 = (w.crossingSlotEquiv S i x').2) := by
  by_cases h : mask (w.endpoints (partialSlotEquiv mask w i).1).1 = true
  · rw [w.crossingSlotEquiv_apply_of_left S i h x, w.crossingSlotEquiv_apply_of_left S i h x']
    exact ⟨fun h₁ _ ↦ by rw [h₁ h], fun h₁ _ ↦ by rw [h₁ h]⟩
  · have h' : mask (w.endpoints (partialSlotEquiv mask w i).1).1 = false := by simpa using h
    rw [w.crossingSlotEquiv_apply_of_right S i h x, w.crossingSlotEquiv_apply_of_right S i h x']
    exact ⟨fun _ h₂ ↦ by rw [h₂ h'], fun _ h₂ ↦ by rw [h₂ h']⟩

/-- Every corrected position has an affected endpoint. Source: Theorem 5.2,
`04-compression.tex`, lines 342–364. -/
theorem correctedMask_meets :
    ∀ e ∈ S, mask (w.endpoints e).1 = true ∨ mask (w.endpoints e).2 = true := fun e he ↦
  Or.inl (decide_eq_true ((GateIncidence.mem_correctedParties _ _ _).2 ⟨e, he, Or.inl rfl⟩))

/-- Both endpoints of the slot of a corrected source are affected. -/
theorem isSome_selectedPartialSlot (i : Fin (partialSlots mask w).length) (hi : i ∈ slots) :
    ((partialSlots mask w).get i).left.isSome = true ∧
      ((partialSlots mask w).get i).right.isSome = true := by
  have he := (mem_selectedPartialSlots mask w S i).mp hi
  rw [(partialSlot_spec mask w i).1, (partialSlot_spec mask w i).2, isSome_affectedOwner,
    isSome_affectedOwner]
  exact ⟨decide_eq_true ((GateIncidence.mem_correctedParties _ _ _).2 ⟨_, he, Or.inl rfl⟩),
    decide_eq_true ((GateIncidence.mem_correctedParties _ _ _).2 ⟨_, he, Or.inr rfl⟩)⟩

/-- The two endpoints of a crossing slot lie on the sides given by the two endpoints of its
position, which differ. -/
theorem isSome_crossingSlot (i : cross) :
    ((partialSlots mask w).get i).left.isSome =
        mask (w.endpoints (partialSlotEquiv mask w i).1).1 ∧
      ((partialSlots mask w).get i).right.isSome =
        !mask (w.endpoints (partialSlotEquiv mask w i).1).1 := by
  have hne : mask (w.endpoints (partialSlotEquiv mask w i).1).1 ≠
      mask (w.endpoints (partialSlotEquiv mask w i).1).2 := (Finset.mem_filter.mp i.2).2
  rw [(partialSlot_spec mask w i).1, (partialSlot_spec mask w i).2, isSome_affectedOwner,
    isSome_affectedOwner]
  refine ⟨rfl, ?_⟩
  revert hne
  cases mask (w.endpoints (partialSlotEquiv mask w i).1).1 <;>
    cases mask (w.endpoints (partialSlotEquiv mask w i).1).2 <;> simp

variable [Fintype P]

local notation "side" => fun (o : Option {p // correctedMask w S p = true}) ↦ Option.isSome o
local notation "Zx" => blockSystem (affectedOwner mask) X
local notation "FS" => SourceInventory.freeSlotSystem (partialSlots mask w) basis
  (correctedFreeSlots w S) (blockSystem (affectedOwner mask) X)

/-- The coordinates of a configuration of the free-slot system, grouped by the two sides of the
affected parties: on the affected side the pairs of the corrected slots, the affected
coordinates of the crossing slots and the affected base configuration; on the exterior side the
exterior coordinates of the crossing slots and the exterior base configuration. Source:
Theorem 5.2, `04-compression.tex`, lines 409–434. -/
noncomputable def freeSideCoordinates (y : Config FS) :
    (((∀ i : slots, (basis).left i × (basis).right i) ×
        (∀ i : cross, w.crossingSlotBasis S i true)) ×
      RegionConfig (blockSystem side Zx) {true}) ×
    ((∀ i : cross, w.crossingSlotBasis S i false) × ComplConfig (blockSystem side Zx) {true}) :=
  let t := SourceInventory.freeSlotColumnEquiv (partialSlots mask w) basis
    (correctedFreeSlots w S) Zx y
  let a := fun i : slots ↦ t.1 ((w.correctedFreeSlotEquiv S).symm (.inl i))
  let b := fun i : cross ↦ t.1 ((w.correctedFreeSlotEquiv S).symm (.inr i))
  let z := cutEquiv (blockSystem side Zx) {true} ((blockConfigEquiv side Zx).symm t.2)
  (((a, fun i ↦ (w.crossingSlotEquiv S i (b i)).1), z.1),
    ((fun i ↦ (w.crossingSlotEquiv S i (b i)).2), z.2))

/-- The side coordinates determine the configuration. -/
theorem freeSideCoordinates_injective : Function.Injective (w.freeSideCoordinates S) := by
  intro y y' h
  apply (SourceInventory.freeSlotColumnEquiv (partialSlots mask w) basis
    (correctedFreeSlots w S) Zx).injective
  have ha := congrArg (fun c ↦ c.1.1.1) h
  have hl := congrArg (fun c ↦ c.1.1.2) h
  have hzA := congrArg (fun c ↦ c.1.2) h
  have hr := congrArg (fun c ↦ c.2.1) h
  have hzE := congrArg (fun c ↦ c.2.2) h
  refine Prod.ext (funext fun j ↦ ?_) ?_
  · obtain ⟨k, rfl⟩ := (w.correctedFreeSlotEquiv S).symm.surjective j
    cases k with
    | inl i => exact congrFun ha i
    | inr i =>
      exact (w.crossingSlotEquiv S i).injective (Prod.ext (congrFun hl i) (congrFun hr i))
  · exact (blockConfigEquiv side Zx).symm.injective
      ((cutEquiv (blockSystem side Zx) {true}).injective (Prod.ext hzA hzE))

/-- The affected side coordinates depend only on the configuration of the affected parties. -/
theorem freeSideCoordinates_fst_congr {y y' : Config FS}
    (h : ∀ q : Option {p // mask p = true}, q.isSome = true → y q = y' q) :
    (w.freeSideCoordinates S y).1 = (w.freeSideCoordinates S y').1 := by
  refine Prod.ext (Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_))
    (funext fun b ↦ funext fun q ↦ ?_)
  · have hi := w.isSome_selectedPartialSlot S i i.2
    exact Prod.ext
      (SourceInventory.freeSlotColumnEquiv_fst_congr _ _ _ _
        ((w.correctedFreeSlotEquiv S).symm (.inl i)) (h _ hi.1))
      (SourceInventory.freeSlotColumnEquiv_snd_congr _ _ _ _
        ((w.correctedFreeSlotEquiv S).symm (.inl i)) (h _ hi.2))
  · have hi := w.isSome_crossingSlot S i
    exact (w.crossingSlotEquiv_congr S i _ _).1
      (fun hm ↦ SourceInventory.freeSlotColumnEquiv_fst_congr _ _ _ _
        ((w.correctedFreeSlotEquiv S).symm (.inr i)) (h _ (hi.1.trans hm)))
      (fun hm ↦ SourceInventory.freeSlotColumnEquiv_snd_congr _ _ _ _
        ((w.correctedFreeSlotEquiv S).symm (.inr i)) (h _ (hi.2.trans (by rw [hm]; rfl))))
  · have hq : (q : Option {p // mask p = true}).isSome = true :=
      ((mem_blockPreimage_singleton side).mp q.2).trans (Finset.mem_singleton.mp b.2)
    exact SourceInventory.freeSlotColumnEquiv_base_congr _ _ _ _ q.1 (h _ hq)

/-- The exterior side coordinates depend only on the configuration of the exterior. -/
theorem freeSideCoordinates_snd_congr {y y' : Config FS}
    (h : ∀ q : Option {p // mask p = true}, q.isSome = false → y q = y' q) :
    (w.freeSideCoordinates S y).2 = (w.freeSideCoordinates S y').2 := by
  refine Prod.ext (funext fun i ↦ ?_) (funext fun b ↦ funext fun q ↦ ?_)
  · have hi := w.isSome_crossingSlot S i
    exact (w.crossingSlotEquiv_congr S i _ _).2
      (fun hm ↦ SourceInventory.freeSlotColumnEquiv_snd_congr _ _ _ _
        ((w.correctedFreeSlotEquiv S).symm (.inr i)) (h _ (hi.2.trans (by rw [hm]; rfl))))
      (fun hm ↦ SourceInventory.freeSlotColumnEquiv_fst_congr _ _ _ _
        ((w.correctedFreeSlotEquiv S).symm (.inr i)) (h _ (hi.1.trans hm)))
  · have hb : (b : Bool) = false := by
      have := b.2
      simpa using this
    have hq : (q : Option {p // mask p = true}).isSome = false :=
      ((mem_blockPreimage_singleton side).mp q.2).trans hb
    exact SourceInventory.freeSlotColumnEquiv_base_congr _ _ _ _ q.1 (h _ hq)

end SourceCircuit

end QuantumCircuit.Party
