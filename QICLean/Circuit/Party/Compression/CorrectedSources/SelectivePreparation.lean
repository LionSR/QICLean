/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.Common
import QICLean.Circuit.Party.Monomial.Stack
import QICLean.Circuit.Party.Compression.CorrectedSources.TensorPartition

/-!
# Selective preparation of source slots

An ordered inventory of pair slots `R` with slot bases `B` is divided by a mask `free` into free
and fixed slots. The *free-slot system* keeps the fresh factors of the free slots, in their
order (`freeSlotSystem`). One word prepares the fixed vectors and carries the free factors along
unchanged (`prepareSelected`); it takes no free vector as an argument. Followed after the
preparation of arbitrary vectors in the free slots (`prepareFreeSlots`), it is the preparation of
all slots with the fixed and the free vectors (`fillSourceVectors`). It is allowed when the fixed
vectors are normalized, and its pair sources are exactly the fixed slots with their original
endpoints. Hence a mask that frees every source crossing two sides leaves only sources internal
to one side, and the selective preparation followed by any source-free word splits into two local
contractions (`exists_selective_partition`).

## Main definitions

* `QuantumCircuit.Party.SourceInventory.selectedSources`,
  `QuantumCircuit.Party.SourceInventory.freeSlotSystem`,
  `QuantumCircuit.Party.SourceInventory.prepareSelected`,
  `QuantumCircuit.Party.SourceInventory.prepareFreeSlots`,
  `QuantumCircuit.Party.SourceInventory.fillSourceVectors`.

## Main results

* `QuantumCircuit.Party.SourceInventory.op_prepareSelected_mul_op_prepareFreeSlots`.
* `QuantumCircuit.Party.SourceInventory.isAllowed_prepareSelected`,
  `QuantumCircuit.Party.SourceInventory.mem_sources_prepareSelected`.
* `QuantumCircuit.Party.Word.exists_selective_partition`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 409–434 (selective free inputs and internal preparations).
-/

noncomputable section

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P]

namespace SourceInventory

/-! ### Selected slots and the free-slot system -/

/-- The slots selected by `free`, in their original order, with their original endpoints, the
slot bases `B` and the vectors `ζ`. Source: Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def selectedSources : (R : SourceInventory P) → (B : SlotBases R.length) →
    (Fin R.length → Bool) → (∀ i, EuclideanSpace ℂ (B.left i × B.right i)) → SourceInventory P
  | [], _, _, _ => []
  | r :: R, B, free, ζ =>
    let tail := selectedSources R B.tail (fun i ↦ free i.succ) (fun i ↦ ζ i.succ)
    if free 0 then ⟨r.left, r.right, r.distinct, B.left 0, B.right 0, ζ 0⟩ :: tail else tail

omit [Fintype P] [DecidableEq P] in
/-- A selected source is one selected original slot with its endpoints, bases and vector.
Source: Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem mem_selectedSources (R : SourceInventory P) (B : SlotBases R.length)
    (free : Fin R.length → Bool) (ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (s : PairSource P) :
    s ∈ selectedSources R B free ζ ↔ ∃ i : Fin R.length, free i = true ∧
      s = ⟨(R.get i).left, (R.get i).right, (R.get i).distinct, B.left i, B.right i, ζ i⟩ := by
  induction R with
  | nil => simp [selectedSources]
  | cons r R ih =>
    by_cases h : free 0 = true
    all_goals simp [selectedSources, h, Fin.exists_fin_succ, ih, SlotBases.tail]

/-- The system after preparing the free slots only: the fresh factors of the free slots, in
their order, in front of `X`. Source: Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def freeSlotSystem : (R : SourceInventory P) → SlotBases R.length → (Fin R.length → Bool) →
    (P → Type) → P → Type
  | [], _, _, X => X
  | r :: R, B, free, X =>
    cond (free ⟨0, Nat.succ_pos _⟩)
      (addPair (freeSlotSystem R B.tail (fun i ↦ free i.succ) X) r.distinct (B.left 0) (B.right 0))
      (freeSlotSystem R B.tail (fun i ↦ free i.succ) X)

/-- The finiteness of the bases of a free-slot system. -/
@[instance_reducible] def freeSlotSystemFintype : (R : SourceInventory P) →
    (B : SlotBases R.length) → (free : Fin R.length → Bool) → (X : P → Type) →
      (∀ p, Fintype (X p)) → ∀ p, Fintype (freeSlotSystem R B free X p)
  | [], _, _, _, h => h
  | r :: R, B, free, X, h =>
    letI := freeSlotSystemFintype R B.tail (fun i ↦ free i.succ) X h
    Bool.rec (motive := fun b ↦ ∀ p, Fintype (cond b (addPair (freeSlotSystem R B.tail
        (fun i ↦ free i.succ) X) r.distinct (B.left 0) (B.right 0))
        (freeSlotSystem R B.tail (fun i ↦ free i.succ) X) p))
      (fun p ↦ inferInstanceAs (Fintype (freeSlotSystem R B.tail (fun i ↦ free i.succ) X p)))
      (fun p ↦ inferInstanceAs (Fintype (addPair (freeSlotSystem R B.tail (fun i ↦ free i.succ)
        X) r.distinct (B.left 0) (B.right 0) p)))
      (free ⟨0, Nat.succ_pos _⟩)

/-- The decidable equality of the bases of a free-slot system. -/
@[instance_reducible] def freeSlotSystemDecidableEq : (R : SourceInventory P) →
    (B : SlotBases R.length) → (free : Fin R.length → Bool) → (X : P → Type) →
      (∀ p, DecidableEq (X p)) → ∀ p, DecidableEq (freeSlotSystem R B free X p)
  | [], _, _, _, h => h
  | r :: R, B, free, X, h =>
    letI := freeSlotSystemDecidableEq R B.tail (fun i ↦ free i.succ) X h
    Bool.rec (motive := fun b ↦ ∀ p, DecidableEq (cond b (addPair (freeSlotSystem R B.tail
        (fun i ↦ free i.succ) X) r.distinct (B.left 0) (B.right 0))
        (freeSlotSystem R B.tail (fun i ↦ free i.succ) X) p))
      (fun p ↦ inferInstanceAs (DecidableEq (freeSlotSystem R B.tail (fun i ↦ free i.succ) X p)))
      (fun p ↦ inferInstanceAs (DecidableEq (addPair (freeSlotSystem R B.tail
        (fun i ↦ free i.succ) X) r.distinct (B.left 0) (B.right 0) p)))
      (free ⟨0, Nat.succ_pos _⟩)

/-- The bases of a free-slot system are finite. -/
instance (R : SourceInventory P) (B : SlotBases R.length) (free : Fin R.length → Bool)
    (X : P → Type) [h : ∀ p, Fintype (X p)] (p : P) : Fintype (freeSlotSystem R B free X p) :=
  freeSlotSystemFintype R B free X h p

/-- The bases of a free-slot system have decidable equality. -/
instance (R : SourceInventory P) (B : SlotBases R.length) (free : Fin R.length → Bool)
    (X : P → Type) [h : ∀ p, DecidableEq (X p)] (p : P) :
    DecidableEq (freeSlotSystem R B free X p) :=
  freeSlotSystemDecidableEq R B free X h p

/-! ### The two preparations -/

/-- Prepare the fixed slots only, carrying the fresh factors of the free slots along. Source:
Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def prepareSelected (R : SourceInventory P) (B : SlotBases R.length) (free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type)
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] :
    Word (freeSlotSystem R B free X) (slotSystem R B X) :=
  match R, B, free, fixed with
  | [], _, _, _ => PartyCircuit.done X
  | r :: R, B, free, fixed =>
    let tail := prepareSelected R B.tail (fun i ↦ free i.succ) (fun i h ↦ fixed i.succ h) X
    Bool.rec (motive := fun b ↦ free ⟨0, Nat.succ_pos _⟩ = b →
        Word (cond b (addPair (freeSlotSystem R B.tail (fun i ↦ free i.succ) X) r.distinct
          (B.left 0) (B.right 0)) (freeSlotSystem R B.tail (fun i ↦ free i.succ) X))
          (addPair (slotSystem R B.tail X) r.distinct (B.left 0) (B.right 0)))
      (fun h ↦ tail.comp (Word.sourceAt r.distinct (B.left 0) (B.right 0) (fixed 0 h)
        (slotSystem R B.tail X)))
      (fun _ ↦ PartyCircuit.liftPair r.distinct (B.left 0) (B.right 0) tail)
      (free ⟨0, Nat.succ_pos _⟩) rfl

/-- Prepare the vectors `ζ` in the free slots. Source: Theorem 5.2, `04-compression.tex`,
lines 409–434. -/
def prepareFreeSlots (R : SourceInventory P) (B : SlotBases R.length) (free : Fin R.length → Bool)
    (ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type) [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] : Word X (freeSlotSystem R B free X) :=
  match R, B, free, ζ with
  | [], _, _, _ => PartyCircuit.done X
  | r :: R, B, free, ζ =>
    let tail := prepareFreeSlots R B.tail (fun i ↦ free i.succ) (fun i ↦ ζ i.succ) X
    Bool.rec (motive := fun b ↦
        Word X (cond b (addPair (freeSlotSystem R B.tail (fun i ↦ free i.succ) X) r.distinct
          (B.left 0) (B.right 0)) (freeSlotSystem R B.tail (fun i ↦ free i.succ) X)))
      tail
      (tail.comp (Word.sourceAt r.distinct (B.left 0) (B.right 0) (ζ 0)
        (freeSlotSystem R B.tail (fun i ↦ free i.succ) X)))
      (free ⟨0, Nat.succ_pos _⟩)

omit [Fintype P] [DecidableEq P] in
/-- The fixed vectors in the fixed slots and the vectors `ζ` in the free slots. Source: Theorem
5.2, `04-compression.tex`, lines 409–434. -/
def fillSourceVectors {n : ℕ} (B : SlotBases n) (free : Fin n → Bool)
    (fixed : ∀ i, free i = false → EuclideanSpace ℂ (B.left i × B.right i))
    (ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (i : Fin n) :
    EuclideanSpace ℂ (B.left i × B.right i) :=
  if h : free i = false then fixed i h else ζ i

/-- **One fixed word recovers the full preparation**: the selective preparation after the
preparation of arbitrary free vectors is the preparation of all slots. Source: Theorem 5.2,
`04-compression.tex`, lines 409–434. -/
theorem op_prepareSelected_mul_op_prepareFreeSlots (R : SourceInventory P)
    (B : SlotBases R.length) (free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → EuclideanSpace ℂ (B.left i × B.right i))
    (ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type) [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] :
    (prepareSelected R B free fixed X).op * (prepareFreeSlots R B free ζ X).op =
      (prepareSlots R B (fillSourceVectors B free fixed ζ) X).op := by
  induction R with
  | nil =>
    change PartyCircuit.op SourceGate.ev (PartyCircuit.done X) *
      PartyCircuit.op SourceGate.ev (PartyCircuit.done X) =
        PartyCircuit.op SourceGate.ev (PartyCircuit.done X)
    simp
  | cons r R ih =>
    obtain ⟨b, free', rfl⟩ : ∃ b free', free = Fin.cons b free' :=
      ⟨free 0, Fin.tail free, (Fin.cons_self_tail free).symm⟩
    have hP (b : Bool) (fixed : ∀ i, Fin.cons (α := fun _ ↦ Bool) b free' i = false →
          EuclideanSpace ℂ (B.left i × B.right i)) :
        (prepareSlots (r :: R) B (fillSourceVectors B (Fin.cons b free') fixed ζ) X).op =
          (Word.sourceAt r.distinct (B.left 0) (B.right 0)
              (fillSourceVectors B (Fin.cons b free') fixed ζ 0) (slotSystem R B.tail X)).op *
            (prepareSlots R B.tail
              (fun i ↦ fillSourceVectors B (Fin.cons b free') fixed ζ i.succ) X).op := by
      rw [prepareSlots]
      exact Word.op_comp _ _
    cases b
    · have hS : (prepareSelected (r :: R) B (Fin.cons false free') fixed X).op =
          (Word.sourceAt r.distinct (B.left 0) (B.right 0) (fixed 0 rfl)
              (slotSystem R B.tail X)).op *
            (prepareSelected R B.tail (fun i ↦ Fin.cons (α := fun _ ↦ Bool) false free' i.succ)
              (fun i h ↦ fixed i.succ h) X).op :=
        Word.op_comp _ _
      have hF : (prepareFreeSlots (r :: R) B (Fin.cons false free') ζ X).op =
          (prepareFreeSlots R B.tail (fun i ↦ Fin.cons (α := fun _ ↦ Bool) false free' i.succ)
            (fun i ↦ ζ i.succ) X).op :=
        rfl
      have h0 : fillSourceVectors B (Fin.cons false free') fixed ζ 0 = fixed 0 rfl := by
        simp [fillSourceVectors]
      rw [hS, hF]
      erw [Matrix.mul_assoc, ih]
      rw [hP, h0]
      rfl
    · have hS : (prepareSelected (r :: R) B (Fin.cons true free') fixed X).op =
          Word.op (PartyCircuit.liftPair r.distinct (B.left 0) (B.right 0)
            (prepareSelected R B.tail (fun i ↦ Fin.cons (α := fun _ ↦ Bool) true free' i.succ)
              (fun i h ↦ fixed i.succ h) X)) :=
        rfl
      have hF : (prepareFreeSlots (r :: R) B (Fin.cons true free') ζ X).op =
          (Word.sourceAt r.distinct (B.left 0) (B.right 0) (ζ 0)
              (freeSlotSystem R B.tail
                (fun i ↦ Fin.cons (α := fun _ ↦ Bool) true free' i.succ) X)).op *
            (prepareFreeSlots R B.tail (fun i ↦ Fin.cons (α := fun _ ↦ Bool) true free' i.succ)
              (fun i ↦ ζ i.succ) X).op :=
        Word.op_comp _ _
      have h0 : fillSourceVectors B (Fin.cons true free') fixed ζ 0 = ζ 0 := by
        simp [fillSourceVectors]
      rw [hS, hF]
      erw [← Matrix.mul_assoc, Word.op_liftPair_mul_op_sourceAt, Matrix.mul_assoc, ih]
      rw [hP, h0]
      rfl

omit [Fintype P] in
/-- The selective preparation is allowed when the fixed vectors are normalized. Source: Theorem
5.2, `04-compression.tex`, lines 409–434. -/
theorem isAllowed_prepareSelected (R : SourceInventory P) (B : SlotBases R.length)
    (free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → EuclideanSpace ℂ (B.left i × B.right i))
    (hfixed : ∀ i h, ‖fixed i h‖ = 1) (X : P → Type) [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] : (prepareSelected R B free fixed X).IsAllowed := by
  induction R with
  | nil => exact Word.isAllowed_done
  | cons r R ih =>
    obtain ⟨b, free', rfl⟩ : ∃ b free', free = Fin.cons b free' :=
      ⟨free 0, Fin.tail free, (Fin.cons_self_tail free).symm⟩
    cases b
    · exact (show Word.IsAllowed (PartyCircuit.comp
          (prepareSelected R B.tail (fun i ↦ Fin.cons (α := fun _ ↦ Bool) false free' i.succ)
            (fun i h ↦ fixed i.succ h) X)
          (Word.sourceAt r.distinct (B.left 0) (B.right 0) (fixed 0 rfl)
            (slotSystem R B.tail X))) from
        Word.IsAllowed.comp (ih _ _ _ fun i h ↦ hfixed i.succ h)
          (Word.isAllowed_sourceAt _ _ _ (hfixed 0 rfl) _))
    · exact (show Word.IsAllowed (PartyCircuit.liftPair r.distinct (B.left 0) (B.right 0)
          (prepareSelected R B.tail (fun i ↦ Fin.cons (α := fun _ ↦ Bool) true free' i.succ)
            (fun i h ↦ fixed i.succ h) X)) from
        PartyCircuit.isAllowed_liftPair r.distinct (B.left 0) (B.right 0) SourceGate.ev
          SourceGate.isCompatible_frame (fun _ _ _ _ _ _ _ _ _ _ _ h ↦ h)
          (ih _ _ _ fun i h ↦ hfixed i.succ h))

omit [Fintype P] in
/-- The pair sources of the selective preparation are the fixed slots, in their order, with
their original endpoints and fixed vectors. Source: Theorem 5.2, `04-compression.tex`,
lines 409–434. -/
theorem sources_prepareSelected (R : SourceInventory P) (B : SlotBases R.length)
    (free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type)
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] :
    (prepareSelected R B free fixed X).sources =
      selectedSources R B (fun i ↦ !free i) (fillSourceVectors B free fixed fun _ ↦ 0) := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    obtain ⟨b, free', rfl⟩ : ∃ b free', free = Fin.cons b free' :=
      ⟨free 0, Fin.tail free, (Fin.cons_self_tail free).symm⟩
    cases b
    · calc (prepareSelected (r :: R) B (Fin.cons false free') fixed X).sources
          = ⟨r.left, r.right, r.distinct, B.left 0, B.right 0, fixed 0 rfl⟩ ::
              (prepareSelected R B.tail
                (fun i ↦ Fin.cons (α := fun _ ↦ Bool) false free' i.succ)
                (fun i h ↦ fixed i.succ h) X).sources := rfl
        _ = _ := by
          erw [ih]
          simp [selectedSources, fillSourceVectors, SlotBases.tail]
          rfl
    · calc (prepareSelected (r :: R) B (Fin.cons true free') fixed X).sources
          = (prepareSelected R B.tail
                (fun i ↦ Fin.cons (α := fun _ ↦ Bool) true free' i.succ)
                (fun i h ↦ fixed i.succ h) X).sources := by
            change Word.sources (PartyCircuit.liftPair _ _ _ _) = _
            simp [PartyCircuit.liftPair]
        _ = _ := by
          erw [ih]
          simp [selectedSources, fillSourceVectors, SlotBases.tail]
          rfl

omit [Fintype P] in
/-- Each prepared source is one fixed original slot, with its original endpoints, bases and
fixed vector. Source: Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem mem_sources_prepareSelected (R : SourceInventory P) (B : SlotBases R.length)
    (free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type)
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (s : PairSource P) :
    s ∈ (prepareSelected R B free fixed X).sources ↔
      ∃ i : Fin R.length, ∃ h : free i = false,
        s = ⟨(R.get i).left, (R.get i).right, (R.get i).distinct, B.left i, B.right i,
          fixed i h⟩ := by
  rw [sources_prepareSelected, mem_selectedSources]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have h : free i = false := by simpa using hi
    exact ⟨i, h, by simp [fillSourceVectors, h]⟩
  · rintro ⟨i, h, rfl⟩
    exact ⟨i, by simp [h], by simp [fillSourceVectors, h]⟩

end SourceInventory

namespace Word

open SourceInventory

/-- **Preparing only internal sources splits the circuit across two sides.** If every fixed slot
joins two parties of the same side of `f`, the selective preparation followed by an allowed
source-free word is tensor partitioned by `f`, the two factors chosen before the free vectors,
and for every family of free vectors the preparation of all slots followed by the word is this
composition after the preparation of the free vectors. No normalization is imposed on the free
vectors. Source: Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem exists_selective_partition (f : P → Bool) (R : SourceInventory P)
    (B : SlotBases R.length) (free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → EuclideanSpace ℂ (B.left i × B.right i))
    (hfixed : ∀ i h, ‖fixed i h‖ = 1)
    (hmask : ∀ i, free i = false → f (R.get i).left = f (R.get i).right) (X : P → Type)
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] {Y : P → Type} [∀ p, Fintype (Y p)]
    (v : Word (slotSystem R B X) Y) (hv : v.IsAllowed) (hs : v.sources = []) :
    IsTensorPartitioned f (PartyCircuit.comp (prepareSelected R B free fixed X) v) ∧
      ∀ ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i),
        v.op * (prepareSlots R B (fillSourceVectors B free fixed ζ) X).op =
          Word.op (PartyCircuit.comp (prepareSelected R B free fixed X) v) *
            (prepareFreeSlots R B free ζ X).op := by
  refine ⟨isTensorPartitioned_of_sources_internal f _
    ((isAllowed_prepareSelected R B free fixed hfixed X).comp hv) fun s hmem ↦ ?_, fun ζ ↦ ?_⟩
  · rw [sources_comp, hs, List.nil_append] at hmem
    obtain ⟨i, hi, rfl⟩ := (mem_sources_prepareSelected R B free fixed X s).mp hmem
    exact hmask i hi
  · rw [op_comp, Matrix.mul_assoc, op_prepareSelected_mul_op_prepareFreeSlots]

end Word

end QuantumCircuit.Party
