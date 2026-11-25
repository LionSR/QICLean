/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.SourceOrder

/-!
# The common source slots of a partial expansion

Every branch of the partial expansion of a source circuit along affected parties `A` is allowed
(`SourceCircuit.isAllowed_partialWord`), and its sources are the sources of the expanded gates
that stay pair sources on the affected parties, in their order
(`SourceCircuit.sources_partialWord`). These are the positions with an affected endpoint
(`SourceCircuit.partialPositions`); their endpoints, read on the affected parties, and the bases
of their slots form one inventory of slots (`SourceCircuit.partialSlots`,
`SourceCircuit.partialSlotBases`) fixed before any label is chosen, enumerated by the positions
(`SourceCircuit.partialSlotEquiv`). The sources of every branch are these slots with the vectors
of the gates at the chosen labels (`SourceCircuit.ofSlots_partialSlotVector`), so every branch
is the preparation of the slots followed by an allowed word without sources
(`SourceCircuit.exists_partial_source_preparation`), and these vectors are the only ones that
represent the branch (`SourceCircuit.eq_partialSlotVector_of_inventory_eq`). When every party is
affected, the slots are all the positions, and no slot has an exterior endpoint.

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.expandedSources`.
* `QuantumCircuit.Party.SourceCircuit.partialPositions`,
  `QuantumCircuit.Party.SourceCircuit.partialSlots`,
  `QuantumCircuit.Party.SourceCircuit.partialSlotBases`,
  `QuantumCircuit.Party.SourceCircuit.partialSlotEquiv`.
* `QuantumCircuit.Party.SourceCircuit.partialSlotChoice`,
  `QuantumCircuit.Party.SourceCircuit.partialSlotVector`.
* `QuantumCircuit.Party.SourceCircuit.allSourceSlotEquiv`.

## Main results

* `QuantumCircuit.Party.SourceCircuit.isAllowed_partialWord`,
  `QuantumCircuit.Party.SourceCircuit.sources_partialWord`.
* `QuantumCircuit.Party.SourceCircuit.ofSlots_partialSlots`,
  `QuantumCircuit.Party.SourceCircuit.ofSlots_partialSlotVector`,
  `QuantumCircuit.Party.SourceCircuit.eq_partialSlotVector_of_inventory_eq`.
* `QuantumCircuit.Party.SourceCircuit.exists_partial_source_preparation`,
  `QuantumCircuit.Party.SourceCircuit.exists_partial_source_preparation_with_original_vectors`.
* `QuantumCircuit.Party.SourceCircuit.sum_nonempty_allSourceSlots`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 253–267, 338–355 and 342–434 (equation `eq:compression-subset-expansion`).

Adapted from TNLean, `TNLean/Lattice/Compression/PartialSourceInventory.lean`,
`TNLean/Lattice/Compression/PartialSourcePreparation.lean`, the slot part of
`TNLean/Lattice/Compression/SourceCircuitChoiceAt.lean`,
`TNLean/Lattice/Compression/AllSourceSlots.lean` and
`TNLean/Lattice/Compression/ActualSourceEmptyOwner.lean` at commit `a05f5d6d0a` (Apache-2.0).
Changes: the slot bases are the bases of the positions (`SourceCircuit.partialSlotBases`), so
the vectors of a branch lie in the slot spaces by construction and no equation between spaces
or register lists is stated.
-/

open Matrix ManyBody

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace SourceCircuit

variable (A : P → Bool) {X Y : P → Type}

/-! ### The sources of a branch -/

/-- **Every branch of the partial expansion is allowed** when the local operations of the source
circuit are contractions: a touched gate contributes a branch of its prepared gate, an untouched
gate its whole operator. Source: Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem isAllowed_partialWord [Fintype P] : {X Y : P → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → (w : SourceCircuit X Y) → w.IsLocalContractive →
      ∀ ξ, (partialWord A w ξ).IsAllowed
  | _, _, _, _, PartyCircuit.done _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate D hY g, _, ξ => by
    by_cases h : PreparedGate.IsTouched A D
    · rw [partialWord_gate_of_isTouched A D hY g h]
      exact Word.isAllowed_coarsen _ (Word.isAllowed_onCell D hY (g.gate.isAllowed_branchWord _))
    · rw [partialWord_gate_of_not_isTouched A D hY g h]
      exact (norm_subregionPlaceBetween_le _ _ _).trans g.gate.norm_eval_le_one
  | _, _, _, _, PartyCircuit.localOp _ _ _, hw, _ => Word.isAllowed_coarsen _ hw
  | _, _, _, _, PartyCircuit.localOps _, hw, _ => Word.isAllowed_coarsen _ hw
  | _, _, _, _, PartyCircuit.comp c c', hw, ξ =>
    ⟨isAllowed_partialWord c hw.1 ξ.1, isAllowed_partialWord c' hw.2 ξ.2⟩

/-- The sources of the gates whose branches are chosen, with the vectors of the chosen labels,
in the order of the source inventory. Source: Theorem 5.2, `04-compression.tex`,
lines 351–417. -/
def expandedSources : {X Y : P → Type} → (w : SourceCircuit X Y) → Choices A w →
    SourceInventory P
  | _, _, PartyCircuit.done _, _ => []
  | _, _, PartyCircuit.gate D _ g, ξ =>
    if h : PreparedGate.IsTouched A D then
      (SourceInventory.ofSlots g.gate.slots g.gate.bases
        (g.gate.vector (cast (ite_eq_left h) ξ))).mapOwner Subtype.val
    else []
  | _, _, PartyCircuit.localOp _ _ _, _ => []
  | _, _, PartyCircuit.localOps _, _ => []
  | _, _, PartyCircuit.comp c c', ξ => expandedSources c' ξ.2 ++ expandedSources c ξ.1

/-- **A branch keeps the sources of the expanded gates whose owners stay distinct**, in their
order. Source: Theorem 5.2, `04-compression.tex`, lines 383–417. -/
theorem sources_partialWord [Fintype P] : {X Y : P → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → (w : SourceCircuit X Y) → (ξ : Choices A w) →
      (partialWord A w ξ).sources =
        SourceInventory.mapOwner (affectedOwner A) (expandedSources A w ξ)
  | _, _, _, _, PartyCircuit.done _, _ => rfl
  | _, _, _, _, PartyCircuit.gate D hY g, ξ => by
    by_cases h : PreparedGate.IsTouched A D
    · rw [partialWord_gate_of_isTouched A D hY g h, Word.sources_coarsen, Word.sources_onCell,
        g.gate.sources_branchWord,
        show expandedSources A (PartyCircuit.gate D hY g : SourceCircuit _ _) ξ = _ from
          dite_eq_left h]
      rfl
    · rw [partialWord_gate_of_not_isTouched A D hY g h,
        show expandedSources A (PartyCircuit.gate D hY g : SourceCircuit _ _) ξ = _ from
          dite_eq_right h]
      rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, _ => by
    rw [partialWord_localOp, Word.sources_coarsen]
    rfl
  | _, _, _, _, PartyCircuit.localOps _, _ => by
    rw [partialWord_localOps, Word.sources_coarsen]
    rfl
  | _, _, _, _, PartyCircuit.comp c c', ξ => by
    rw [partialWord_comp, Word.sources_comp, sources_partialWord c ξ.1,
      sources_partialWord c' ξ.2]
    exact (SourceInventory.mapOwner_append _ _ _).symm

/-- Every source of a branch comes from an expanded gate, has an affected endpoint and keeps its
bases and vector. Source: Theorem 5.2, `04-compression.tex`, lines 383–417. -/
theorem mem_sources_partialWord [Fintype P] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (w : SourceCircuit X Y) (ξ : Choices A w) (t : PairSource (Option {p // A p = true})) :
    t ∈ (partialWord A w ξ).sources ↔
      ∃ s ∈ expandedSources A w ξ, ∃ h : A s.left = true ∨ A s.right = true,
        t = ⟨affectedOwner A s.left, affectedOwner A s.right,
          (s.affectedOwner_ne_iff A).mpr h, s.leftBasis, s.rightBasis, s.vector⟩ := by
  rw [sources_partialWord]
  exact SourceInventory.mem_mapOwner_affectedOwner A (expandedSources A w ξ) t

/-! ### The common slots -/

/-- The positions kept after grouping the exterior parties: those with an affected endpoint, in
preparation order. Source: Theorem 5.2, `04-compression.tex`, lines 342–417. -/
def partialPositions (w : SourceCircuit X Y) : List w.sourceLocations :=
  (sourceOrder w).filter fun e ↦ A (w.endpoints e).1 || A (w.endpoints e).2

/-- A position is kept exactly when an endpoint is affected. Source: Theorem 5.2,
`04-compression.tex`, lines 383–417. -/
theorem mem_partialPositions_iff (w : SourceCircuit X Y) (e : w.sourceLocations) :
    e ∈ partialPositions A w ↔ A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true := by
  simp [partialPositions, mem_sourceOrder]

/-- The endpoints of a position with an affected endpoint stay distinct on the affected parties.
Source: Theorem 5.2, `04-compression.tex`, lines 383–417. -/
theorem affectedOwner_endpoints_ne (w : SourceCircuit X Y) {e : w.sourceLocations}
    (he : A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true) :
    affectedOwner A (w.endpoints e).1 ≠ affectedOwner A (w.endpoints e).2 :=
  (affectedOwner_eq_iff A _ _).not.mpr fun h ↦ h.elim (w.endpoints_ne e) fun h ↦ by
    simp [h.1, h.2] at he

/-- The fixed inventory of the kept positions: their endpoints on the affected parties and the
bases of their slots; the zero vectors record no preparation. Source: Theorem 5.2,
`04-compression.tex`, lines 253–267 and 342–417. -/
def partialSlots (w : SourceCircuit X Y) : SourceInventory (Option {p // A p = true}) :=
  (partialPositions A w).attach.map fun e ↦
    ⟨affectedOwner A (w.endpoints e.1).1, affectedOwner A (w.endpoints e.1).2,
      affectedOwner_endpoints_ne A w ((mem_partialPositions_iff A w e.1).mp e.2),
      w.leftBasis e.1, w.rightBasis e.1, 0⟩

/-- The slots are enumerated by the kept positions, in preparation order. Source: Theorem 5.2,
`04-compression.tex`, lines 342–417. -/
noncomputable def partialSlotEquiv (w : SourceCircuit X Y) :
    Fin (partialSlots A w).length ≃
      {e : w.sourceLocations // A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true} := by
  classical
  exact (finCongr (by simp [partialSlots])).trans
    (((nodup_sourceOrder w).filter _).getEquiv (partialPositions A w) |>.trans
      (Equiv.subtypeEquivRight (mem_partialPositions_iff A w)))

/-- The enumeration reads the list of kept positions. Source: Theorem 5.2, `04-compression.tex`,
lines 342–417. -/
theorem partialSlotEquiv_apply (w : SourceCircuit X Y) (i : Fin (partialSlots A w).length) :
    (partialSlotEquiv A w i).1 =
      (partialPositions A w).get ⟨i.1, by simpa [partialSlots] using i.2⟩ :=
  rfl

/-- The bases of the slots: the bases of the kept positions. Source: Theorem 5.2,
`04-compression.tex`, lines 253–267 and 342–417. -/
noncomputable def partialSlotBases (w : SourceCircuit X Y) :
    SourceInventory.SlotBases (partialSlots A w).length where
  left i := w.leftBasis (partialSlotEquiv A w i).1
  right i := w.rightBasis (partialSlotEquiv A w i).1

/-- The endpoints of a slot are those of its position, read on the affected parties.
Source: Theorem 5.2, `04-compression.tex`, lines 253–267 and 342–417. -/
theorem partialSlot_spec (w : SourceCircuit X Y) (i : Fin (partialSlots A w).length) :
    ((partialSlots A w).get i).left =
        affectedOwner A (w.endpoints (partialSlotEquiv A w i).1).1 ∧
      ((partialSlots A w).get i).right =
        affectedOwner A (w.endpoints (partialSlotEquiv A w i).1).2 := by
  change ((partialSlots A w)[i.1]'i.2).left = _ ∧ ((partialSlots A w)[i.1]'i.2).right = _
  simp only [partialSlots, List.getElem_map, List.getElem_attach]
  exact ⟨rfl, rfl⟩

/-! ### The vectors in the slots -/

/-- The label chosen at the gate of a slot. Source: Theorem 5.2, `04-compression.tex`,
lines 342–417. -/
noncomputable def partialSlotChoice (w : SourceCircuit X Y) (ξ : Choices A w)
    (i : Fin (partialSlots A w).length) : w.branchLabels (partialSlotEquiv A w i).1.1 :=
  choiceAt A w ξ (partialSlotEquiv A w i).1.1
    (isTouched_of_source_endpoint A w (partialSlotEquiv A w i).1 (partialSlotEquiv A w i).2)

/-- The vector in a slot: the vector of its gate at the chosen label, which reads no other
label. Source: Theorem 5.2, `04-compression.tex`, lines 342–417. -/
noncomputable def partialSlotVector (w : SourceCircuit X Y) (ξ : Choices A w)
    (i : Fin (partialSlots A w).length) :
    EuclideanSpace ℂ ((partialSlotBases A w).left i × (partialSlotBases A w).right i) :=
  w.sourceVectorAt (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i)

/-- The slot vectors are normalized. -/
theorem norm_partialSlotVector (w : SourceCircuit X Y) (ξ : Choices A w)
    (i : Fin (partialSlots A w).length) : ‖partialSlotVector A w ξ i‖ = 1 :=
  w.norm_sourceVectorAt _ _

/-- Kept sources with prescribed positions agree. -/
private theorem pairSource_mk_eq {Q : Type} {l l' r r' : Q} (hl : l = l') (hr : r = r')
    (d : l ≠ r) (d' : l' ≠ r') (α β : Type) [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (v : EuclideanSpace ℂ (α × β)) :
    (⟨l, r, d, α, β, v⟩ : PairSource Q) = ⟨l', r', d', α, β, v⟩ := by
  subst hl hr
  rfl

/-- Keeping the elements with a property is mapping the kept elements. -/
private theorem filterMap_dite_eq_pmap {α β : Type*} (p : α → Prop) [DecidablePred p]
    (G : ∀ a, p a → β) (L : List α) :
    L.filterMap (fun a ↦ if h : p a then some (G a h) else none) =
      (L.filter fun a ↦ decide (p a)).pmap G
        fun _ ha ↦ of_decide_eq_true (List.mem_filter.mp ha).2 := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    by_cases h : p b
    · simp [h, ih]
    · simp [h, ih]

/-- **The slots with prescribed vectors are the kept pair sources of the positions**, in
preparation order, for every family of vectors at the positions. Source: Theorem 5.2,
`04-compression.tex`, lines 338–417. -/
theorem ofSlots_partialSlots (w : SourceCircuit X Y)
    (v : ∀ e : w.sourceLocations, EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e)) :
    SourceInventory.ofSlots (partialSlots A w) (partialSlotBases A w)
        (fun i ↦ v (partialSlotEquiv A w i).1) =
      (sourceOrder w).filterMap fun e ↦ (pairSourceAt w e (v e)).mapOwner (affectedOwner A) := by
  let p : w.sourceLocations → Prop := fun e ↦ A (w.endpoints e).1 = true ∨ A (w.endpoints e).2
  let G : ∀ e, p e → PairSource (Option {p // A p = true}) := fun e h ↦
    ⟨affectedOwner A (w.endpoints e).1, affectedOwner A (w.endpoints e).2,
      affectedOwner_endpoints_ne A w h, w.leftBasis e, w.rightBasis e, v e⟩
  have hm : (fun e ↦ (pairSourceAt w e (v e)).mapOwner (affectedOwner A)) =
      fun e ↦ if h : p e then some (G e h) else none := by
    funext e
    by_cases h : p e
    · rw [dite_eq_left h]
      exact dite_eq_right (affectedOwner_endpoints_ne A w h)
    · rw [dite_eq_right h]
      refine dite_eq_left (not_not.mp fun hne ↦ h ?_)
      exact ((pairSourceAt w e (v e)).affectedOwner_ne_iff A).mp hne
  rw [hm, filterMap_dite_eq_pmap]
  have hf : ((sourceOrder w).filter fun a ↦ decide (p a)) = partialPositions A w := by
    refine congrArg (List.filter · _) (funext fun e ↦ ?_)
    simp only [p, Bool.decide_or, Bool.decide_eq_true]
  refine List.ext_getElem ?_ fun j hj hj' ↦ ?_
  · simp [SourceInventory.ofSlots, partialSlots, hf]
  · simp only [SourceInventory.ofSlots, List.getElem_ofFn, List.getElem_pmap]
    have hi : j < (partialSlots A w).length := by simpa [SourceInventory.ofSlots] using hj
    have hs := partialSlot_spec A w ⟨j, hi⟩
    refine (pairSource_mk_eq hs.1 hs.2 _
      (affectedOwner_endpoints_ne A w (partialSlotEquiv A w ⟨j, hi⟩).2) _ _ _).trans ?_
    have hG : ∀ e e' (_ : e = e') (he : p e) (he' : p e'), G e he = G e' he' := by
      rintro e _ rfl _ _
      rfl
    refine hG _ _ (List.getElem_of_eq hf.symm _) (partialSlotEquiv A w ⟨j, hi⟩).2 ?_
    have hm' := (List.mem_filter.mp (List.getElem_mem (l := (sourceOrder w).filter
      fun a ↦ decide (p a)) (n := j) (by simpa [hf, partialSlots] using hi))).2
    exact of_decide_eq_true hm'

/-- **The sources of every branch are the slots with the vectors of the chosen labels.**
Source: Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem ofSlots_partialSlotVector [Fintype P] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (w : SourceCircuit X Y) (ξ : Choices A w) :
    SourceInventory.ofSlots (partialSlots A w) (partialSlotBases A w)
      (partialSlotVector A w ξ) = (partialWord A w ξ).sources := by
  let v : ∀ e : w.sourceLocations, EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e) :=
    fun e ↦ if h : IsTouched A w e.1 then w.sourceVectorAt e (choiceAt A w ξ e.1 h) else 0
  have hv : partialSlotVector A w ξ = fun i ↦ v (partialSlotEquiv A w i).1 :=
    funext fun i ↦ by
      simp only [v, dite_eq_left (isTouched_of_source_endpoint A w _ (partialSlotEquiv A w i).2)]
      rfl
  rw [hv, ofSlots_partialSlots, sources_partialWord_eq_filterMap]
  refine List.filterMap_congr fun e _ ↦ ?_
  rw [sourceAt_eq_dite]
  by_cases h : IsTouched A w e.1
  · simp only [v, dite_eq_left h]
  · rw [dite_eq_right h]
    refine dite_eq_left (not_not.mp fun hne ↦ h ?_)
    exact isTouched_of_source_endpoint A w e
      (((pairSourceAt w e (v e)).affectedOwner_ne_iff A).mp hne)

/-- **The vectors of the gates at the chosen labels are the only vectors representing a branch
in the slots.** Source: Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem eq_partialSlotVector_of_inventory_eq [Fintype P] [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] (w : SourceCircuit X Y) (ξ : Choices A w)
    (η : ∀ i, EuclideanSpace ℂ ((partialSlotBases A w).left i × (partialSlotBases A w).right i))
    (hη : SourceInventory.ofSlots (partialSlots A w) (partialSlotBases A w) η =
      (partialWord A w ξ).sources) :
    η = partialSlotVector A w ξ := by
  have h := hη.trans (ofSlots_partialSlotVector A w ξ).symm
  funext i
  have hi := congrArg (fun L ↦ L[i.1]?) h
  simp only [SourceInventory.ofSlots, List.getElem?_ofFn, Fin.eta] at hi
  simpa using hi

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
-- The instances of `Y` build the witness words, which end in the system `Y` on blocks.
/-- **Every branch is the preparation of the common slots followed by an allowed word without
sources.** The slots and their bases do not depend on the labels. Source: Theorem 5.2,
`04-compression.tex`, lines 253–267 and 342–417. -/
theorem exists_partial_source_preparation [Fintype P] [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (w : SourceCircuit X Y) (hw : w.IsLocalContractive) :
    ∃ η : Choices A w →
        ∀ i, EuclideanSpace ℂ ((partialSlotBases A w).left i × (partialSlotBases A w).right i),
      (∀ ξ i, ‖η ξ i‖ = 1) ∧
      (∀ ξ, SourceInventory.ofSlots (partialSlots A w) (partialSlotBases A w) (η ξ) =
        (partialWord A w ξ).sources) ∧
      ∃ v : Choices A w → Word
          (SourceInventory.slotSystem (partialSlots A w) (partialSlotBases A w)
            (blockSystem (affectedOwner A) X))
          (blockSystem (affectedOwner A) Y),
        (∀ ξ, (v ξ).IsAllowed) ∧ (∀ ξ, (v ξ).sources = []) ∧
        ∀ ξ, Word.op (partialWord A w ξ) =
          (v ξ).op * (SourceInventory.prepareSlots (partialSlots A w) (partialSlotBases A w)
            (η ξ) (blockSystem (affectedOwner A) X)).op := by
  have hE (ξ : Choices A w) :
      (SourceInventory.ofSlots (partialSlots A w) (partialSlotBases A w)
        (partialSlotVector A w ξ)).Expands (partialWord A w ξ).sources := by
    rw [ofSlots_partialSlotVector]
  choose d hd hds hde using fun ξ ↦ SourceInventory.exists_prepareSlots_recovery _ _ _ _ (hE ξ)
    (blockSystem (affectedOwner A) X)
  refine ⟨partialSlotVector A w, norm_partialSlotVector A w, ofSlots_partialSlotVector A w,
    fun ξ ↦ (d ξ).comp (partialWord A w ξ).localPart,
    fun ξ ↦ ⟨hd ξ, Word.isAllowed_localPart (isAllowed_partialWord A w hw ξ)⟩,
    fun ξ ↦ by rw [Word.sources_comp, hds ξ]; rfl, fun ξ ↦ ?_⟩
  rw [Word.op_comp, Matrix.mul_assoc, hde, Word.op_localPart_mul_prepare]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
-- The instances of `Y` build the witness words, which end in the system `Y` on blocks.
/-- The preparation of every branch uses the vectors of the gates at the chosen labels.
Source: Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem exists_partial_source_preparation_with_original_vectors [Fintype P]
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (w : SourceCircuit X Y) (hw : w.IsLocalContractive) :
    (∀ ξ i, ‖partialSlotVector A w ξ i‖ = 1) ∧
      (∀ ξ, SourceInventory.ofSlots (partialSlots A w) (partialSlotBases A w)
        (partialSlotVector A w ξ) = (partialWord A w ξ).sources) ∧
      ∃ v : Choices A w → Word
          (SourceInventory.slotSystem (partialSlots A w) (partialSlotBases A w)
            (blockSystem (affectedOwner A) X))
          (blockSystem (affectedOwner A) Y),
        (∀ ξ, (v ξ).IsAllowed) ∧ (∀ ξ, (v ξ).sources = []) ∧
        ∀ ξ, Word.op (partialWord A w ξ) =
          (v ξ).op * (SourceInventory.prepareSlots (partialSlots A w) (partialSlotBases A w)
            (partialSlotVector A w ξ) (blockSystem (affectedOwner A) X)).op := by
  obtain ⟨η, hη, hS, v, hv, hvs, he⟩ := exists_partial_source_preparation A w hw
  obtain rfl : η = partialSlotVector A w :=
    funext fun ξ ↦ eq_partialSlotVector_of_inventory_eq A w ξ (η ξ) (hS ξ)
  exact ⟨hη, hS, v, hv, hvs, he⟩

/-! ### All parties affected -/

/-- With every party affected, the slots enumerate all positions. Source: Theorem 5.2,
`04-compression.tex`, lines 338–355. -/
noncomputable def allSourceSlotEquiv (w : SourceCircuit X Y) :
    Fin (partialSlots (fun _ ↦ true) w).length ≃ w.sourceLocations :=
  (partialSlotEquiv (fun _ ↦ true) w).trans (Equiv.subtypeUnivEquiv fun _ ↦ Or.inl rfl)

/-- The enumeration of all positions is the enumeration of the slots. Source: Theorem 5.2,
`04-compression.tex`, lines 342–355. -/
theorem allSourceSlotEquiv_apply (w : SourceCircuit X Y)
    (i : Fin (partialSlots (fun _ ↦ true) w).length) :
    allSourceSlotEquiv w i = (partialSlotEquiv (fun _ ↦ true) w i).1 :=
  rfl

open Classical in
/-- The sum over the nonempty sets of slots is the sum over the nonempty sets of positions.
Source: Theorem 5.2, `eq:compression-subset-expansion`, `04-compression.tex`, lines 338–355. -/
theorem sum_nonempty_allSourceSlots {M : Type*} [AddCommMonoid M] (w : SourceCircuit X Y)
    (F : Finset w.sourceLocations → M) :
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin (partialSlots (fun _ ↦ true) w).length))).erase ∅,
        F (S.map (allSourceSlotEquiv w).toEmbedding) =
      ∑ S ∈ (Finset.univ : Finset (Finset w.sourceLocations)).erase ∅, F S := by
  classical
  refine Finset.sum_equiv (allSourceSlotEquiv w).finsetCongr (fun S ↦ ?_) fun _ _ ↦ rfl
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Equiv.finsetCongr_apply]
  exact (not_congr Finset.map_eq_empty).symm

/-- With every party affected, no slot has the exterior party as an endpoint. Source:
Theorem 5.2, `04-compression.tex`, lines 253–267, 342–417 and 409–434. -/
theorem partialSlots_all_ne_none (w : SourceCircuit X Y)
    (i : Fin (partialSlots (fun _ ↦ true) w).length) :
    ((partialSlots (fun _ ↦ true) w).get i).left ≠ none ∧
      ((partialSlots (fun _ ↦ true) w).get i).right ≠ none := by
  rw [(partialSlot_spec (fun _ ↦ true) w i).1, (partialSlot_spec (fun _ ↦ true) w i).2]
  exact ⟨affectedOwner_true_ne_none _, affectedOwner_true_ne_none _⟩

end SourceCircuit

end QuantumCircuit.Party
