/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Choices

/-!
# The ordered source positions of a partial expansion

The source positions of a source circuit are listed in the order of its source inventory
(`SourceCircuit.sourceOrder`): the slots of later gates come first, and each gate keeps the
order of its slots; every position occurs once. At a position of a gate touched by the affected
parties `A`, a choice of the partial expansion determines the pair source of the chosen branch,
read on the affected parties and the exterior party (`SourceCircuit.sourceAt`); it is kept
exactly when an endpoint is affected, and its vector is the vector of the gate at the chosen
label (`SourceCircuit.sourceVectorAt`). The source inventory of every branch of the partial
expansion is the list of these kept sources, in the order of the positions
(`SourceCircuit.sources_partialWord_eq_filterMap`).

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.sourceOrder` — the positions in preparation order.
* `QuantumCircuit.Party.SourceCircuit.sourceVectorAt` — the vector of a position at a label.
* `QuantumCircuit.Party.SourceCircuit.pairSourceAt` — the pair source at a position, with a
  prescribed vector.
* `QuantumCircuit.Party.SourceCircuit.sourceAt` — the kept source of a branch at a position.
* `QuantumCircuit.Party.SourceCircuit.CorrectedSchmidtCoordinates` — Schmidt indices at a set of
  positions.

## Main results

* `QuantumCircuit.Party.SourceCircuit.mem_sourceOrder`,
  `QuantumCircuit.Party.SourceCircuit.nodup_sourceOrder`.
* `QuantumCircuit.Party.SourceCircuit.sourceAt_isSome_iff`,
  `QuantumCircuit.Party.SourceCircuit.sourceAt_eq_mapOwner_sourceVectorAt`.
* `QuantumCircuit.Party.SourceCircuit.sources_partialWord_eq_filterMap`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 253–267 and 342–434.

Adapted from TNLean, `TNLean/Lattice/Compression/SourceCircuitSourceOrder.lean` and the vector
part of `TNLean/Lattice/Compression/SourceCircuitChoiceAt.lean` at commit `a05f5d6d0a`
(Apache-2.0). Changes: the two factors of a position are the basis types of its slot
(`SourceCircuit.leftBasis`, `SourceCircuit.rightBasis`), so a kept source carries them by
construction and no equation between spaces is stated.
-/

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace SourceCircuit

variable {X Y Z : P → Type}

/-! ### The positions in preparation order -/

/-- All source positions in preparation order: the positions of the later part of a composition
first, and the slots of each gate in their order. Source: Theorem 5.2, `04-compression.tex`,
lines 342–355. -/
def sourceOrder : {X Y : P → Type} → (w : SourceCircuit X Y) → List w.sourceLocations
  | _, _, PartyCircuit.done _ => []
  | _, _, PartyCircuit.gate _ _ g => List.ofFn fun i : Fin g.gate.slots.length ↦ ⟨(), i⟩
  | _, _, PartyCircuit.localOp _ _ _ => []
  | _, _, PartyCircuit.localOps _ => []
  | _, _, PartyCircuit.comp c c' =>
    (sourceOrder c').map (fun e ↦ (⟨Sum.inr e.1, e.2⟩ : sourceLocations (.comp c c'))) ++
      (sourceOrder c).map fun e ↦ (⟨Sum.inl e.1, e.2⟩ : sourceLocations (.comp c c'))

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The empty circuit has no position. -/
@[simp] theorem sourceOrder_done : sourceOrder (PartyCircuit.done X : SourceCircuit X X) = [] :=
  rfl

/-- The positions of one gate are its slots in their order. Source: Theorem 5.2,
`04-compression.tex`, lines 342–355. -/
theorem sourceOrder_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y) :
    sourceOrder (PartyCircuit.gate D hY g : SourceCircuit X Y) =
      (List.finRange g.gate.slots.length).map
        (β := sourceLocations (PartyCircuit.gate D hY g : SourceCircuit X Y)) fun i ↦ ⟨(), i⟩ :=
  List.ofFn_eq_map

/-- A local operation has no position. -/
@[simp] theorem sourceOrder_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (U : Matrix (Y p) (X p) ℂ) :
    sourceOrder (PartyCircuit.localOp p hY U : SourceCircuit X Y) = [] :=
  rfl

/-- Local operations at every party have no position. -/
@[simp] theorem sourceOrder_localOps (U : ∀ p, Matrix (Y p) (X p) ℂ) :
    sourceOrder (PartyCircuit.localOps U : SourceCircuit X Y) = [] :=
  rfl

/-- The positions of a composition: those of the later part, then those of the earlier part.
Source: Theorem 5.2, `04-compression.tex`, lines 351–355. -/
theorem sourceOrder_comp (w : SourceCircuit X Y) (w' : SourceCircuit Y Z) :
    sourceOrder (PartyCircuit.comp w w') =
      (sourceOrder w').map (fun e ↦ (⟨Sum.inr e.1, e.2⟩ : sourceLocations (.comp w w'))) ++
        (sourceOrder w).map fun e ↦ (⟨Sum.inl e.1, e.2⟩ : sourceLocations (.comp w w')) :=
  rfl

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Every position occurs in the ordered list. Source: Theorem 5.2, `04-compression.tex`,
lines 342–355. -/
theorem mem_sourceOrder : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (e : w.sourceLocations) → e ∈ sourceOrder w
  | _, _, PartyCircuit.done _, e => Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ _, ⟨_, i⟩ => List.mem_ofFn.mpr ⟨i, rfl⟩
  | _, _, PartyCircuit.localOp _ _ _, e => Empty.elim e.1
  | _, _, PartyCircuit.localOps _, e => Empty.elim e.1
  | _, _, PartyCircuit.comp c c', e => match e with
    | ⟨Sum.inl g, i⟩ =>
      List.mem_append_right _ (List.mem_map.mpr ⟨⟨g, i⟩, mem_sourceOrder c _, rfl⟩)
    | ⟨Sum.inr g, i⟩ =>
      List.mem_append_left _ (List.mem_map.mpr ⟨⟨g, i⟩, mem_sourceOrder c' _, rfl⟩)

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- No position is repeated, even when its pair of endpoints occurs at several gates.
Source: Theorem 5.2, `04-compression.tex`, lines 342–355. -/
theorem nodup_sourceOrder : {X Y : P → Type} → (w : SourceCircuit X Y) → (sourceOrder w).Nodup
  | _, _, PartyCircuit.done _ => List.nodup_nil
  | _, _, PartyCircuit.gate _ _ _ =>
    List.nodup_ofFn_ofInjective fun _ _ h ↦ eq_of_heq (Sigma.mk.inj h).2
  | _, _, PartyCircuit.localOp _ _ _ => List.nodup_nil
  | _, _, PartyCircuit.localOps _ => List.nodup_nil
  | _, _, PartyCircuit.comp c c' => by
    refine List.Nodup.append ((nodup_sourceOrder c').map (Sum.inr_injective.sigma_map
        (β₁ := fun g ↦ Fin (slotCount c' g))
        (β₂ := fun g ↦ Fin (slotCount (PartyCircuit.comp c c') g))
        fun _ ↦ Function.injective_id))
      ((nodup_sourceOrder c).map (Sum.inl_injective.sigma_map
        (β₁ := fun g ↦ Fin (slotCount c g))
        (β₂ := fun g ↦ Fin (slotCount (PartyCircuit.comp c c') g))
        fun _ ↦ Function.injective_id)) ?_
    intro e hv hw
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
    obtain ⟨y, _, h⟩ := List.mem_map.mp hw
    exact Sum.inl_ne_inr (congrArg Sigma.fst h)

/-! ### The vectors at the positions -/

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The vector of the gate of a position at one of its branch labels. Source: Theorem 5.2,
`04-compression.tex`, lines 342–417. -/
def sourceVectorAt : {X Y : P → Type} → (w : SourceCircuit X Y) → (e : w.sourceLocations) →
    w.branchLabels e.1 → EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e)
  | _, _, PartyCircuit.done _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ g => fun e ξ ↦ g.gate.vector ξ e.2
  | _, _, PartyCircuit.localOp _ _ _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.localOps _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.comp c c' => fun
    | ⟨Sum.inl g, i⟩ => sourceVectorAt c ⟨g, i⟩
    | ⟨Sum.inr g, i⟩ => sourceVectorAt c' ⟨g, i⟩

/-- The vector at a position of one gate is the vector of the gate at its slot. -/
theorem sourceVectorAt_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y)
    (e : sourceLocations (PartyCircuit.gate D hY g : SourceCircuit X Y)) (ξ : g.ι) :
    sourceVectorAt (PartyCircuit.gate D hY g : SourceCircuit X Y) e ξ = g.gate.vector ξ e.2 :=
  rfl

/-- A position of the first part of a composition keeps its vectors. -/
@[simp] theorem sourceVectorAt_comp_inl (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w.gateLocations) (i : Fin (w.slotCount g)) (ξ : w.branchLabels g) :
    sourceVectorAt (PartyCircuit.comp w w') ⟨Sum.inl g, i⟩ ξ = w.sourceVectorAt ⟨g, i⟩ ξ :=
  rfl

/-- A position of the second part of a composition keeps its vectors. -/
@[simp] theorem sourceVectorAt_comp_inr (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w'.gateLocations) (i : Fin (w'.slotCount g)) (ξ : w'.branchLabels g) :
    sourceVectorAt (PartyCircuit.comp w w') ⟨Sum.inr g, i⟩ ξ = w'.sourceVectorAt ⟨g, i⟩ ξ :=
  rfl

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Every vector of a gate is normalized. Source: Theorem 5.2, `04-compression.tex`,
lines 342–417. -/
theorem norm_sourceVectorAt : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (e : w.sourceLocations) → (ξ : w.branchLabels e.1) → ‖w.sourceVectorAt e ξ‖ = 1
  | _, _, PartyCircuit.done _, e, _ => Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ g, e, ξ => g.gate.vector_norm ξ e.2
  | _, _, PartyCircuit.localOp _ _ _, e, _ => Empty.elim e.1
  | _, _, PartyCircuit.localOps _, e, _ => Empty.elim e.1
  | _, _, PartyCircuit.comp c c', e, ξ => match e, ξ with
    | ⟨Sum.inl g, i⟩, ξ => norm_sourceVectorAt c ⟨g, i⟩ ξ
    | ⟨Sum.inr g, i⟩, ξ => norm_sourceVectorAt c' ⟨g, i⟩ ξ

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The pair source at a position: its two endpoints and the bases of its slot, with a
prescribed vector. Source: Theorem 5.2, `04-compression.tex`, lines 253–267 and 342–355. -/
def pairSourceAt (w : SourceCircuit X Y) (e : w.sourceLocations)
    (v : EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e)) : PairSource P where
  left := (w.endpoints e).1
  right := (w.endpoints e).2
  distinct := w.endpoints_ne e
  leftBasis := w.leftBasis e
  rightBasis := w.rightBasis e
  vector := v

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The Schmidt indices at both endpoints of every position of a set `S`. Source: Theorem 5.2,
`04-compression.tex`, lines 383–434. -/
abbrev CorrectedSchmidtCoordinates (w : SourceCircuit X Y) (S : Finset w.sourceLocations) :=
  ∀ e : S, Fin (min (w.sourceDims e.1).1 (w.sourceDims e.1).2) ×
    Fin (min (w.sourceDims e.1).1 (w.sourceDims e.1).2)

/-! ### The kept sources of a branch -/

variable (A : P → Bool)

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The source of the branch of a choice at a position, read on the affected parties and the
exterior party, when it stays a pair source; an untouched gate asks for no label and keeps no
source. Source: Theorem 5.2, `04-compression.tex`, lines 351–417. -/
def sourceAt : {X Y : P → Type} → (w : SourceCircuit X Y) → Choices A w →
    w.sourceLocations → Option (PairSource (Option {p // A p = true}))
  | _, _, PartyCircuit.done _ => fun _ e ↦ Empty.elim e.1
  | _, _, PartyCircuit.gate D _ g => fun ξ e ↦
    if h : PreparedGate.IsTouched A D then
      let j : Fin g.gate.slots.length := e.2
      PairSource.mapOwner (affectedOwner A)
        { left := (g.gate.slots.get j).left.1
          right := (g.gate.slots.get j).right.1
          distinct := fun h' ↦ (g.gate.slots.get j).distinct (Subtype.ext h')
          leftBasis := g.gate.bases.left j
          rightBasis := g.gate.bases.right j
          leftFintype := g.gate.bases.leftFintype j
          leftDecEq := g.gate.bases.leftDecEq j
          rightFintype := g.gate.bases.rightFintype j
          rightDecEq := g.gate.bases.rightDecEq j
          vector := g.gate.vector (cast (ite_eq_left h) ξ) j }
    else none
  | _, _, PartyCircuit.localOp _ _ _ => fun _ e ↦ Empty.elim e.1
  | _, _, PartyCircuit.localOps _ => fun _ e ↦ Empty.elim e.1
  | _, _, PartyCircuit.comp c c' => fun ξ e ↦ match e with
    | ⟨Sum.inl g, i⟩ => sourceAt c ξ.1 ⟨g, i⟩
    | ⟨Sum.inr g, i⟩ => sourceAt c' ξ.2 ⟨g, i⟩

/-- A position of the first part of a composition keeps its source. -/
@[simp] theorem sourceAt_comp_inl (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (ξ : Choices A (PartyCircuit.comp w w')) (g : w.gateLocations) (i : Fin (w.slotCount g)) :
    sourceAt A (PartyCircuit.comp w w') ξ ⟨Sum.inl g, i⟩ = sourceAt A w ξ.1 ⟨g, i⟩ :=
  rfl

/-- A position of the second part of a composition keeps its source. -/
@[simp] theorem sourceAt_comp_inr (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (ξ : Choices A (PartyCircuit.comp w w')) (g : w'.gateLocations) (i : Fin (w'.slotCount g)) :
    sourceAt A (PartyCircuit.comp w w') ξ ⟨Sum.inr g, i⟩ = sourceAt A w' ξ.2 ⟨g, i⟩ :=
  rfl

/-- An untouched gate keeps no source. -/
theorem sourceAt_gate_of_not_isTouched (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (h : ¬ PreparedGate.IsTouched A D)
    (ξ : Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y))
    (e : sourceLocations (PartyCircuit.gate D hY g : SourceCircuit X Y)) :
    sourceAt A (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ e = none :=
  dite_eq_right h

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- **The kept source is the pair source of the position with the vector of the chosen label**,
read on the affected parties. Source: Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem sourceAt_eq_mapOwner_sourceVectorAt : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (ξ : Choices A w) → (e : w.sourceLocations) → (he : IsTouched A w e.1) →
      sourceAt A w ξ e =
        (pairSourceAt w e (w.sourceVectorAt e (choiceAt A w ξ e.1 he))).mapOwner
          (affectedOwner A)
  | _, _, PartyCircuit.done _, _, e, _ => Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ _, _, _, he => dite_eq_left he
  | _, _, PartyCircuit.localOp _ _ _, _, e, _ => Empty.elim e.1
  | _, _, PartyCircuit.localOps _, _, e, _ => Empty.elim e.1
  | _, _, PartyCircuit.comp c c', ξ, e, he => match e, he with
    | ⟨Sum.inl g, i⟩, he => sourceAt_eq_mapOwner_sourceVectorAt c ξ.1 ⟨g, i⟩ he
    | ⟨Sum.inr g, i⟩, he => sourceAt_eq_mapOwner_sourceVectorAt c' ξ.2 ⟨g, i⟩ he

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- A pair source stays a pair source on the affected parties exactly when an endpoint is
affected. -/
theorem isSome_mapOwner_affectedOwner (s : PairSource P) :
    (s.mapOwner (affectedOwner A)).isSome = true ↔ A s.left = true ∨ A s.right = true := by
  simp [PairSource.mapOwner, ← s.affectedOwner_ne_iff A]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The source at a position, for every position: at a touched one by
`sourceAt_eq_mapOwner_sourceVectorAt`, and none at an untouched one. -/
theorem sourceAt_eq_dite (w : SourceCircuit X Y) (ξ : Choices A w) (e : w.sourceLocations) :
    sourceAt A w ξ e = if h : IsTouched A w e.1 then
      (pairSourceAt w e (w.sourceVectorAt e (choiceAt A w ξ e.1 h))).mapOwner
        (affectedOwner A) else none := by
  split_ifs with h
  · exact sourceAt_eq_mapOwner_sourceVectorAt A w ξ e h
  · induction w with
    | done => exact Empty.elim e.1
    | gate D hY g => exact dite_eq_right h
    | localOp => exact Empty.elim e.1
    | localOps => exact Empty.elim e.1
    | comp c c' ihc ihc' =>
      obtain ⟨g | g, i⟩ := e
      · exact ihc ξ.1 ⟨g, i⟩ h
      · exact ihc' ξ.2 ⟨g, i⟩ h

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- **A position keeps its source exactly when an endpoint is affected**, whatever the choice.
Source: Theorem 5.2, `04-compression.tex`, lines 383–417. -/
theorem sourceAt_isSome_iff (w : SourceCircuit X Y) (ξ : Choices A w) (e : w.sourceLocations) :
    (sourceAt A w ξ e).isSome = true ↔
      A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true := by
  rw [sourceAt_eq_dite]
  split_ifs with h
  · exact isSome_mapOwner_affectedOwner A _
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun he ↦ h (isTouched_of_source_endpoint A w e he)

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- A kept source has the endpoints of its position read on the affected parties and a
normalized vector. Source: Theorem 5.2, `04-compression.tex`, lines 253–267 and 383–417. -/
theorem sourceAt_eq_some_spec (w : SourceCircuit X Y) (ξ : Choices A w) (e : w.sourceLocations)
    {s : PairSource (Option {p // A p = true})} (h : sourceAt A w ξ e = some s) :
    s.left = affectedOwner A (w.endpoints e).1 ∧
      s.right = affectedOwner A (w.endpoints e).2 ∧ ‖s.vector‖ = 1 := by
  rw [sourceAt_eq_dite] at h
  split_ifs at h with ht
  simp only [PairSource.mapOwner] at h
  split_ifs at h
  cases Option.some.inj h
  exact ⟨rfl, rfl, w.norm_sourceVectorAt e _⟩

/-- At a composition, the kept sources of the later part precede those of the earlier part.
Source: Theorem 5.2, `04-compression.tex`, lines 351–355. -/
theorem filterMap_sourceAt_comp (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (ξ : Choices A (PartyCircuit.comp w w')) :
    (sourceOrder (PartyCircuit.comp w w')).filterMap (sourceAt A (PartyCircuit.comp w w') ξ) =
      (sourceOrder w').filterMap (sourceAt A w' ξ.2) ++
        (sourceOrder w).filterMap (sourceAt A w ξ.1) :=
  (List.filterMap_append ..).trans
    (congrArg₂ (· ++ ·) (List.filterMap_map ..) (List.filterMap_map ..))

/-- At a gate, the kept sources are read off its slots in their order. Source: Theorem 5.2,
`04-compression.tex`, lines 351–355. -/
theorem filterMap_sourceAt_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (ξ : Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y)) :
    (sourceOrder (PartyCircuit.gate D hY g : SourceCircuit X Y)).filterMap
        (sourceAt A (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ) =
      (List.finRange g.gate.slots.length).filterMap
        fun i ↦ sourceAt A (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ ⟨(), i⟩ :=
  (congrArg _ (sourceOrder_gate D hY g)).trans (List.filterMap_map ..)

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- **The source inventory of every branch is the list of kept sources at the ordered
positions.** Source: Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem sources_partialWord_eq_filterMap [Fintype P] : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (ξ : Choices A w) →
      (partialWord A w ξ).sources = (sourceOrder w).filterMap (sourceAt A w ξ)
  | _, _, _, _, PartyCircuit.done _, _ => rfl
  | _, _, _, _, PartyCircuit.gate D hY g, ξ => by
    rw [filterMap_sourceAt_gate]
    by_cases h : PreparedGate.IsTouched A D
    · rw [partialWord_gate_of_isTouched A D hY g h, Word.sources_coarsen, Word.sources_onCell,
        g.gate.sources_branchWord, SourceInventory.mapOwner, SourceInventory.mapOwner,
        SourceInventory.ofSlots, List.ofFn_eq_map, List.filterMap_map, List.filterMap_filterMap]
      refine List.filterMap_congr fun i _ ↦ ?_
      simp only [Function.comp_apply, PairSource.mapOwner]
      rw [dite_eq_right fun h' ↦ (g.gate.slots.get i).distinct (Subtype.ext h')]
      rw [show sourceAt A (PartyCircuit.gate D hY g : SourceCircuit _ _) ξ ⟨(), i⟩ = _ from
        dite_eq_left h]
      rfl
    · rw [partialWord_gate_of_not_isTouched A D hY g h]
      refine (List.filterMap_eq_nil_iff.mpr fun i _ ↦ ?_).symm
      exact dite_eq_right h
  | _, _, _, _, PartyCircuit.localOp p hY U, _ => by
    rw [partialWord_localOp, Word.sources_coarsen]
    rfl
  | _, _, _, _, PartyCircuit.localOps U, _ => by
    rw [partialWord_localOps, Word.sources_coarsen]
    rfl
  | _, _, _, _, PartyCircuit.comp c c', ξ => by
    rw [filterMap_sourceAt_comp, partialWord_comp, Word.sources_comp,
      sources_partialWord_eq_filterMap c ξ.1, sources_partialWord_eq_filterMap c' ξ.2]

end SourceCircuit

end QuantumCircuit.Party
