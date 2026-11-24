/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.Locations

/-!
# Choices of a partial expansion as labels at touched gate occurrences

A choice of a partial expansion of a source circuit along affected parties `A` determines one
branch label at every gate occurrence touched by `A` (`SourceCircuit.choiceAt`). Conversely,
one label at each touched occurrence gives a choice (`SourceCircuit.choicesOfTouchedLabels`):
the choices are the same data as these labels (`SourceCircuit.choicesTouchedLabelsEquiv`), also
when a branch type is empty. Keeping the labels of a choice for all parties at the occurrences
touched by `A` projects it to a choice for `A` (`SourceCircuit.projectAllChoices`). When every
party is affected, the touched occurrences are those with a nonempty cell
(`SourceCircuit.nonemptyGateLocations`), and each of them has a party of its cell
(`SourceCircuit.sourceGateRoot`).

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.choiceAt` — the label of a choice at a touched
  occurrence.
* `QuantumCircuit.Party.SourceCircuit.TouchedLabels`,
  `QuantumCircuit.Party.SourceCircuit.choicesOfTouchedLabels`,
  `QuantumCircuit.Party.SourceCircuit.choicesTouchedLabelsEquiv` — labels at touched
  occurrences.
* `QuantumCircuit.Party.SourceCircuit.projectAllChoices` — projection of a choice for all
  parties.
* `QuantumCircuit.Party.SourceCircuit.nonemptyGateLocations`,
  `QuantumCircuit.Party.SourceCircuit.allChoicesNonemptyLabelsEquiv`,
  `QuantumCircuit.Party.SourceCircuit.sourceGateRoot` — the occurrences with a nonempty cell.

## Main results

* `QuantumCircuit.Party.SourceCircuit.choiceAt_choicesOfTouchedLabels`,
  `QuantumCircuit.Party.SourceCircuit.choicesOfTouchedLabels_choiceAt`.
* `QuantumCircuit.Party.SourceCircuit.choiceAt_projectAllChoices`.
* `QuantumCircuit.Party.SourceCircuit.isTouched_of_source_endpoint`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 342–381 and 565–579.

Adapted from TNLean, `TNLean/Lattice/Compression/TouchedLabels.lean`,
`TNLean/Lattice/Compression/NonemptyGateLabels.lean`,
`TNLean/Lattice/Compression/SourceGateRoot.lean` and the first part of
`TNLean/Lattice/Compression/SourceCircuitChoiceAt.lean` at commit `a05f5d6d0a` (Apache-2.0).
-/

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace SourceCircuit

variable (A : P → Bool)

/-! ### The label of a choice at a touched occurrence -/

/-- The branch label that a choice of the partial expansion selects at a touched gate
occurrence. Source: Theorem 5.2, `04-compression.tex`, lines 342–417. -/
def choiceAt : {X Y : P → Type} → (w : SourceCircuit X Y) → Choices A w →
    (g : w.gateLocations) → IsTouched A w g → w.branchLabels g
  | _, _, PartyCircuit.done _ => fun _ g ↦ Empty.elim g
  | _, _, PartyCircuit.gate _ _ _ => fun ξ _ h ↦ cast (ite_eq_left h) ξ
  | _, _, PartyCircuit.localOp _ _ _ => fun _ g ↦ Empty.elim g
  | _, _, PartyCircuit.localOps _ => fun _ g ↦ Empty.elim g
  | _, _, PartyCircuit.comp c c' => fun ξ g ↦ match g with
    | Sum.inl g => choiceAt c ξ.1 g
    | Sum.inr g => choiceAt c' ξ.2 g

variable {X Y Z : P → Type}

/-- At a gate, the selected label is the label chosen at the gate. -/
theorem choiceAt_gate [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (D : Finset P)
    (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y)
    (ξ : Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y)) (o : Unit)
    (h : IsTouched A (PartyCircuit.gate D hY g : SourceCircuit X Y) o) :
    choiceAt A (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ o h = choiceLabel A hY g h ξ :=
  rfl

/-- An occurrence of the first part of a composition keeps its selected label. -/
@[simp] theorem choiceAt_comp_inl [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (ξ : Choices A (PartyCircuit.comp w w')) (g : w.gateLocations)
    (h : IsTouched A (PartyCircuit.comp w w') (Sum.inl g)) :
    choiceAt A (PartyCircuit.comp w w') ξ (Sum.inl g) h = choiceAt A w ξ.1 g h :=
  rfl

/-- An occurrence of the second part of a composition keeps its selected label. -/
@[simp] theorem choiceAt_comp_inr [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (ξ : Choices A (PartyCircuit.comp w w')) (g : w'.gateLocations)
    (h : IsTouched A (PartyCircuit.comp w w') (Sum.inr g)) :
    choiceAt A (PartyCircuit.comp w w') ξ (Sum.inr g) h = choiceAt A w' ξ.2 g h :=
  rfl

/-- Whether an occurrence is touched is decidable. -/
instance instDecidablePredIsTouched (w : SourceCircuit X Y) : DecidablePred (IsTouched A w) :=
  fun g ↦ inferInstanceAs (Decidable (∃ p ∈ w.participants g, A p = true))

/-- A source position with an affected endpoint lies at a touched gate occurrence.
Source: Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem isTouched_of_source_endpoint (w : SourceCircuit X Y) (e : w.sourceLocations)
    (he : A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true) : IsTouched A w e.1 := by
  rcases he with he | he
  · exact ⟨(w.endpoints e).1, (w.endpoints_mem_participants e).1, he⟩
  · exact ⟨(w.endpoints e).2, (w.endpoints_mem_participants e).2, he⟩

/-! ### Labels at the touched occurrences -/

/-- One branch label at each gate occurrence touched by the affected parties; an untouched
occurrence carries no label. Source: `04-compression.tex`, lines 351–381. -/
def TouchedLabels (w : SourceCircuit X Y) : Type :=
  (g : w.gateLocations) → IsTouched A w g → w.branchLabels g

/-- The choice of a partial expansion with prescribed labels at the touched occurrences.
Source: `04-compression.tex`, lines 351–381. -/
def choicesOfTouchedLabels : {X Y : P → Type} → (w : SourceCircuit X Y) →
    TouchedLabels A w → Choices A w
  | _, _, PartyCircuit.done _ => fun _ ↦ ()
  | _, _, PartyCircuit.gate D _ _ => fun ξ ↦
    if h : PreparedGate.IsTouched A D then cast (ite_eq_left h).symm (ξ () h)
    else cast (ite_eq_right h).symm ()
  | _, _, PartyCircuit.localOp _ _ _ => fun _ ↦ ()
  | _, _, PartyCircuit.localOps _ => fun _ ↦ ()
  | _, _, PartyCircuit.comp c c' => fun ξ ↦
    (choicesOfTouchedLabels c fun g h ↦ ξ (Sum.inl g) h,
      choicesOfTouchedLabels c' fun g h ↦ ξ (Sum.inr g) h)

/-- Reading the choice built from labels at a touched occurrence returns the prescribed label.
Source: `04-compression.tex`, lines 351–381. -/
theorem choiceAt_choicesOfTouchedLabels : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (ξ : TouchedLabels A w) → (g : w.gateLocations) → (hg : IsTouched A w g) →
      choiceAt A w (choicesOfTouchedLabels A w ξ) g hg = ξ g hg
  | _, _, PartyCircuit.done _, _, g, _ => Empty.elim g
  | _, _, PartyCircuit.gate D _ _, ξ, o, hg => by
    cases o
    simp only [choiceAt, choicesOfTouchedLabels,
      dite_eq_left (show PreparedGate.IsTouched A D from hg)]
    exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
  | _, _, PartyCircuit.localOp _ _ _, _, g, _ => Empty.elim g
  | _, _, PartyCircuit.localOps _, _, g, _ => Empty.elim g
  | _, _, PartyCircuit.comp c c', ξ, g, hg => match g, hg with
    | Sum.inl g, hg => choiceAt_choicesOfTouchedLabels c (fun g h ↦ ξ (Sum.inl g) h) g hg
    | Sum.inr g, hg => choiceAt_choicesOfTouchedLabels c' (fun g h ↦ ξ (Sum.inr g) h) g hg

/-- The labels selected by a choice at the touched occurrences give back the choice.
Source: `04-compression.tex`, lines 351–381. -/
theorem choicesOfTouchedLabels_choiceAt : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (ξ : Choices A w) → choicesOfTouchedLabels A w (choiceAt A w ξ) = ξ
  | _, _, PartyCircuit.done _, _ => rfl
  | _, _, PartyCircuit.gate D hY g, ξ => by
    by_cases h : PreparedGate.IsTouched A D
    · simp only [choiceAt, choicesOfTouchedLabels, dite_eq_left h]
      exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
    · have : Subsingleton (Choices A (PartyCircuit.gate D hY g : SourceCircuit _ _)) := by
        rw [choices_gate, ite_eq_right h]
        infer_instance
      exact Subsingleton.elim _ _
  | _, _, PartyCircuit.localOp _ _ _, _ => rfl
  | _, _, PartyCircuit.localOps _, _ => rfl
  | _, _, PartyCircuit.comp c c', ξ =>
    Prod.ext (choicesOfTouchedLabels_choiceAt c ξ.1) (choicesOfTouchedLabels_choiceAt c' ξ.2)

/-- The choices of a partial expansion are the labels at precisely the touched occurrences,
also for empty branch types. Source: `04-compression.tex`, lines 351–381 and 565–573. -/
def choicesTouchedLabelsEquiv (w : SourceCircuit X Y) : Choices A w ≃ TouchedLabels A w where
  toFun := choiceAt A w
  invFun := choicesOfTouchedLabels A w
  left_inv := choicesOfTouchedLabels_choiceAt A w
  right_inv ξ := funext fun g ↦ funext fun hg ↦ choiceAt_choicesOfTouchedLabels A w ξ g hg

/-- The choice for the affected parties `A` that keeps the labels of a choice for all parties at
the occurrences touched by `A`. A gate with an empty cell requests no label in either
expansion. Source: `04-compression.tex`, lines 351–381. -/
def projectAllChoices (w : SourceCircuit X Y) (ξ : Choices (fun _ ↦ true) w) : Choices A w :=
  choicesOfTouchedLabels A w fun g hg ↦
    choiceAt (fun _ ↦ true) w ξ g (by obtain ⟨p, hp, _⟩ := hg; exact ⟨p, hp, rfl⟩)

/-- A projected choice selects the label of the choice for all parties at the same
occurrence. Source: `04-compression.tex`, lines 351–381. -/
theorem choiceAt_projectAllChoices (w : SourceCircuit X Y) (ξ : Choices (fun _ ↦ true) w)
    (g : w.gateLocations) (hg : IsTouched A w g) :
    choiceAt A w (projectAllChoices A w ξ) g hg =
      choiceAt (fun _ ↦ true) w ξ g (by obtain ⟨p, hp, _⟩ := hg; exact ⟨p, hp, rfl⟩) :=
  choiceAt_choicesOfTouchedLabels A w _ g hg

/-! ### The occurrences with a nonempty cell -/

/-- When every party is affected, the touched occurrences are those with a nonempty cell.
Source: `04-compression.tex`, lines 351–381. -/
theorem isTouched_all_iff (w : SourceCircuit X Y) (g : w.gateLocations) :
    IsTouched (fun _ ↦ true) w g ↔ (w.participants g).Nonempty :=
  ⟨fun ⟨p, hp, _⟩ ↦ ⟨p, hp⟩, fun ⟨p, hp⟩ ↦ ⟨p, hp, rfl⟩⟩

/-- The gate occurrences whose cell is nonempty: they carry the labels of the expansion for all
parties, while a gate with an empty cell stays a scalar. Source: `04-compression.tex`,
lines 351–381 and 565–573. -/
def nonemptyGateLocations (w : SourceCircuit X Y) : Type :=
  {g : w.gateLocations // (w.participants g).Nonempty}

/-- There are finitely many occurrences with a nonempty cell. -/
instance instFintypeNonemptyGateLocations (w : SourceCircuit X Y) :
    Fintype w.nonemptyGateLocations :=
  inferInstanceAs (Fintype {g : w.gateLocations // (w.participants g).Nonempty})

/-- The choices of the expansion for all parties are the labels at the occurrences with a
nonempty cell; no label is requested at an empty cell. Source: `04-compression.tex`,
lines 351–381 and 565–573. -/
def allChoicesNonemptyLabelsEquiv (w : SourceCircuit X Y) :
    Choices (fun _ ↦ true) w ≃ ((g : w.nonemptyGateLocations) → w.branchLabels g.1) :=
  (choicesTouchedLabelsEquiv (fun _ ↦ true) w).trans
    { toFun := fun ξ g ↦ ξ g.1 ((isTouched_all_iff w g.1).mpr g.2)
      invFun := fun ξ g hg ↦ ξ ⟨g, (isTouched_all_iff w g).mp hg⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- The equivalence keeps the label of each occurrence. Source: `04-compression.tex`,
lines 351–381. -/
theorem allChoicesNonemptyLabelsEquiv_apply (w : SourceCircuit X Y)
    (ξ : Choices (fun _ ↦ true) w) (g : w.nonemptyGateLocations) :
    allChoicesNonemptyLabelsEquiv w ξ g =
      choiceAt (fun _ ↦ true) w ξ g.1 ((isTouched_all_iff w g.1).mpr g.2) :=
  rfl

/-- A chosen party of the cell of an occurrence with a nonempty cell. Source: Theorem 5.2,
`04-compression.tex`, lines 565–579. -/
noncomputable def sourceGateRoot (w : SourceCircuit X Y) (g : w.nonemptyGateLocations) : P :=
  g.2.choose

/-- The chosen party lies in the cell of the occurrence. Source: Theorem 5.2,
`04-compression.tex`, lines 565–579. -/
theorem sourceGateRoot_mem (w : SourceCircuit X Y) (g : w.nonemptyGateLocations) :
    sourceGateRoot w g ∈ w.participants g.1 :=
  g.2.choose_spec

end SourceCircuit

end QuantumCircuit.Party
