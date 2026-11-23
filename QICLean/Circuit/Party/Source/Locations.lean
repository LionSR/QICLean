/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.PreparedGate

/-!
# Gate and source positions of a source circuit

The gate occurrences of a source circuit are those of its party circuit
(`PartyCircuit.gateLocations`: `Unit` at a gate, `Empty` at a local operation, a sum at a
composition), and a *source position* is a gate occurrence together with one of its common
slots (`SourceCircuit.sourceLocations`), with no branch label. The endpoints of a source position
are two distinct parties of the cell of its gate. The number of slots, the endpoints, the branch
labels and the branch coefficients are structural recursions on the party circuit, so that their
values at a gate and at the two sides of a composition hold by `rfl`. So are the basis types of the
two fresh factors at a source position (`SourceCircuit.leftBasis`, `SourceCircuit.rightBasis`,
the slot bases of its gate), with their dimensions `SourceCircuit.sourceDims`.

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.slotCount`,
  `QuantumCircuit.Party.SourceCircuit.sourceLocations`,
  `QuantumCircuit.Party.SourceCircuit.endpoints` — source positions and their endpoints.
* `QuantumCircuit.Party.SourceCircuit.branchLabels`,
  `QuantumCircuit.Party.SourceCircuit.branchCoefficient` — the branches at a gate occurrence.
* `QuantumCircuit.Party.SourceCircuit.IsTouched` — gate occurrences meeting affected parties.
* `QuantumCircuit.Party.SourceCircuit.leftBasis`, `QuantumCircuit.Party.SourceCircuit.rightBasis`,
  `QuantumCircuit.Party.SourceCircuit.sourceDims` — the bases of the fresh factors at a source
  position and their dimensions.

## Main results

* `QuantumCircuit.Party.SourceCircuit.endpoints_mem_participants`,
  `QuantumCircuit.Party.SourceCircuit.endpoints_ne` — the endpoints are two distinct parties of
  the cell.
* `QuantumCircuit.Party.SourceCircuit.gateLocationsFrameEquiv` and the lemmas `*_frame` —
  framing keeps the positions.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 233–267 and 342–381.
-/

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Positions of a source circuit -/

namespace SourceCircuit

variable {X Y Z : P → Type}

/-- The number of source slots of the gate at an occurrence. Source: Theorem 5.2,
`04-compression.tex`, lines 233–267 and 342–355. -/
def slotCount : {X Y : P → Type} → (w : SourceCircuit X Y) → w.gateLocations → ℕ
  | _, _, PartyCircuit.done _ => Empty.elim
  | _, _, PartyCircuit.gate _ _ g => fun _ ↦ g.gate.slots.length
  | _, _, PartyCircuit.localOp _ _ _ => Empty.elim
  | _, _, PartyCircuit.localOps _ => Empty.elim
  | _, _, PartyCircuit.comp c c' => Sum.elim (slotCount c) (slotCount c')

/-- A source position: a gate occurrence together with one of its common slots, with no branch
label. Source: Theorem 5.2, `04-compression.tex`, lines 342–355. -/
def sourceLocations (w : SourceCircuit X Y) : Type :=
  Σ g : w.gateLocations, Fin (w.slotCount g)

/-- There are finitely many source positions. -/
instance instFintypeSourceLocations (w : SourceCircuit X Y) : Fintype w.sourceLocations :=
  inferInstanceAs (Fintype (Σ g : w.gateLocations, Fin (w.slotCount g)))

/-- The two parties of a source position: the endpoints of its slot. Source: Theorem 5.2,
`04-compression.tex`, lines 342–364. -/
def endpoints : {X Y : P → Type} → (w : SourceCircuit X Y) → w.sourceLocations → P × P
  | _, _, PartyCircuit.done _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ g => fun e ↦
    ((g.gate.slots.get e.2).left.1, (g.gate.slots.get e.2).right.1)
  | _, _, PartyCircuit.localOp _ _ _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.localOps _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.comp c c' => fun
    | ⟨Sum.inl g, i⟩ => endpoints c ⟨g, i⟩
    | ⟨Sum.inr g, i⟩ => endpoints c' ⟨g, i⟩

/-- Both endpoints of a source position lie in the cell of its gate. Source: Theorem 5.2,
`04-compression.tex`, lines 342–364. -/
theorem endpoints_mem_participants : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (e : w.sourceLocations) →
      (w.endpoints e).1 ∈ w.participants e.1 ∧ (w.endpoints e).2 ∈ w.participants e.1
  | _, _, PartyCircuit.done _, e => Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ g, e =>
    ⟨(g.gate.slots.get e.2).left.2, (g.gate.slots.get e.2).right.2⟩
  | _, _, PartyCircuit.localOp _ _ _, e => Empty.elim e.1
  | _, _, PartyCircuit.localOps _, e => Empty.elim e.1
  | _, _, PartyCircuit.comp c c', e => match e with
    | ⟨Sum.inl g, i⟩ => endpoints_mem_participants c ⟨g, i⟩
    | ⟨Sum.inr g, i⟩ => endpoints_mem_participants c' ⟨g, i⟩

/-- The endpoints of a source position are distinct. Source: Theorem 5.2, `04-compression.tex`,
lines 233–245 and 342–364. -/
theorem endpoints_ne : {X Y : P → Type} → (w : SourceCircuit X Y) → (e : w.sourceLocations) →
    (w.endpoints e).1 ≠ (w.endpoints e).2
  | _, _, PartyCircuit.done _, e => Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ g, e => fun h ↦ (g.gate.slots.get e.2).distinct (Subtype.ext h)
  | _, _, PartyCircuit.localOp _ _ _, e => Empty.elim e.1
  | _, _, PartyCircuit.localOps _, e => Empty.elim e.1
  | _, _, PartyCircuit.comp c c', e => match e with
    | ⟨Sum.inl g, i⟩ => endpoints_ne c ⟨g, i⟩
    | ⟨Sum.inr g, i⟩ => endpoints_ne c' ⟨g, i⟩

/-- The branch labels at a gate occurrence: the labels of its gate. Source: Theorem 5.2,
`04-compression.tex`, lines 351–381. -/
def branchLabels : {X Y : P → Type} → (w : SourceCircuit X Y) → w.gateLocations → Type
  | _, _, PartyCircuit.done _ => Empty.elim
  | _, _, PartyCircuit.gate _ _ g => fun _ ↦ g.ι
  | _, _, PartyCircuit.localOp _ _ _ => Empty.elim
  | _, _, PartyCircuit.localOps _ => Empty.elim
  | _, _, PartyCircuit.comp c c' => Sum.elim (branchLabels c) (branchLabels c')

/-- The branch labels at an occurrence form a finite set. -/
instance instFintypeBranchLabels : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (g : w.gateLocations) → Fintype (w.branchLabels g)
  | _, _, PartyCircuit.done _ => fun g ↦ Empty.elim g
  | _, _, PartyCircuit.gate _ _ g => fun _ ↦ inferInstanceAs (Fintype g.ι)
  | _, _, PartyCircuit.localOp _ _ _ => fun g ↦ Empty.elim g
  | _, _, PartyCircuit.localOps _ => fun g ↦ Empty.elim g
  | _, _, PartyCircuit.comp c c' => fun
    | Sum.inl g => instFintypeBranchLabels c g
    | Sum.inr g => instFintypeBranchLabels c' g

/-- The scalar coefficients at a gate occurrence, before any choice of affected parties. Source:
Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex`, lines 351–381. -/
def branchCoefficient : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (g : w.gateLocations) → w.branchLabels g → ℂ
  | _, _, PartyCircuit.done _ => fun g ↦ Empty.elim g
  | _, _, PartyCircuit.gate _ _ g => fun _ ↦ g.coeff
  | _, _, PartyCircuit.localOp _ _ _ => fun g ↦ Empty.elim g
  | _, _, PartyCircuit.localOps _ => fun g ↦ Empty.elim g
  | _, _, PartyCircuit.comp c c' => fun
    | Sum.inl g => branchCoefficient c g
    | Sum.inr g => branchCoefficient c' g

/-- A gate occurrence is touched when a party of its cell is affected. Source: Theorem 5.2,
`04-compression.tex`, lines 356–364. -/
def IsTouched (A : P → Bool) (w : SourceCircuit X Y) (g : w.gateLocations) : Prop :=
  ∃ p ∈ w.participants g, A p = true

/-! #### Computation rules -/

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The empty circuit has no gate occurrence. -/
@[simp] theorem gateLocations_done :
    PartyCircuit.gateLocations (PartyCircuit.done X : SourceCircuit X X) = Empty :=
  rfl

/-- The gate occurrences of a composition are those of its two parts. -/
@[simp] theorem gateLocations_comp (w : SourceCircuit X Y) (w' : SourceCircuit Y Z) :
    PartyCircuit.gateLocations (PartyCircuit.comp w w') =
      (w.gateLocations ⊕ w'.gateLocations) :=
  rfl

/-- A local operation has no gate occurrence. -/
@[simp] theorem gateLocations_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (U : Matrix (Y p) (X p) ℂ) :
    PartyCircuit.gateLocations (PartyCircuit.localOp p hY U : SourceCircuit X Y) = Empty :=
  rfl

/-- Local operations at every party have no gate occurrence. -/
@[simp] theorem gateLocations_localOps (U : ∀ p, Matrix (Y p) (X p) ℂ) :
    PartyCircuit.gateLocations (PartyCircuit.localOps U : SourceCircuit X Y) = Empty :=
  rfl

/-- One gate has one gate occurrence. -/
@[simp] theorem gateLocations_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) :
    PartyCircuit.gateLocations (PartyCircuit.gate D hY g : SourceCircuit X Y) = Unit :=
  rfl

/-- The parties of the occurrence of one gate are its cell. -/
@[simp] theorem participants_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (o : Unit) :
    PartyCircuit.participants (PartyCircuit.gate D hY g : SourceCircuit X Y) o = D :=
  rfl

/-- The number of source positions of one gate is its number of slots. -/
@[simp] theorem slotCount_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (o : Unit) :
    slotCount (PartyCircuit.gate D hY g : SourceCircuit X Y) o = g.gate.slots.length :=
  rfl

/-- A gate occurrence of the first part of a composition keeps its number of slots. -/
@[simp] theorem slotCount_comp_inl (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w.gateLocations) : slotCount (PartyCircuit.comp w w') (Sum.inl g) = w.slotCount g :=
  rfl

/-- A gate occurrence of the second part of a composition keeps its number of slots. -/
@[simp] theorem slotCount_comp_inr (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w'.gateLocations) : slotCount (PartyCircuit.comp w w') (Sum.inr g) = w'.slotCount g :=
  rfl

/-- The endpoints of a source position of one gate are the endpoints of its slot. -/
theorem endpoints_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y)
    (e : sourceLocations (PartyCircuit.gate D hY g : SourceCircuit X Y)) :
    endpoints (PartyCircuit.gate D hY g : SourceCircuit X Y) e =
      ((g.gate.slots.get e.2).left.1, (g.gate.slots.get e.2).right.1) :=
  rfl

/-- A source position of the first part of a composition keeps its endpoints. -/
@[simp] theorem endpoints_comp_inl (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w.gateLocations) (i : Fin (w.slotCount g)) :
    endpoints (PartyCircuit.comp w w') ⟨Sum.inl g, i⟩ = w.endpoints ⟨g, i⟩ :=
  rfl

/-- A source position of the second part of a composition keeps its endpoints. -/
@[simp] theorem endpoints_comp_inr (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w'.gateLocations) (i : Fin (w'.slotCount g)) :
    endpoints (PartyCircuit.comp w w') ⟨Sum.inr g, i⟩ = w'.endpoints ⟨g, i⟩ :=
  rfl

/-- The branch labels of the occurrence of one gate are the labels of the gate. -/
@[simp] theorem branchLabels_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (o : Unit) :
    branchLabels (PartyCircuit.gate D hY g : SourceCircuit X Y) o = g.ι :=
  rfl

/-- A gate occurrence of the first part of a composition keeps its branch labels. -/
@[simp] theorem branchLabels_comp_inl (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w.gateLocations) :
    branchLabels (PartyCircuit.comp w w') (Sum.inl g) = w.branchLabels g :=
  rfl

/-- A gate occurrence of the second part of a composition keeps its branch labels. -/
@[simp] theorem branchLabels_comp_inr (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w'.gateLocations) :
    branchLabels (PartyCircuit.comp w w') (Sum.inr g) = w'.branchLabels g :=
  rfl

/-- The coefficient of a branch label of one gate is the coefficient of the gate. -/
theorem branchCoefficient_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (o : Unit) :
    branchCoefficient (PartyCircuit.gate D hY g : SourceCircuit X Y) o = g.coeff :=
  rfl

/-- A gate occurrence of the first part of a composition keeps its coefficients. -/
theorem branchCoefficient_comp_inl (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w.gateLocations) :
    branchCoefficient (PartyCircuit.comp w w') (Sum.inl g) = w.branchCoefficient g :=
  rfl

/-- A gate occurrence of the second part of a composition keeps its coefficients. -/
theorem branchCoefficient_comp_inr (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w'.gateLocations) :
    branchCoefficient (PartyCircuit.comp w w') (Sum.inr g) = w'.branchCoefficient g :=
  rfl

/-- The occurrence predicate is exactly the gate condition used by the partial monomial choices.
Source: `04-compression.tex`, lines 356–381. -/
theorem isTouched_gate_iff (A : P → Bool) (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (o : Unit) :
    IsTouched A (PartyCircuit.gate D hY g : SourceCircuit X Y) o ↔ PreparedGate.IsTouched A D :=
  Iff.rfl

/-! #### Positions of a framed source circuit -/

section Frame

variable (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The gate occurrences of a framed circuit are those of the circuit
(`PartyCircuit.frameLocationsEquiv`, read backwards). -/
def gateLocationsFrameEquiv [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (w : SourceCircuit X Y) : (w.frame W).gateLocations ≃ w.gateLocations :=
  (PartyCircuit.frameLocationsEquiv W w).symm

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Framing keeps the cell of every occurrence. -/
theorem participants_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (g : (w.frame W).gateLocations) →
      (w.frame W).participants g = w.participants (gateLocationsFrameEquiv W w g)
  | _, _, _, _, PartyCircuit.done _, g => Empty.elim g
  | _, _, _, _, PartyCircuit.gate _ _ _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, g => Empty.elim g
  | _, _, _, _, PartyCircuit.localOps _, g => Empty.elim g
  | _, _, _, _, PartyCircuit.comp c c', g => match g with
    | Sum.inl g => participants_frame c g
    | Sum.inr g => participants_frame c' g

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Framing keeps the number of slots of every occurrence. -/
theorem slotCount_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (g : (w.frame W).gateLocations) →
      (w.frame W).slotCount g = w.slotCount (gateLocationsFrameEquiv W w g)
  | _, _, _, _, PartyCircuit.done _, g => Empty.elim g
  | _, _, _, _, PartyCircuit.gate _ _ _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, g => Empty.elim g
  | _, _, _, _, PartyCircuit.localOps _, g => Empty.elim g
  | _, _, _, _, PartyCircuit.comp c c', g => match g with
    | Sum.inl g => slotCount_frame c g
    | Sum.inr g => slotCount_frame c' g

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Framing keeps the endpoints of every source position. -/
theorem endpoints_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (g : (w.frame W).gateLocations) → (i : Fin ((w.frame W).slotCount g)) →
      (w.frame W).endpoints ⟨g, i⟩ =
        w.endpoints ⟨gateLocationsFrameEquiv W w g, Fin.cast (slotCount_frame W w g) i⟩
  | _, _, _, _, PartyCircuit.done _, g, _ => Empty.elim g
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, g, _ => Empty.elim g
  | _, _, _, _, PartyCircuit.localOps _, g, _ => Empty.elim g
  | _, _, _, _, PartyCircuit.comp c c', g, i => match g, i with
    | Sum.inl g, i => endpoints_frame c g i
    | Sum.inr g, i => endpoints_frame c' g i

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Framing keeps the branch labels of every occurrence. -/
theorem branchLabels_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (g : (w.frame W).gateLocations) →
      (w.frame W).branchLabels g = w.branchLabels (gateLocationsFrameEquiv W w g)
  | _, _, _, _, PartyCircuit.done _, g => Empty.elim g
  | _, _, _, _, PartyCircuit.gate _ _ _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, g => Empty.elim g
  | _, _, _, _, PartyCircuit.localOps _, g => Empty.elim g
  | _, _, _, _, PartyCircuit.comp c c', g => match g with
    | Sum.inl g => branchLabels_frame c g
    | Sum.inr g => branchLabels_frame c' g

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Framing keeps the branch coefficients of every occurrence. -/
theorem branchCoefficient_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (g : (w.frame W).gateLocations) → (ξ : (w.frame W).branchLabels g) →
      (w.frame W).branchCoefficient g ξ =
        w.branchCoefficient (gateLocationsFrameEquiv W w g) (cast (branchLabels_frame W w g) ξ)
  | _, _, _, _, PartyCircuit.done _, g, _ => Empty.elim g
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, g, _ => Empty.elim g
  | _, _, _, _, PartyCircuit.localOps _, g, _ => Empty.elim g
  | _, _, _, _, PartyCircuit.comp c c', g, ξ => match g, ξ with
    | Sum.inl g, ξ => branchCoefficient_frame c g ξ
    | Sum.inr g, ξ => branchCoefficient_frame c' g ξ

end Frame

end SourceCircuit

/-! ### The bases of the fresh factors at a source position -/

namespace SourceCircuit

variable {X Y Z : P → Type}

/-- The basis of the fresh factor at the first endpoint of a source position: the slot basis of
its gate. Source: Theorem 5.2, `04-compression.tex`, lines 253–267 and 342–355. -/
def leftBasis : {X Y : P → Type} → (w : SourceCircuit X Y) → w.sourceLocations → Type
  | _, _, PartyCircuit.done _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ g => fun e ↦ g.gate.bases.left e.2
  | _, _, PartyCircuit.localOp _ _ _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.localOps _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.comp c c' => fun
    | ⟨Sum.inl g, i⟩ => leftBasis c ⟨g, i⟩
    | ⟨Sum.inr g, i⟩ => leftBasis c' ⟨g, i⟩

/-- The basis of the fresh factor at the second endpoint of a source position: the slot basis of
its gate. Source: Theorem 5.2, `04-compression.tex`, lines 253–267 and 342–355. -/
def rightBasis : {X Y : P → Type} → (w : SourceCircuit X Y) → w.sourceLocations → Type
  | _, _, PartyCircuit.done _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ g => fun e ↦ g.gate.bases.right e.2
  | _, _, PartyCircuit.localOp _ _ _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.localOps _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.comp c c' => fun
    | ⟨Sum.inl g, i⟩ => rightBasis c ⟨g, i⟩
    | ⟨Sum.inr g, i⟩ => rightBasis c' ⟨g, i⟩

/-- The basis at the first endpoint of a source position is finite. -/
instance instFintypeLeftBasis : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (e : w.sourceLocations) → Fintype (w.leftBasis e)
  | _, _, PartyCircuit.done _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ g => fun e ↦ g.gate.bases.leftFintype e.2
  | _, _, PartyCircuit.localOp _ _ _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.localOps _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.comp c c' => fun
    | ⟨Sum.inl g, i⟩ => instFintypeLeftBasis c ⟨g, i⟩
    | ⟨Sum.inr g, i⟩ => instFintypeLeftBasis c' ⟨g, i⟩

/-- The basis at the first endpoint of a source position has decidable equality. -/
instance instDecidableEqLeftBasis : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (e : w.sourceLocations) → DecidableEq (w.leftBasis e)
  | _, _, PartyCircuit.done _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ g => fun e ↦ g.gate.bases.leftDecEq e.2
  | _, _, PartyCircuit.localOp _ _ _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.localOps _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.comp c c' => fun
    | ⟨Sum.inl g, i⟩ => instDecidableEqLeftBasis c ⟨g, i⟩
    | ⟨Sum.inr g, i⟩ => instDecidableEqLeftBasis c' ⟨g, i⟩

/-- The basis at the second endpoint of a source position is finite. -/
instance instFintypeRightBasis : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (e : w.sourceLocations) → Fintype (w.rightBasis e)
  | _, _, PartyCircuit.done _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ g => fun e ↦ g.gate.bases.rightFintype e.2
  | _, _, PartyCircuit.localOp _ _ _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.localOps _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.comp c c' => fun
    | ⟨Sum.inl g, i⟩ => instFintypeRightBasis c ⟨g, i⟩
    | ⟨Sum.inr g, i⟩ => instFintypeRightBasis c' ⟨g, i⟩

/-- The basis at the second endpoint of a source position has decidable equality. -/
instance instDecidableEqRightBasis : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (e : w.sourceLocations) → DecidableEq (w.rightBasis e)
  | _, _, PartyCircuit.done _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.gate _ _ g => fun e ↦ g.gate.bases.rightDecEq e.2
  | _, _, PartyCircuit.localOp _ _ _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.localOps _ => fun e ↦ Empty.elim e.1
  | _, _, PartyCircuit.comp c c' => fun
    | ⟨Sum.inl g, i⟩ => instDecidableEqRightBasis c ⟨g, i⟩
    | ⟨Sum.inr g, i⟩ => instDecidableEqRightBasis c' ⟨g, i⟩

/-- The dimensions of the two fresh factors at a source position: the numbers of elements of
its two slot bases. Source: Theorem 5.2, `04-compression.tex`, lines 253–267 and 342–355. -/
def sourceDims (w : SourceCircuit X Y) (e : w.sourceLocations) : ℕ × ℕ :=
  (Fintype.card (w.leftBasis e), Fintype.card (w.rightBasis e))

/-! #### Computation rules of the bases -/

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The basis at the first endpoint of a source position of one gate is its slot basis. -/
theorem leftBasis_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y)
    (e : sourceLocations (PartyCircuit.gate D hY g : SourceCircuit X Y)) :
    leftBasis (PartyCircuit.gate D hY g : SourceCircuit X Y) e = g.gate.bases.left e.2 :=
  rfl

/-- The basis at the second endpoint of a source position of one gate is its slot basis. -/
theorem rightBasis_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y)
    (e : sourceLocations (PartyCircuit.gate D hY g : SourceCircuit X Y)) :
    rightBasis (PartyCircuit.gate D hY g : SourceCircuit X Y) e = g.gate.bases.right e.2 :=
  rfl

/-- A source position of the first part of a composition keeps its first basis. -/
@[simp] theorem leftBasis_comp_inl (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w.gateLocations) (i : Fin (w.slotCount g)) :
    leftBasis (PartyCircuit.comp w w') ⟨Sum.inl g, i⟩ = w.leftBasis ⟨g, i⟩ :=
  rfl

/-- A source position of the second part of a composition keeps its first basis. -/
@[simp] theorem leftBasis_comp_inr (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w'.gateLocations) (i : Fin (w'.slotCount g)) :
    leftBasis (PartyCircuit.comp w w') ⟨Sum.inr g, i⟩ = w'.leftBasis ⟨g, i⟩ :=
  rfl

/-- A source position of the first part of a composition keeps its second basis. -/
@[simp] theorem rightBasis_comp_inl (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w.gateLocations) (i : Fin (w.slotCount g)) :
    rightBasis (PartyCircuit.comp w w') ⟨Sum.inl g, i⟩ = w.rightBasis ⟨g, i⟩ :=
  rfl

/-- A source position of the second part of a composition keeps its second basis. -/
@[simp] theorem rightBasis_comp_inr (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w'.gateLocations) (i : Fin (w'.slotCount g)) :
    rightBasis (PartyCircuit.comp w w') ⟨Sum.inr g, i⟩ = w'.rightBasis ⟨g, i⟩ :=
  rfl

/-- The dimensions at a source position of one gate are those of its slot bases. -/
theorem sourceDims_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y)
    (i : Fin g.gate.slots.length) :
    sourceDims (PartyCircuit.gate D hY g : SourceCircuit X Y) ⟨(), i⟩ =
      (Fintype.card (g.gate.bases.left i), Fintype.card (g.gate.bases.right i)) :=
  rfl

/-- A source position of the first part of a composition keeps its dimensions. -/
@[simp] theorem sourceDims_comp_inl (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w.gateLocations) (i : Fin (w.slotCount g)) :
    sourceDims (PartyCircuit.comp w w') ⟨Sum.inl g, i⟩ = w.sourceDims ⟨g, i⟩ :=
  rfl

/-- A source position of the second part of a composition keeps its dimensions. -/
@[simp] theorem sourceDims_comp_inr (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (g : w'.gateLocations) (i : Fin (w'.slotCount g)) :
    sourceDims (PartyCircuit.comp w w') ⟨Sum.inr g, i⟩ = w'.sourceDims ⟨g, i⟩ :=
  rfl

/-! #### Framing -/

section Frame

variable (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Framing keeps the basis at the first endpoint of every source position. -/
theorem leftBasis_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (g : (w.frame W).gateLocations) → (i : Fin ((w.frame W).slotCount g)) →
      (w.frame W).leftBasis ⟨g, i⟩ =
        w.leftBasis ⟨gateLocationsFrameEquiv W w g, Fin.cast (slotCount_frame W w g) i⟩
  | _, _, _, _, PartyCircuit.done _, g, _ => Empty.elim g
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, g, _ => Empty.elim g
  | _, _, _, _, PartyCircuit.localOps _, g, _ => Empty.elim g
  | _, _, _, _, PartyCircuit.comp c c', g, i => match g, i with
    | Sum.inl g, i => leftBasis_frame c g i
    | Sum.inr g, i => leftBasis_frame c' g i

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Framing keeps the basis at the second endpoint of every source position. -/
theorem rightBasis_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (g : (w.frame W).gateLocations) → (i : Fin ((w.frame W).slotCount g)) →
      (w.frame W).rightBasis ⟨g, i⟩ =
        w.rightBasis ⟨gateLocationsFrameEquiv W w g, Fin.cast (slotCount_frame W w g) i⟩
  | _, _, _, _, PartyCircuit.done _, g, _ => Empty.elim g
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, g, _ => Empty.elim g
  | _, _, _, _, PartyCircuit.localOps _, g, _ => Empty.elim g
  | _, _, _, _, PartyCircuit.comp c c', g, i => match g, i with
    | Sum.inl g, i => rightBasis_frame c g i
    | Sum.inr g, i => rightBasis_frame c' g i

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Framing keeps the dimensions at every source position. -/
theorem sourceDims_frame [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (w : SourceCircuit X Y)
    (g : (w.frame W).gateLocations) (i : Fin ((w.frame W).slotCount g)) :
    (w.frame W).sourceDims ⟨g, i⟩ =
      w.sourceDims ⟨gateLocationsFrameEquiv W w g, Fin.cast (slotCount_frame W w g) i⟩ :=
  Prod.ext (@Fintype.card_congr' _ _ (instFintypeLeftBasis _ _) (instFintypeLeftBasis _ _)
      (leftBasis_frame W w g i))
    (@Fintype.card_congr' _ _ (instFintypeRightBasis _ _) (instFintypeRightBasis _ _)
      (rightBasis_frame W w g i))

end Frame

end SourceCircuit

end QuantumCircuit.Party
