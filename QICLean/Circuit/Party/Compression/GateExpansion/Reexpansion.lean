/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Original.Approximation

/-!
# Changing the gate expansions of a fixed chronology

An effect circuit fixes a chronology: its local operations, its gates with their cells, and the
order of composition. A gate map is assigned to each gate occurrence (`EffectCircuit.GateMaps`).
New gate expansions may be chosen independently at the same occurrences (`GateLists`): the
reexpanded circuit `reexpand` has the same local operations and the same cells, only the
weighted lists of monomials change. The circuit of the gate maps is therefore unchanged
(`evalWithGateMaps_reexpand`), the gate occurrences correspond one to one
(`reexpandLocationsEquiv`) with the same cells, and the number of gates and the participation
counts of all parties are unchanged.

No assumption on the original expansions is needed: they need be neither exact nor allowed.

`PartyCircuit.mapGates` does not give the reexpansion: a gate morphism replaces every gate by a
function of the gate alone, while here the new expansion is chosen per occurrence.

## Main definitions

* `QuantumCircuit.Party.EffectCircuit.GateLists`, `reexpand`, `reexpandGateMaps`,
  `reexpandLocationsEquiv`.

## Main results

* `QuantumCircuit.Party.EffectCircuit.evalWithGateMaps_reexpand`.
* `QuantumCircuit.Party.EffectCircuit.participants_reexpand`, `gateCells_reexpand`,
  `numGates_reexpand`, `participationCount_reexpand`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 21–30, 53–57, 137–142, 199–202 and 590–598.
-/

noncomputable section

open Matrix ManyBody

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace EffectCircuit

/-- One gate expansion on the cell of each gate occurrence, with the input and output systems of
the occurrence. Composition keeps distinct occurrences separate. Source: Theorem 5.2,
`04-compression.tex`, lines 53–57 and 590–598. -/
@[reducible] def GateLists : {X Y : P → Type} → EffectCircuit X Y → Type 1
  | _, _, PartyCircuit.done _ => PUnit
  | X, Y, PartyCircuit.gate D _ _ => WeightedGate D X Y
  | _, _, PartyCircuit.localOp _ _ _ => PUnit
  | _, _, PartyCircuit.localOps _ => PUnit
  | _, _, PartyCircuit.comp c c' => GateLists c × GateLists c'

/-- Replace the gate expansion at each gate occurrence, keeping the local operations, the cells
and the composition. Source: Theorem 5.2, `04-compression.tex`, lines 590–598. -/
def reexpand : {X Y : P → Type} → (c : EffectCircuit X Y) → c.GateLists → EffectCircuit X Y
  | _, _, PartyCircuit.done X, _ => PartyCircuit.done X
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY _, l => PartyCircuit.gate D hY l
  | _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A, _ => PartyCircuit.localOp p hY A
  | _, _, @PartyCircuit.localOps _ _ _ _ _ _ A, _ => PartyCircuit.localOps A
  | _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', l =>
    PartyCircuit.comp (reexpand c l.1) (reexpand c' l.2)

/-- The same gate maps on the reexpanded chronology. Source: Theorem 5.2, `04-compression.tex`,
lines 590–598. -/
def reexpandGateMaps : {X Y : P → Type} → (c : EffectCircuit X Y) → (lists : c.GateLists) →
    c.GateMaps → (c.reexpand lists).GateMaps
  | _, _, PartyCircuit.done _, _, _ => PUnit.unit
  | _, _, PartyCircuit.gate _ _ _, _, G => G
  | _, _, PartyCircuit.localOp _ _ _, _, _ => PUnit.unit
  | _, _, PartyCircuit.localOps _, _, _ => PUnit.unit
  | _, _, PartyCircuit.comp c c', lists, G =>
    (reexpandGateMaps c lists.1 G.1, reexpandGateMaps c' lists.2 G.2)

section Rules

variable {X Y Z : P → Type}

/-- The empty circuit is its own reexpansion. -/
@[simp] theorem reexpand_done (l : GateLists (PartyCircuit.done X : EffectCircuit X X)) :
    reexpand (PartyCircuit.done X) l = PartyCircuit.done X :=
  rfl

variable [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- One gate is replaced by the new expansion on the same cell. -/
@[simp] theorem reexpand_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : WeightedGate D X Y)
    (l : WeightedGate D X Y) :
    reexpand (PartyCircuit.gate D hY g : EffectCircuit X Y) l = PartyCircuit.gate D hY l :=
  rfl

/-- A local operation is kept. -/
@[simp] theorem reexpand_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s) (A : Matrix (Y p) (X p) ℂ)
    (l : GateLists (PartyCircuit.localOp p hY A : EffectCircuit X Y)) :
    reexpand (PartyCircuit.localOp p hY A : EffectCircuit X Y) l = PartyCircuit.localOp p hY A :=
  rfl

/-- Local operations at every party are kept. -/
@[simp] theorem reexpand_localOps (A : ∀ p, Matrix (Y p) (X p) ℂ)
    (l : GateLists (PartyCircuit.localOps A : EffectCircuit X Y)) :
    reexpand (PartyCircuit.localOps A : EffectCircuit X Y) l = PartyCircuit.localOps A :=
  rfl

/-- A composition is reexpanded part by part. -/
@[simp] theorem reexpand_comp (c : EffectCircuit X Y) (c' : EffectCircuit Y Z)
    (l : GateLists (PartyCircuit.comp c c')) :
    reexpand (PartyCircuit.comp c c') l = PartyCircuit.comp (reexpand c l.1) (reexpand c' l.2) :=
  rfl

/-- The gate map of one gate is kept. -/
@[simp] theorem reexpandGateMaps_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : WeightedGate D X Y) (l : WeightedGate D X Y)
    (G : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    reexpandGateMaps (PartyCircuit.gate D hY g : EffectCircuit X Y) l G = G :=
  rfl

/-- The gate maps of a composition are carried part by part. -/
@[simp] theorem reexpandGateMaps_comp (c : EffectCircuit X Y) (c' : EffectCircuit Y Z)
    (l : GateLists (PartyCircuit.comp c c')) (G : GateMaps (PartyCircuit.comp c c')) :
    reexpandGateMaps (PartyCircuit.comp c c') l G =
      (reexpandGateMaps c l.1 G.1, reexpandGateMaps c' l.2 G.2) :=
  rfl

end Rules

/-- **The circuit of the gate maps does not depend on the gate expansions.** Source: Theorem 5.2,
`04-compression.tex`, lines 590–598. -/
theorem evalWithGateMaps_reexpand [Fintype P] : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) → (lists : c.GateLists) →
    (G : c.GateMaps) →
      (c.reexpand lists).evalWithGateMaps (c.reexpandGateMaps lists G) = c.evalWithGateMaps G
  | _, _, _, _, PartyCircuit.done _, _, _ => rfl
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _ => rfl
  | _, _, _, _, PartyCircuit.localOps _, _, _ => rfl
  | _, _, _, _, PartyCircuit.comp c c', lists, G =>
    congrArg₂ (· * ·) (evalWithGateMaps_reexpand c' lists.2 G.2)
      (evalWithGateMaps_reexpand c lists.1 G.1)

/-- The reexpansion keeps the gate occurrences. Source: Theorem 5.2, `04-compression.tex`,
lines 21–30 and 590–598. -/
def reexpandLocationsEquiv : {X Y : P → Type} → (c : EffectCircuit X Y) →
    (lists : c.GateLists) → (c.reexpand lists).gateLocations ≃ c.gateLocations
  | _, _, PartyCircuit.done _, _ => Equiv.refl _
  | _, _, PartyCircuit.gate _ _ _, _ => Equiv.refl _
  | _, _, PartyCircuit.localOp _ _ _, _ => Equiv.refl _
  | _, _, PartyCircuit.localOps _, _ => Equiv.refl _
  | _, _, PartyCircuit.comp c c', lists =>
    Equiv.sumCongr (reexpandLocationsEquiv c lists.1) (reexpandLocationsEquiv c' lists.2)

/-- The correspondence of occurrences keeps the cell of every occurrence. Source: Theorem 5.2,
`04-compression.tex`, lines 25–27 and 590–598. -/
theorem participants_reexpand : {X Y : P → Type} → (c : EffectCircuit X Y) →
    (lists : c.GateLists) → (g : (c.reexpand lists).gateLocations) →
      (c.reexpand lists).participants g = c.participants (c.reexpandLocationsEquiv lists g)
  | _, _, PartyCircuit.done _, _, g => g.elim
  | _, _, PartyCircuit.gate _ _ _, _, _ => rfl
  | _, _, PartyCircuit.localOp _ _ _, _, g => g.elim
  | _, _, PartyCircuit.localOps _, _, g => g.elim
  | _, _, PartyCircuit.comp c c', lists, g => by
    rcases g with g | g
    exacts [participants_reexpand c lists.1 g, participants_reexpand c' lists.2 g]

/-- The reexpansion has the cells of the circuit, in chronological order. Source: Theorem 5.2,
`04-compression.tex`, lines 25–27 and 590–598. -/
theorem gateCells_reexpand : {X Y : P → Type} → (c : EffectCircuit X Y) →
    (lists : c.GateLists) → (c.reexpand lists).gateCells = c.gateCells
  | _, _, PartyCircuit.done _, _ => rfl
  | _, _, PartyCircuit.gate _ _ _, _ => rfl
  | _, _, PartyCircuit.localOp _ _ _, _ => rfl
  | _, _, PartyCircuit.localOps _, _ => rfl
  | _, _, PartyCircuit.comp c c', lists =>
    congrArg₂ (· ++ ·) (gateCells_reexpand c lists.1) (gateCells_reexpand c' lists.2)

/-- The reexpansion neither adds nor removes gates, every gate counted. Source: Theorem 5.2,
`04-compression.tex`, lines 137, 199–202 and 590–598. -/
theorem numGates_reexpand : {X Y : P → Type} → (c : EffectCircuit X Y) →
    (lists : c.GateLists) → (c.reexpand lists).numGates = c.numGates
  | _, _, PartyCircuit.done _, _ => rfl
  | _, _, PartyCircuit.gate _ _ _, _ => rfl
  | _, _, PartyCircuit.localOp _ _ _, _ => rfl
  | _, _, PartyCircuit.localOps _, _ => rfl
  | _, _, PartyCircuit.comp c c', lists =>
    congrArg₂ (· + ·) (numGates_reexpand c lists.1) (numGates_reexpand c' lists.2)

/-- **Every party takes part in the same number of gates over the whole chronology**, one-party
gates included, whatever the new expansions. Source: Theorem 5.2, `04-compression.tex`,
lines 140–142 and 590–598. -/
theorem participationCount_reexpand {X Y : P → Type} (c : EffectCircuit X Y)
    (lists : c.GateLists) (p : P) :
    (c.reexpand lists).participationCount p = c.participationCount p := by
  rw [← PartyCircuit.natCard_participants_mem, ← PartyCircuit.natCard_participants_mem]
  exact Nat.card_congr ((c.reexpandLocationsEquiv lists).subtypeEquiv fun g ↦ by
    rw [c.participants_reexpand lists g])

end EffectCircuit

end QuantumCircuit.Party
