/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.PartyCircuit

/-!
# Party circuits using a set of parties

A party circuit uses only the parties of a set `R` when its gates act on cells inside `R`, its
local operations act at parties of `R`, and its local operations at every party are the
identification of equal bases outside `R` (`PartyCircuit.UsesOnly`). The predicate is a
structural recursion on the syntax, for every gate family, so its rules on the five
constructors hold by `rfl`. Such a circuit changes no basis outside `R`
(`PartyCircuit.UsesOnly.eq_of_notMem`).

## Main definitions

* `QuantumCircuit.Party.PartyCircuit.UsesOnly`.

## Main results

* `QuantumCircuit.Party.PartyCircuit.UsesOnly.mono`,
  `QuantumCircuit.Party.PartyCircuit.UsesOnly.eq_of_notMem`,
  `QuantumCircuit.Party.PartyCircuit.UsesOnly.forallGate_subset`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 23–35.
-/

namespace QuantumCircuit.Party

variable {P : Type}

namespace PartyCircuit

variable {G : Finset P → (P → Type) → (P → Type) → Type 1}

open Classical in
/-- A party circuit uses only the parties of `R`: its gates act on cells inside `R`, its local
operations act at parties of `R`, and its local operations at every party are the identification
of equal bases outside `R`. Source: `04-compression.tex`, lines 23–35. -/
def UsesOnly (R : Set P) : {X Y : P → Type} → PartyCircuit G X Y → Prop
  | _, _, done _ => True
  | _, _, gate D _ _ => (D : Set P) ⊆ R
  | _, _, localOp p _ _ => p ∈ R
  | X, Y, localOps A =>
    ∀ p ∉ R, ∃ h : Y p = X p, ∀ y x, A p y x = if cast h y = x then 1 else 0
  | _, _, comp c c' => UsesOnly R c ∧ UsesOnly R c'

/-- A circuit using only the parties of `R` uses only those of a larger set. -/
theorem UsesOnly.mono {R R' : Set P} (h : R ⊆ R') : {X Y : P → Type} →
    {c : PartyCircuit G X Y} → c.UsesOnly R → c.UsesOnly R'
  | _, _, done _, _ => trivial
  | _, _, gate _ _ _, hc => hc.trans h
  | _, _, localOp _ _ _, hc => h hc
  | _, _, localOps _, hc => fun p hp ↦ hc p fun hR ↦ hp (h hR)
  | _, _, comp _ _, hc => ⟨UsesOnly.mono h hc.1, UsesOnly.mono h hc.2⟩

/-- A circuit using only the parties of `R` changes no basis outside `R`. -/
theorem UsesOnly.eq_of_notMem {R : Set P} : {X Y : P → Type} → {c : PartyCircuit G X Y} →
    c.UsesOnly R → ∀ s ∉ R, Y s = X s
  | _, _, done _, _ => fun _ _ ↦ rfl
  | _, _, @gate _ _ _ _ _ _ _ hY _, h => fun s hs ↦ hY s fun hD ↦ hs (h hD)
  | _, _, @localOp _ _ _ _ _ _ _ hY _, h => fun s hs ↦ hY s fun e ↦ hs (e ▸ h)
  | _, _, @localOps _ _ _ _ _ _ _, h => fun s hs ↦ (h s hs).1
  | _, _, @comp _ _ _ _ _ _ _ _ _, h => fun s hs ↦
    (h.2.eq_of_notMem s hs).trans (h.1.eq_of_notMem s hs)

/-- The gates of a circuit using only the parties of `R` act on cells inside `R`. -/
theorem UsesOnly.forallGate_subset {R : Set P} : {X Y : P → Type} → {c : PartyCircuit G X Y} →
    c.UsesOnly R → c.ForallGate fun D _ _ _ ↦ (↑D : Set P) ⊆ R
  | _, _, done _, _ => trivial
  | _, _, gate _ _ _, h => h
  | _, _, localOp _ _ _, _ => trivial
  | _, _, localOps _, _ => trivial
  | _, _, comp _ _, h => ⟨forallGate_subset h.1, forallGate_subset h.2⟩

end PartyCircuit

end QuantumCircuit.Party
