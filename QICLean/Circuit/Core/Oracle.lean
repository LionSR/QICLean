/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.GateSum

/-!
# Oracle calls and their number

An oracle is a matrix `V` on a basis `β` that a circuit may apply but not inspect. A call to it
on a region `D` identifies the configurations of `D` with `β` and applies `V` there. The gates of
a circuit with oracle calls are those of the sum `GateSum G (Oracle β)`, where `G` holds the
other gates. The circuit does not depend on `V`: only its interpretation `Oracle.ev V` does, so
a statement about every oracle is a statement about one circuit under every interpretation. The
number of calls, along the branch with most calls, is a cost like the gate count; it counts the
calls and not their cells (`Layer.cellCost`).

## Main definitions

* `QuantumCircuit.Oracle` — calls to an oracle on the basis `β`.
* `QuantumCircuit.Oracle.ev` — their interpretation by a matrix.
* `QuantumCircuit.Circuit.queryCount` — the number of calls of a circuit.
* `QuantumCircuit.Circuit.NoCalls` — no layer of a circuit calls the oracle.

## Main results

* `QuantumCircuit.Circuit.queryCount_eq_zero` — a circuit with no calls in its layers makes none.
* `QuantumCircuit.Circuit.noCalls_mapGate_inl` — a circuit of plain gates, included into the sum,
  makes no calls.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} {β : Type}

/-- Calls to an oracle on the basis `β`: a call on the region `D` identifies the configurations
of `D` with `β`, and leaves the system unchanged. -/
inductive Oracle (β : Type) : Finset S → (S → Type) → (S → Type) → Type 1
  /-- The call on `D` along the identification `e`. -/
  | call {D : Finset S} {X : S → Type} (e : RegionConfig X D ≃ β) : Oracle β D X X

/-- A call has one outcome. -/
instance : GateFamily (S := S) (Oracle β) where
  Outcome _ := Unit
  fintype _ := inferInstanceAs (Fintype Unit)

/-- The interpretation of the calls by the matrix `V`, transported to each region along its
identification with `β`. -/
def Oracle.ev (V : Matrix β β ℂ) : Interpretation (S := S) (Oracle β)
  | _, _, _, _, _, _, _, .call e => fun _ ↦ V.submatrix e e

variable {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

/-- The number of oracle calls of a gate: one for a call, none for any other gate. -/
def Oracle.callCount : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, GateSum G (Oracle β) D X Y → ℕ
  | _, _, _, .inl _ => 0
  | _, _, _, .inr _ => 1

variable [Fintype S] [DecidableEq S] {Γ : Geometry S}

/-- The number of oracle calls of a circuit, along the branch with most calls. -/
def Circuit.queryCount {X Z : S → Type} (c : Circuit Γ (GateSum G (Oracle β)) X Z) : ℕ :=
  c.total fun _ _ L ↦ L.cellCost fun _ _ _ g ↦ Oracle.callCount g

namespace Circuit

/-- No layer of the circuit calls the oracle. -/
def NoCalls : {X Z : S → Type} → Circuit Γ (GateSum G (Oracle β)) X Z → Prop
  | _, _, done _ => True
  | _, _, step L next => L.cellCost (fun _ _ _ g ↦ Oracle.callCount g) = 0 ∧ ∀ i, (next i).NoCalls

/-- A circuit with no calls in its layers makes no calls. -/
theorem queryCount_eq_zero : {X Z : S → Type} → {c : Circuit Γ (GateSum G (Oracle β)) X Z} →
    c.NoCalls → c.queryCount = 0
  | _, _, done _, _ => rfl
  | _, _, step L next, h => by
    change L.cellCost _ + Finset.univ.sup (fun i ↦ (next i).queryCount) = 0
    rw [h.1, zero_add]
    exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ ↦ (queryCount_eq_zero (h.2 i)).le)

omit [Fintype S] in
/-- A circuit of plain gates, moved into the sum with the oracle calls, makes no calls. -/
theorem noCalls_mapGate_inl {Δ : Geometry S} (h : Γ.Hom Δ (Function.Embedding.refl S)) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G X Z) → (c.mapGate h (GateMorphism.inl (G₂ := Oracle β))).NoCalls
  | _, _, _, _, done _ => by simp only [mapGate, mapLayers, NoCalls]
  | _, _, _, _, step L next => by
    change (L.mapGate h _).cellCost _ = 0 ∧ ∀ i, ((next _).mapGate h _).NoCalls
    exact ⟨(L.cellCost_mapGate h _ _).trans (Finset.sum_eq_zero fun _ _ ↦ rfl),
      fun _ ↦ noCalls_mapGate_inl h _⟩

end Circuit

end QuantumCircuit
