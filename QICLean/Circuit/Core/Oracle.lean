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

end QuantumCircuit
