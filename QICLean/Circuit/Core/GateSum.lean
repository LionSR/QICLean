/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Cost

/-!
# Sums of gate families and costs of gates

A circuit may mix gates of two families, such as plain gates and calls to an oracle. The sum
of two gate families has the gates of both, with their outcomes; an interpretation of each
gives one of the sum. A weight of gates, such as the number of oracle calls a gate makes,
accumulates along the most expensive branch like every other cost; it depends on the gate and
not on its cell.

## Main definitions

* `QuantumCircuit.GateSum` — the sum of two gate families.
* `QuantumCircuit.Interpretation.sum` — the interpretation of a sum.
* `QuantumCircuit.Layer.gateCost`, `QuantumCircuit.Circuit.gateCost` — a weight of the gates.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type}

/-- The gates of two families. -/
def GateSum (G₁ G₂ : Finset S → (S → Type) → (S → Type) → Type 1) :
    Finset S → (S → Type) → (S → Type) → Type 1 :=
  fun D X Y ↦ G₁ D X Y ⊕ G₂ D X Y

variable {G₁ G₂ : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G₁] [GateFamily G₂]

instance : GateFamily (GateSum G₁ G₂) where
  Outcome
    | .inl g => GateFamily.Outcome g
    | .inr g => GateFamily.Outcome g
  fintype
    | .inl g => GateFamily.fintype g
    | .inr g => GateFamily.fintype g

/-- The interpretation of the sum of two gate families. -/
def Interpretation.sum (ev₁ : Interpretation G₁) (ev₂ : Interpretation G₂) :
    Interpretation (GateSum G₁ G₂)
  | _, _, _, _, _, _, _, .inl g => ev₁ g
  | _, _, _, _, _, _, _, .inr g => ev₂ g

variable [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

/-- The total weight of the gates of a layer. -/
def Layer.gateCost (w : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, G D X Y → ℕ) {X Y : S → Type}
    (L : Layer Γ G X Y) : ℕ :=
  ∑ b : L.cells, w (L.gate b)

/-- The total weight of the gates of a circuit, along the most expensive branch. -/
def Circuit.gateCost (w : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, G D X Y → ℕ) {X Z : S → Type}
    (c : Circuit Γ G X Z) : ℕ :=
  c.total fun _ _ L ↦ L.gateCost w

theorem Circuit.gateCost_comp (w : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, G D X Y → ℕ)
    {X Y Z : S → Type} (c : Circuit Γ G X Y) (c' : Circuit Γ G Y Z) :
    (c.comp c').gateCost w ≤ c.gateCost w + c'.gateCost w :=
  total_comp _ c c'

end QuantumCircuit
