/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Map

/-!
# Sums of gate families

A circuit may mix gates of two families, such as plain gates and calls to an oracle. The sum of
two gate families has the gates of both, with their outcomes, and an interpretation of each
family gives one of the sum. A circuit of either family moves into the sum along the inclusion
of gates, a morphism of gate families on the same sites compatible with the interpretations.

## Main definitions

* `QuantumCircuit.GateSum` — the sum of two gate families.
* `QuantumCircuit.Interpretation.sum` — the interpretation of a sum.
* `QuantumCircuit.GateMorphism.inl` — the inclusion of the first family.
* `QuantumCircuit.Geometry.Hom.refl` — the identity morphism of a geometry.

## Main results

* `QuantumCircuit.GateMorphism.isCompatible_inl` — the inclusion keeps the matrices.
-/

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

/-- The identity morphism of a geometry. -/
def Geometry.Hom.refl (Γ : Geometry S) : Γ.Hom Γ (Function.Embedding.refl S) where
  cellMap := Function.Embedding.refl _
  cell_cellMap _ := Finset.map_refl.symm

/-- The inclusion of the gates of the first family into the sum. -/
def GateMorphism.inl : GateMorphism G₁ (GateSum G₁ G₂) where
  map _ _ _ g := .inl g
  outcome _ _ _ _ := Equiv.refl _

theorem GateMorphism.isCompatible_inl (ev₁ : Interpretation G₁) (ev₂ : Interpretation G₂) :
    (GateMorphism.inl (G₂ := G₂)).IsCompatible ev₁ (ev₁.sum ev₂) :=
  fun _ _ _ _ _ _ _ _ _ ↦ rfl

end QuantumCircuit
