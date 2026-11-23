/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Coarsen
import QICLean.Circuit.Geometry.Subsets

/-!
# Coarsening a circuit along blocks of sites

Let a map of sites `f : S → S'` group the sites of a geometry `Γ` into blocks, the sites of a
geometry `Γ'`. A circuit of plain gates on `Γ` whose every layer has its cells covered, after `f`,
by pairwise disjoint cells `cover b` of `Γ'` (`Circuit.Coarsenable`) is, read on the blocked
systems, a circuit on `Γ'` (`Circuit.coarsen`): each layer is replaced by its coarse layer
`Layer.coarsen`, and the continuation after an outcome of the coarse layer is the coarsened
continuation after the corresponding outcome of the layer. The branches of the two circuits
correspond (`Circuit.coarsenIndexEquiv`), and the Kraus operator of a branch of the coarse circuit
is that of the corresponding branch, read on the blocks (`Circuit.kraus_coarsen`).

A circuit whose layers have at most one cell each is coarsenable onto the geometry of all finite
sets of blocks, each cell covered by its image (`Circuit.coarsenable_of_atMostOneCell`).

The gates are plain Kraus families: the coarse gate on a covering cell is the product of several
gates and onsite families, which a general gate family need not contain.

## Main definitions

* `QuantumCircuit.Circuit.Coarsenable` — every layer has disjoint covering cells.
* `QuantumCircuit.Circuit.coarsen` — the circuit read on the blocks.
* `QuantumCircuit.Circuit.coarsenIndexEquiv` — its branches are those of the circuit.
* `QuantumCircuit.Circuit.AtMostOneCell` — every layer uses at most one cell.

## Main results

* `QuantumCircuit.Circuit.kraus_coarsen` — the Kraus operators of the coarse circuit.
* `QuantumCircuit.Circuit.coarsenable_of_atMostOneCell` — circuits of one gate per layer are
  coarsenable onto the geometry of all finite sets.
-/

open Matrix ManyBody

namespace QuantumCircuit

namespace Circuit

variable {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']
  {Γ : Geometry S} {Γ' : Geometry S'}

/-- Every layer of the circuit, on every branch, has each of its cells `b` covered, after `f`, by
the cell `cover b`, distinct covering cells being disjoint. -/
def Coarsenable (f : S → S') (cover : Γ.Cell → Γ'.Cell) :
    {X Z : S → Type} → Circuit Γ KrausGate X Z → Prop
  | _, _, done _ => True
  | _, _, step L next =>
      ((∀ b ∈ L.cells, (Γ.cell b).image f ⊆ Γ'.cell (cover b)) ∧
        ∀ b₁ ∈ L.cells, ∀ b₂ ∈ L.cells, cover b₁ ≠ cover b₂ →
          Disjoint (Γ'.cell (cover b₁)) (Γ'.cell (cover b₂))) ∧
      ∀ i, (next i).Coarsenable f cover

/-- The circuit read on the blocks of `f`: every layer replaced by its coarse layer. -/
noncomputable def coarsen (f : S → S') (cover : Γ.Cell → Γ'.Cell) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ KrausGate X Z) → c.Coarsenable f cover →
        Circuit Γ' KrausGate (blockSystem f X) (blockSystem f Z)
  | _, _, _, _, done _, _ => done _
  | _, _, _, _, step L next, h =>
      step (Layer.coarsen f cover L h.1.1 h.1.2) fun i' ↦
        (next (Layer.coarsenIndexEquiv f cover L h.1.1 h.1.2 i')).coarsen f cover (h.2 _)

/-- The branches of the coarse circuit are those of the circuit. -/
noncomputable def coarsenIndexEquiv (f : S → S') (cover : Γ.Cell → Γ'.Cell) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ KrausGate X Z) → (h : c.Coarsenable f cover) →
        (c.coarsen f cover h).Index ≃ c.Index
  | _, _, _, _, done _, _ => Equiv.refl Unit
  | _, _, _, _, step L next, h =>
      Equiv.sigmaCongr (Layer.coarsenIndexEquiv f cover L h.1.1 h.1.2) fun i' ↦
        (next (Layer.coarsenIndexEquiv f cover L h.1.1 h.1.2 i')).coarsenIndexEquiv f cover
          (h.2 _)

/-- **Coarsening a circuit.** The Kraus operator of a branch of the coarse circuit is the Kraus
operator of the corresponding branch of the circuit, read on the blocks. -/
theorem kraus_coarsen (f : S → S') (cover : Γ.Cell → Γ'.Cell) {Z : S → Type} :
    {X : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ KrausGate X Z) → (h : c.Coarsenable f cover) →
        (p : (c.coarsen f cover h).Index) →
          (c.coarsen f cover h).kraus KrausGate.ev p =
            (c.kraus KrausGate.ev (c.coarsenIndexEquiv f cover h p)).submatrix
              (blockConfigEquiv f Z) (blockConfigEquiv f X)
  | _, _, _, done _, _, _ => (submatrix_one_equiv _).symm
  | _, _, _, step L next, h, p => by
    change (coarsen f cover (next (Layer.coarsenIndexEquiv f cover L h.1.1 h.1.2 p.1))
        (h.2 _)).kraus KrausGate.ev p.2 * (Layer.coarsen f cover L h.1.1 h.1.2).kraus
          KrausGate.ev p.1 = _
    rw [kraus_coarsen f cover _ (h.2 _) p.2, Layer.kraus_coarsen, submatrix_mul_equiv]
    rfl

/-- Every layer of the circuit, on every branch, uses at most one cell. -/
def AtMostOneCell : {X Z : S → Type} → Circuit Γ KrausGate X Z → Prop
  | _, _, done _ => True
  | _, _, step L next => L.cells.card ≤ 1 ∧ ∀ i, (next i).AtMostOneCell

omit [Fintype S] [Fintype S'] in
/-- A circuit whose layers use at most one cell each is coarsenable onto the geometry of all
finite sets of blocks, each cell covered by its image. -/
theorem coarsenable_of_atMostOneCell (f : S → S') : {X Z : S → Type} →
    (c : Circuit Γ KrausGate X Z) → c.AtMostOneCell →
      c.Coarsenable (Γ' := Geometry.subsets S') f fun b ↦ (Γ.cell b).image f
  | _, _, done _, _ => trivial
  | _, _, step L next, h =>
    ⟨⟨fun _ _ ↦ subset_rfl, fun b₁ hb₁ b₂ hb₂ hne ↦
        absurd (by rw [Finset.card_le_one.mp h.1 b₁ hb₁ b₂ hb₂]) hne⟩,
      fun i ↦ coarsenable_of_atMostOneCell f (next i) (h.2 i)⟩

end Circuit

end QuantumCircuit
