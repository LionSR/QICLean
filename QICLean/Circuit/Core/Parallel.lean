/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Seq

/-!
# Layers of several gates, and adjoints

A layer of gates on a finite set of pairwise disjoint cells with the identity elsewhere is the
parallel application of the gates. For plain gates of one operator each, its single Kraus
operator is the product, in any order, of the placements of the gates, and it costs as much as
its cells; its depth is `1` when one of its cells has positive cost.

The adjoint of a Kraus family is the family of the adjoint operators. The adjoint of a sequence
of layers of plain gates is the sequence of the adjoint layers in reverse order; for layers of
one operator each its Kraus operator is the adjoint of the original one, and it has the same
costs.

## Main definitions

* `QuantumCircuit.Layer.ofCells` — gates on disjoint cells, the identity elsewhere.
* `KrausFamily.adjoint`, `QuantumCircuit.Layer.adjoint`, `QuantumCircuit.Circuit.seqAdjoint`.

## Main results

* `QuantumCircuit.Layer.kraus_ofCells`, `QuantumCircuit.Layer.gateCount_ofCells`,
  `QuantumCircuit.Layer.depth_ofCells`.
* `QuantumCircuit.Circuit.kraus_seqAdjoint`, `QuantumCircuit.Circuit.total_seqAdjoint`.
-/

open Matrix ManyBody

/-- The adjoint of a Kraus family: the adjoints of its operators. -/
def KrausFamily.adjoint {α β : Type} (K : KrausFamily α β) : KrausFamily β α :=
  ⟨K.Index, fun i ↦ (K.op i)ᴴ⟩

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

namespace Layer

variable {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The gates `g b` on the pairwise disjoint cells `b ∈ cells`, with the identity elsewhere. -/
def ofCells (cells : Finset Γ.Cell) (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell)
    (g : (b : Γ.Cell) → G (Γ.cell b) X X) : Layer Γ G X X where
  cells := cells
  pairwiseDisjoint := h
  gate b := g b
  onsite _ := KrausFamily.single 1

/-- The single Kraus operator of a layer of plain gates `V b` on disjoint cells is the product
of their placements, in the order of any enumeration of the cells. -/
theorem kraus_ofCells (cells : Finset Γ.Cell) (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell)
    (V : (b : Γ.Cell) → Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ)
    (l : List Γ.Cell) (hl : l.Nodup) (hcells : l.toFinset = cells)
    (i : (ofCells (G := KrausGate) cells h fun b ↦ KrausFamily.single (V b)).Index) :
    (ofCells (G := KrausGate) cells h fun b ↦ KrausFamily.single (V b)).kraus KrausGate.ev i =
      (l.map fun b ↦ place (Γ.cell b) (V b)).prod :=
  sorry

omit [Fintype S] [GateFamily G] [∀ s, Fintype (X s)] in
theorem gateCount_ofCells (cells : Finset Γ.Cell)
    (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell) (g : (b : Γ.Cell) → G (Γ.cell b) X X) :
    (ofCells cells h g).gateCount = ∑ b ∈ cells, Γ.cost b :=
  rfl

omit [Fintype S] [GateFamily G] [∀ s, Fintype (X s)] in
theorem depth_ofCells_le_one (cells : Finset Γ.Cell)
    (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell) (g : (b : Γ.Cell) → G (Γ.cell b) X X) :
    (ofCells cells h g).depth ≤ 1 := by
  unfold depth; split_ifs <;> omega

theorem nonempty_index_ofCells (cells : Finset Γ.Cell)
    (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell) (g : (b : Γ.Cell) → G (Γ.cell b) X X)
    (hg : ∀ b, Nonempty (GateFamily.Outcome (g b))) : Nonempty (ofCells cells h g).Index :=
  ⟨(fun b ↦ Classical.choice (hg b), fun _ ↦ ())⟩

/-- The adjoint of a layer of plain gates: the adjoint gates and onsite families. -/
def adjoint {Y : S → Type} (L : Layer Γ KrausGate X Y) : Layer Γ KrausGate Y X where
  cells := L.cells
  pairwiseDisjoint := L.pairwiseDisjoint
  gate b := (L.gate b).adjoint
  onsite s := (L.onsite s).adjoint

/-- The Kraus operators of the adjoint layer are the adjoints of those of the layer. -/
theorem kraus_adjoint {Y : S → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (L : Layer Γ KrausGate X Y) (i : L.Index) :
    L.adjoint.kraus KrausGate.ev i = (L.kraus KrausGate.ev i)ᴴ :=
  sorry

end Layer

namespace Circuit

variable {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The adjoint of a sequence of layers of plain gates: the adjoint layers in reverse order. -/
def seqAdjoint (Ls : List (Layer Γ KrausGate X X)) : Circuit Γ KrausGate X X :=
  seq (Ls.reverse.map Layer.adjoint)

/-- For layers of one operator each, the Kraus operator of the adjoint sequence is the adjoint of
the Kraus operator of the sequence. -/
theorem kraus_seqAdjoint (Ls : List (Layer Γ KrausGate X X))
    (U : Layer Γ KrausGate X X → Matrix (Config X) (Config X) ℂ)
    (hU : ∀ L ∈ Ls, ∀ i, L.kraus KrausGate.ev i = U L) (p : (seqAdjoint Ls).Index) :
    (seqAdjoint Ls).kraus KrausGate.ev p = ((Ls.map U).reverse.prod)ᴴ :=
  sorry

/-- The adjoint sequence has the costs of the sequence, for every cost depending only on the
cells of the layers. -/
theorem total_seqAdjoint (f : ∀ ⦃X Y : S → Type⦄, Layer Γ KrausGate X Y → ℕ)
    (hf : ∀ ⦃X Y : S → Type⦄ (L : Layer Γ KrausGate X Y), f L.adjoint = f L)
    (Ls : List (Layer Γ KrausGate X X)) (hne : ∀ L ∈ Ls, Nonempty L.Index) :
    (seqAdjoint Ls).total f = (seq Ls).total f :=
  sorry

end Circuit

end QuantumCircuit
