/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Geometry.Basic

/-!
# Morphisms of geometries

A morphism of geometries over an injective map of sites `ι : S ↪ S'` is an injective map of cells
carrying the sites of each cell to the image of its sites; costs are compared separately. Circuits
move along such morphisms (`Circuit/Core/Map.lean`).

## Main definitions

* `QuantumCircuit.Geometry.Hom` — a morphism of geometries over a map of sites.
* `QuantumCircuit.Geometry.Hom.refl` — the identity morphism.

## Main results

* `QuantumCircuit.Geometry.Hom.biUnion_map` — the sites of the image of a set of cells.
* `QuantumCircuit.Geometry.Hom.pairwiseDisjoint_map` — images of disjoint cells are disjoint.
-/

namespace QuantumCircuit

section Hom

variable {S S' : Type} {Γ : Geometry S} {Γ' : Geometry S'} {ι : S ↪ S'}

/-- A morphism of geometries over the map of sites `ι`: an injective map of cells carrying the
sites of a cell to the sites of its image. Costs are compared separately. -/
structure Geometry.Hom (Γ : Geometry S) (Γ' : Geometry S') (ι : S ↪ S') where
  /-- The map of cells. -/
  cellMap : Γ.Cell ↪ Γ'.Cell
  /-- The sites of the image of a cell. -/
  cell_cellMap : ∀ b, Γ'.cell (cellMap b) = (Γ.cell b).map ι

/-- The identity morphism of a geometry. -/
def Geometry.Hom.refl (Γ : Geometry S) : Γ.Hom Γ (Function.Embedding.refl S) where
  cellMap := Function.Embedding.refl _
  cell_cellMap _ := Finset.map_refl.symm

/-- The sites of the image of a set of cells are the image of its sites. -/
theorem Geometry.Hom.biUnion_map [DecidableEq S] [DecidableEq S'] (h : Γ.Hom Γ' ι)
    (s : Finset Γ.Cell) :
    (s.map h.cellMap).biUnion Γ'.cell = (s.biUnion Γ.cell).map ι := by
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_map]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, hv⟩
    rw [h.cell_cellMap] at hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hv
    exact ⟨t, ⟨b, hb, ht⟩, rfl⟩
  · rintro ⟨t, ⟨b, hb, ht⟩, rfl⟩
    exact ⟨h.cellMap b, ⟨b, hb, rfl⟩, by rw [h.cell_cellMap]; exact Finset.mem_map_of_mem _ ht⟩

/-- The images of pairwise disjoint cells are pairwise disjoint. -/
theorem Geometry.Hom.pairwiseDisjoint_map (h : Γ.Hom Γ' ι) {s : Finset Γ.Cell}
    (hs : (s : Set Γ.Cell).PairwiseDisjoint Γ.cell) :
    ((s.map h.cellMap : Finset Γ'.Cell) : Set Γ'.Cell).PairwiseDisjoint Γ'.cell := by
  intro b₁ hb₁ b₂ hb₂ hne
  obtain ⟨c₁, hc₁, rfl⟩ := Finset.mem_map.mp hb₁
  obtain ⟨c₂, hc₂, rfl⟩ := Finset.mem_map.mp hb₂
  simp only [Function.onFun, h.cell_cellMap, Finset.disjoint_map]
  exact hs hc₁ hc₂ fun hc ↦ hne (congrArg _ hc)

end Hom

end QuantumCircuit
