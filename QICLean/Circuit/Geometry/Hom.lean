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
* `QuantumCircuit.Geometry.restrictHom` — the cells inside a region are cells of the geometry.
* `QuantumCircuit.Geometry.Hom.toRestrict` — a morphism into a geometry over a map of sites into
  a region, as a morphism into the cells inside the region.

## Main results

* `QuantumCircuit.Geometry.Hom.biUnion_map` — the sites of the image of a set of cells.
* `QuantumCircuit.Geometry.Hom.pairwiseDisjoint_map` — images of disjoint cells are disjoint.
* `QuantumCircuit.Geometry.Blocking`: blockings of geometries.
-/

namespace QuantumCircuit

section Hom

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

/-- The cells inside the region `D`, as a geometry on the sites of `D`, are cells of `Γ`. -/
def Geometry.restrictHom [DecidableEq S] (Γ : Geometry S) (D : Finset S) :
    (Γ.restrict D).Hom Γ (Function.Embedding.subtype (· ∈ D)) where
  cellMap := Function.Embedding.subtype _
  cell_cellMap b := (Finset.subtype_map_of_mem fun _ hv ↦ b.2 hv).symm

/-- A morphism of geometries into `Γ` over a map of sites into the region `D` is a morphism into
the cells inside `D`. -/
def Geometry.Hom.toRestrict {T : Type} [DecidableEq S] {Δ : Geometry T} {D : Finset S}
    {ι : T ↪ {s // s ∈ D}}
    (h : Δ.Hom Γ (ι.trans (Function.Embedding.subtype _))) : Δ.Hom (Γ.restrict D) ι where
  cellMap := ⟨fun b ↦ ⟨h.cellMap b, fun v hv ↦ by
      rw [h.cell_cellMap] at hv
      obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hv
      exact (ι t).2⟩,
    fun _ _ hbb' ↦ h.cellMap.injective (congrArg Subtype.val hbb')⟩
  cell_cellMap b := by
    ext w
    simp only [Geometry.restrict, Finset.mem_subtype, Finset.mem_map, Subtype.ext_iff]
    change w.1 ∈ Γ.cell (h.cellMap b) ↔ _
    rw [h.cell_cellMap]
    simp only [Finset.mem_map, Function.Embedding.trans_apply, Function.Embedding.coe_subtype]

end Hom

end Hom

section Block

/-!
## Blockings of geometries

A map of sites `f : S → S'` groups the sites of a geometry `Γ` into blocks, the sites of a
geometry `Γ'`. A blocking of `Γ` into `Γ'` along `f` with `r` colours sends every cell of `Γ`
to a cell of `Γ'` containing its image, and colours the cells of `Γ'` with `r` colours so that
distinct cells of one colour are disjoint. A layer on `Γ` is then a sequence of `r` layers on
`Γ'`, one for each colour (`QuantumCircuit.IsProtocol.block`).

A blocking is formalization-side: it is the hypothesis under which a protocol on a geometry is a
protocol on its blocks. The ring of `M * k` sites is blocked into the ring of `M` blocks of `k`
consecutive sites with two colours for `M` even and three for `M` odd
(`QuantumCircuit.Geometry.ringBlocking`).

### Main definitions

* `QuantumCircuit.Geometry.Blocking` — a blocking of one geometry into another.
-/

namespace Geometry

variable {S S' : Type} [DecidableEq S']

/-- A blocking of the geometry `Γ` into the geometry `Γ'` along the map of sites `f`, with `r`
colours: every cell `b` of `Γ` is covered by a cell `cover b` of `Γ'` containing its image, the
cells of `Γ'` are coloured so that distinct cells of one colour are disjoint, and the cells of
`Γ` have positive cost.

The cells of one colour can therefore carry gates in one layer on `Γ'`, and a layer on `Γ` is
realised by one layer on `Γ'` for each colour. Positivity of the costs of `Γ` is what the depth
`r` of these layers is charged against: a layer on `Γ` using a cell has depth one, while a layer
using no cell has depth zero and is realised in depth zero.

This structure is formalization-side; the source blocks a chain into consecutive sites
(arXiv:2103.13367v3, `main.tex`, lines 287–289), which is `Geometry.ringBlocking`. -/
structure Blocking (Γ : Geometry S) (Γ' : Geometry S') (f : S → S') (r : ℕ) where
  /-- The cell of `Γ'` covering a cell of `Γ`. -/
  cover : Γ.Cell → Γ'.Cell
  /-- A cell of `Γ` lies, after `f`, in its covering cell. -/
  image_subset : ∀ b, (Γ.cell b).image f ⊆ Γ'.cell (cover b)
  /-- The colour of a cell of `Γ'`. -/
  colour : Γ'.Cell → Fin r
  /-- Distinct cells of one colour are disjoint. -/
  disjoint : ∀ c₁ c₂, colour c₁ = colour c₂ → c₁ ≠ c₂ → Disjoint (Γ'.cell c₁) (Γ'.cell c₂)
  /-- The cells of `Γ` have positive cost. -/
  cost_pos : ∀ b, 0 < Γ.cost b

end Geometry

end Block

end QuantumCircuit
