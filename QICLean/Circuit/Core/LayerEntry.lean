/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Layer

/-!
# A layer cell by cell

Every site met by a cell of a layer lies in exactly one cell, since the cells are pairwise
disjoint (`Layer.cellOf`). A configuration of any system is therefore its restrictions to the
cells together with its values at the remaining sites (`Layer.configEquiv`).

The map of a layer is the tensor product of the maps of its gates and onsite families: on a
matrix unit `|x⟩⟨x'|` its entry at `(y, y')` is the product of the entries of the local maps on
the local matrix units (`Layer.map_single_apply`). Two layers with the same cells whose local
maps agree therefore have the same map.

## Main definitions

* `QuantumCircuit.Layer.cellOf` — the cell containing a site met by the layer.
* `QuantumCircuit.Layer.configEquiv` — a configuration as restrictions to the cells and values
  at the free sites.
* `QuantumCircuit.Layer.gateFamily` — the gate of a cell as a Kraus family.

## Main results

* `QuantumCircuit.Layer.cellOf_eq` — the cell containing a site is unique.
* `QuantumCircuit.Layer.map_single_apply` — the entries of the map of a layer on matrix units.
* `KrausFamily.map_single_apply` — the entries of the map of a Kraus family on matrix units.
-/

open Matrix ManyBody

namespace KrausFamily

/-- The entries of the map of a Kraus family on a matrix unit. -/
theorem map_single_apply {α β : Type} [Fintype α] [DecidableEq α]
    (K : KrausFamily α β) (a a' : α) (c c' : β) :
    K.map (Matrix.single a a' 1) c c' = ∑ i, K.op i c a * star (K.op i c' a') := by
  rw [map_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [mul_apply, Matrix.single_apply, ite_and]

end KrausFamily

namespace QuantumCircuit

namespace Layer

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {X Y : S → Type}

omit [Fintype S] [GateFamily G] in
private theorem exists_cell (L : Layer Γ G X Y) {s : S} (hs : s ∈ L.cells.biUnion Γ.cell) :
    ∃ b : L.cells, s ∈ Γ.cell b := by
  obtain ⟨b, hb, hsb⟩ := Finset.mem_biUnion.mp hs
  exact ⟨⟨b, hb⟩, hsb⟩

/-- The cell of the layer containing a site met by the layer. -/
noncomputable def cellOf (L : Layer Γ G X Y) {s : S} (hs : s ∈ L.cells.biUnion Γ.cell) :
    L.cells :=
  (L.exists_cell hs).choose

omit [Fintype S] [GateFamily G] in
theorem mem_cellOf (L : Layer Γ G X Y) {s : S} (hs : s ∈ L.cells.biUnion Γ.cell) :
    s ∈ Γ.cell (L.cellOf hs) :=
  (L.exists_cell hs).choose_spec

omit [Fintype S] [GateFamily G] in
/-- The cell containing a site is unique. -/
theorem cellOf_eq (L : Layer Γ G X Y) {s : S} (hs : s ∈ L.cells.biUnion Γ.cell) {b : L.cells}
    (hb : s ∈ Γ.cell b) : L.cellOf hs = b := by
  by_contra h
  exact Finset.disjoint_left.mp (L.pairwiseDisjoint (L.cellOf hs).2 b.2
    (fun e ↦ h (Subtype.ext e))) (L.mem_cellOf hs) hb

omit [Fintype S] [GateFamily G] in
private theorem apply_cellOf {F : S → Type} (L : Layer Γ G X Y)
    (p : (b : L.cells) → RegionConfig F (Γ.cell b)) (b : L.cells) (v : {v // v ∈ Γ.cell b})
    (hv : v.1 ∈ L.cells.biUnion Γ.cell) :
    p (L.cellOf hv) ⟨v, L.mem_cellOf hv⟩ = p b v := by
  have key : ∀ (c : L.cells) (hc : c = b) (hv' : v.1 ∈ Γ.cell c), p c ⟨v, hv'⟩ = p b v := by
    rintro c rfl _
    rfl
  exact key _ (L.cellOf_eq hv v.2) _

omit [Fintype S] [GateFamily G] in
theorem mem_biUnion_of_mem_cell (L : Layer Γ G X Y) (b : L.cells) {v : S}
    (hv : v ∈ Γ.cell b) : v ∈ L.cells.biUnion Γ.cell :=
  Finset.mem_biUnion.mpr ⟨b, b.2, hv⟩

/-- A configuration of a system `F` as its restrictions to the cells of the layer and its values
at the free sites. -/
noncomputable def configEquiv (L : Layer Γ G X Y) (F : S → Type) :
    Config F ≃ ((b : L.cells) → RegionConfig F (Γ.cell b)) × ((s : L.Free) → F s) where
  toFun f := (fun _ v ↦ f v, fun s ↦ f s)
  invFun p s := if hs : s ∈ L.cells.biUnion Γ.cell then p.1 (L.cellOf hs) ⟨s, L.mem_cellOf hs⟩
    else p.2 ⟨s, hs⟩
  left_inv f := by
    funext s
    dsimp only
    split_ifs <;> rfl
  right_inv p := by
    refine Prod.ext (funext fun b ↦ funext fun v ↦ ?_) (funext fun s ↦ ?_)
    · simp only [L.mem_biUnion_of_mem_cell b v.2, ↓reduceDIte]
      exact L.apply_cellOf p.1 b v _
    · simp only [s.2, ↓reduceDIte]

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)]

/-- The gate of the layer on a cell, as a Kraus family on the configurations of the cell. -/
def gateFamily (ev : Interpretation G) (L : Layer Γ G X Y) (b : L.cells) :
    KrausFamily (RegionConfig X (Γ.cell b)) (RegionConfig Y (Γ.cell b)) :=
  ⟨GateFamily.Outcome (L.gate b), ev (L.gate b)⟩

/-- The map of a layer on a matrix unit is the product of the maps of its gates and onsite
families on the local matrix units. -/
theorem map_single_apply (ev : Interpretation G) (L : Layer Γ G X Y) (x x' : Config X)
    (y y' : Config Y) :
    (L.krausFamily ev).map (Matrix.single x x' 1) y y' =
      (∏ b : L.cells, (L.gateFamily ev b).map (Matrix.single (fun v ↦ x v) (fun v ↦ x' v) 1)
        (fun v ↦ y v) (fun v ↦ y' v)) *
      ∏ s : L.Free, (L.onsite s).map (Matrix.single (x s) (x' s) 1) (y s) (y' s) := by
  simp only [KrausFamily.map_single_apply, Fintype.prod_sum, Finset.sum_mul_sum]
  refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun j _ ↦ ?_)
  change kraus ev L (i, j) y x * star (kraus ev L (i, j) y' x') = _
  simp only [kraus, star_mul', star_prod, gateFamily]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end Layer

end QuantumCircuit
