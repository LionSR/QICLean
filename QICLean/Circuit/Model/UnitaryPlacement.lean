/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Geometry.Graph
import QICLean.Circuit.Geometry.Hom
import QICLean.Circuit.Geometry.Ring
import QICLean.Circuit.Model.UnitaryRegion
import QICLean.ManyBody.Sites.Relabel
import QICLean.ManyBody.Sites.Subregion

/-!
# Moving unitary circuits between sites

A unitary circuit moves layer by layer, its cells along a map of cells, and its gates and onsite
families along the corresponding identification of configurations. Two moves are needed.

**Placement on a region.** A unitary circuit on the cells inside a region `D`, as a geometry on
the sites of `D` (`Geometry.restrict`), is a unitary circuit on the whole geometry acting inside
`D`, with the identity outside `D` (`UnitaryCircuit.place`). Its operator is the placement
`ManyBody.place D` of the operator, and its depth and gate count do not change.

**Relabelling along a bijection of sites.** For a bijection `e : T ≃ S` of sites and a morphism
of geometries carrying the cells of a geometry on `T` to cells of a geometry on `S` of the same
cost, a unitary circuit on the system `t ↦ Y (e t)` moves to a unitary circuit on the system `Y`
(`UnitaryCircuit.relabel`), with the relabelled operator, the same depth and the same gate
count.

Together they place a circuit on a graph, such as an open chain of `m` sites, as a block of a
larger geometry: when neighbouring sites of the graph go to the two sites of a cell of cost `1`,
a product of `K` gates on the graph becomes a unitary circuit of depth at most `K` inside the
block, and a product of `K` gates of the larger geometry
(`IsGateProduct.isUnitaryCircuitOn_graph`). On a ring this is the statement that a product of
`K` two-site gates on a window of consecutive sites is a circuit of depth `K` inside the window,
the step behind the depth count of arXiv:2307.01696 (the unitaries `U_i` of eq. (10), each of
which "can be implemented in `T=O(q)`", paragraph before "The sequential-RG circuit").

The declarations restate `IsPairProduct.embedOp` of `TNLean/Circuit/PairProduct.lean` and
`IsPairProduct.isCircuitOn` and `isCircuitOn_list_prod_embedOp` of
`TNLean/Circuit/Composition.lean` at commit `414a18fb88` (Apache-2.0). The changes: the circuit
on the small chain is any unitary circuit, of any geometry and any finite basis at each site;
`embedOp e X` is the placement on the block of the operator relabelled along a bijection of the
small chain onto the block; one theorem covers every larger geometry whose cells contain the
images of neighbouring pairs.

## Main definitions

* `QuantumCircuit.Geometry.restrictHom` — the cells inside a region are cells of the geometry.
* `QuantumCircuit.Layer.place`, `QuantumCircuit.UnitaryCircuit.place` — placement on a region.
* `QuantumCircuit.Layer.relabel`, `QuantumCircuit.UnitaryCircuit.relabel` — relabelling along a
  bijection of sites.

## Main results

* `QuantumCircuit.UnitaryCircuit.op_eq_of_forall₂` — the operator of a circuit moved layer by
  layer along a multiplicative unital map.
* `QuantumCircuit.UnitaryCircuit.op_place`, `QuantumCircuit.UnitaryCircuit.op_relabel` — the
  operators of the moved circuits.
* `QuantumCircuit.IsGateProduct.isUnitaryCircuitOn_of_restrict` — a product of gates of cost `K`
  inside a region is a circuit of depth `K` inside it.
* `QuantumCircuit.IsGateProduct.isUnitaryCircuitOn_graph` — a product of gates on a graph placed
  as a block of a larger geometry.
* `QuantumCircuit.Geometry.graph_cell_nonempty`, `QuantumCircuit.Geometry.ring_cell_nonempty` —
  the cells of a graph and of the ring are nonempty, as the parallel composition needs.
* `QuantumCircuit.IsGateProduct.isUnitaryCircuitOn_ring`,
  `QuantumCircuit.IsGateProduct.place_pathGraph` — an open chain placed on consecutive sites of
  a ring or of a longer open chain.
-/

open Matrix ManyBody

namespace QuantumCircuit

/-! ### Operators of circuits moved layer by layer -/

namespace UnitaryCircuit

variable {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']
  {Γ : Geometry S} {Γ' : Geometry S'} {X : S → Type} [∀ s, Fintype (X s)]
  [∀ s, DecidableEq (X s)] {X' : S' → Type} [∀ s, Fintype (X' s)] [∀ s, DecidableEq (X' s)]

/-- The operator of a circuit `c'` whose layers correspond to those of `c`, each Kraus operator of
a layer of `c'` the image under a multiplicative unital map `Φ` of a Kraus operator of the
corresponding layer of `c`, is the image under `Φ` of the operator of `c`. -/
theorem op_eq_of_forall₂ (Φ : Matrix (Config X) (Config X) ℂ → Matrix (Config X') (Config X') ℂ)
    (hone : Φ 1 = 1) (hmul : ∀ A B, Φ (A * B) = Φ A * Φ B) {c : UnitaryCircuit Γ X}
    {c' : UnitaryCircuit Γ' X'}
    (h : List.Forall₂ (fun L L' ↦ ∀ i i', L'.kraus KrausGate.ev i' = Φ (L.kraus KrausGate.ev i))
      c.layers c'.layers) : c'.op = Φ c.op := by
  generalize hl : c.layers = Ls at h
  generalize hl' : c'.layers = Ls' at h
  induction h generalizing c c' with
  | nil => rw [op_eq_one hl, op_eq_one hl', hone]
  | @cons L L' Ls Ls' hL _ ih =>
    obtain ⟨i⟩ := (Layer.nonempty_unique_index_of_forall_isUnitary
      (c.isUnitary L (hl ▸ List.mem_cons_self))).map fun u ↦ u.default
    obtain ⟨i'⟩ := (Layer.nonempty_unique_index_of_forall_isUnitary
      (c'.isUnitary L' (hl' ▸ List.mem_cons_self))).map fun u ↦ u.default
    rw [op_eq_tail_op_mul hl i, op_eq_tail_op_mul hl' i', hmul, hL i i',
      ih (c := c.tail) (c' := c'.tail) (congrArg List.tail hl) (congrArg List.tail hl')]

end UnitaryCircuit

/-! ### Placement on a region -/

/-- The cells inside the region `D`, as a geometry on the sites of `D`, are cells of `Γ`. -/
def Geometry.restrictHom {S : Type} [DecidableEq S] (Γ : Geometry S) (D : Finset S) :
    (Γ.restrict D).Hom Γ (Function.Embedding.subtype (· ∈ D)) where
  cellMap := Function.Embedding.subtype _
  cell_cellMap b := (Finset.subtype_map_of_mem fun _ hv ↦ b.2 hv).symm

namespace Layer

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S} {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] {D : Finset S}
  {L : Layer (Γ.restrict D) KrausGate (fun s ↦ X s.1) (fun s ↦ X s.1)}

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
private theorem cell_subset_of_mem_map {b : Γ.Cell}
    (hb : b ∈ L.cells.map (Γ.restrictHom D).cellMap) : Γ.cell b ⊆ D := by
  obtain ⟨c, -, rfl⟩ := Finset.mem_map.mp hb
  exact c.2

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
private theorem mem_cells_of_mem_map {b : Γ.Cell}
    (hb : b ∈ L.cells.map (Γ.restrictHom D).cellMap) :
    (⟨b, cell_subset_of_mem_map hb⟩ : (Γ.restrict D).Cell) ∈ L.cells := by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
  exact hc

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
private theorem mem_biUnion_place_iff {s : S} (h : s ∈ D) :
    s ∈ (L.cells.map (Γ.restrictHom D).cellMap).biUnion Γ.cell ↔
      (⟨s, h⟩ : {s // s ∈ D}) ∈ L.cells.biUnion (Γ.restrict D).cell := by
  rw [(Γ.restrictHom D).biUnion_map]
  exact ⟨fun hs ↦ by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
    exact ht, fun hs ↦ Finset.mem_map_of_mem _ hs⟩

omit [∀ s, Fintype (X s)] in
/-- A layer on the cells inside `D` placed on the whole geometry: the cells as cells of `Γ`, the
gates on the configurations of the cells, the onsite families at the sites of `D`, and the
identity outside `D`. -/
def place (D : Finset S) (L : Layer (Γ.restrict D) KrausGate (fun s ↦ X s.1) (fun s ↦ X s.1)) :
    Layer Γ KrausGate X X where
  cells := L.cells.map (Γ.restrictHom D).cellMap
  pairwiseDisjoint := (Γ.restrictHom D).pairwiseDisjoint_map L.pairwiseDisjoint
  gate b := (L.gate ⟨⟨b.1, cell_subset_of_mem_map b.2⟩, mem_cells_of_mem_map b.2⟩).reindex
    (subregionConfigEquiv (cell_subset_of_mem_map b.2))
    (subregionConfigEquiv (cell_subset_of_mem_map b.2))
  onsite s := if h : s.1 ∈ D then
      L.onsite ⟨⟨s.1, h⟩, fun hs ↦ s.2 ((mem_biUnion_place_iff h).mpr hs)⟩
    else KrausFamily.single 1

omit [Fintype S] in
theorem forall_isUnitary_place (hu : L.Forall KrausGate.ev KrausFamily.IsUnitary) :
    (L.place D).Forall KrausGate.ev KrausFamily.IsUnitary := by
  refine ⟨fun b ↦ (hu.1 _).reindex _ _, fun s ↦ ?_⟩
  by_cases h : s.1 ∈ D
  · have key : ∀ K, K = L.onsite ⟨⟨s.1, h⟩, fun hs ↦ s.2 ((mem_biUnion_place_iff h).mpr hs)⟩ →
        KrausFamily.IsUnitary K := by
      rintro K rfl
      exact hu.2 _
    exact key _ (dite_eq_left h)
  · have key : ∀ K, K = KrausFamily.single (1 : Matrix (X s) (X s) ℂ) →
        KrausFamily.IsUnitary K := by
      rintro K rfl
      exact KrausFamily.isUnitary_single (one_mem _)
    exact key _ (dite_eq_right h)

omit [Fintype S] [∀ s, Fintype (X s)] in
/-- A layer placed on `D` acts inside `D`. -/
theorem isIn_place : (L.place D).IsIn D := by
  refine ⟨fun b hb ↦ cell_subset_of_mem_map hb, fun s hs ↦ ?_⟩
  have key : ∀ K, K = KrausFamily.single (1 : Matrix (X s) (X s) ℂ) → ∀ i, K.op i = 1 := by
    rintro K rfl _
    rfl
  exact key _ (dite_eq_right hs)

omit [Fintype S] [∀ s, Fintype (X s)] in
theorem gateCount_place : (L.place D).gateCount = L.gateCount := by
  rw [gateCount_eq_sum, gateCount_eq_sum]
  exact Finset.sum_map _ _ _

omit [Fintype S] [∀ s, Fintype (X s)] in
theorem depth_place : (L.place D).depth = L.depth := by
  simp only [depth, place, Finset.filter_map, Finset.map_nonempty]
  rfl

omit [Fintype S] [∀ s, Fintype (X s)] in
private theorem prod_cells_place (f : (L.place D).cells → ℂ) :
    ∏ b, f b = ∏ c : L.cells, f ⟨c.1.1, Finset.mem_map_of_mem _ c.2⟩ :=
  ((L.cells.equivMap (Γ.restrictHom D).cellMap).prod_comp f).symm

/-- The Kraus operator of a unitary layer placed on `D` is the placement on `D` of its Kraus
operator. -/
theorem kraus_place (hu : L.Forall KrausGate.ev KrausFamily.IsUnitary) (i : (L.place D).Index)
    (i' : L.Index) :
    (L.place D).kraus KrausGate.ev i = ManyBody.place D (L.kraus KrausGate.ev i') := by
  ext y x
  rw [ManyBody.place_apply, kraus_apply, kraus_apply, prod_cells_place, prod_free, prod_free]
  have hG : ∏ c : L.cells, KrausGate.ev ((L.place D).gate ⟨c.1.1, Finset.mem_map_of_mem _ c.2⟩)
      (i.1 ⟨c.1.1, Finset.mem_map_of_mem _ c.2⟩) (fun v ↦ y v) (fun v ↦ x v) =
      ∏ c : L.cells, KrausGate.ev (L.gate c) (i'.1 c) (fun v ↦ y v.1) (fun v ↦ x v.1) :=
    Fintype.prod_congr _ _ fun c ↦ congrFun (congrFun ((hu.1 c).op_eq_of_eq rfl _ _) _) _
  have hsplit : ∀ s, (if h : s ∈ (L.place D).cells.biUnion Γ.cell then 1 else
      ((L.place D).onsite ⟨s, h⟩).op (i.2 ⟨s, h⟩) (y s) (x s)) =
      (if s ∈ D then (if h : s ∈ (L.place D).cells.biUnion Γ.cell then 1 else
        ((L.place D).onsite ⟨s, h⟩).op (i.2 ⟨s, h⟩) (y s) (x s)) else 1) *
      (if s ∈ D ∨ y s = x s then 1 else 0) := by
    intro s
    by_cases hs : s ∈ D
    · rw [ite_eq_left hs, ite_eq_left (Or.inl hs), mul_one]
    · have hfree : s ∉ (L.place D).cells.biUnion Γ.cell := isIn_place.not_mem_biUnion hs
      rw [ite_eq_right hs, one_mul, dite_eq_right hfree, isIn_place.2 ⟨s, hfree⟩ hs, one_apply]
      exact if_congr (or_iff_right hs).symm rfl rfl
  have hin : ∀ t : {s // s ∈ D}, (if h : t.1 ∈ (L.place D).cells.biUnion Γ.cell then 1 else
      ((L.place D).onsite ⟨t.1, h⟩).op (i.2 ⟨t.1, h⟩) (y t.1) (x t.1)) =
      (if h : t ∈ L.cells.biUnion (Γ.restrict D).cell then 1 else
        (L.onsite ⟨t, h⟩).op (i'.2 ⟨t, h⟩) (y t.1) (x t.1)) := by
    intro t
    by_cases ht : t ∈ L.cells.biUnion (Γ.restrict D).cell
    · have ht' : t.1 ∈ (L.place D).cells.biUnion Γ.cell := (mem_biUnion_place_iff t.2).mpr ht
      rw [dite_eq_left ht', dite_eq_left ht]
    · have ht' : t.1 ∉ (L.place D).cells.biUnion Γ.cell :=
        fun h ↦ ht ((mem_biUnion_place_iff t.2).mp h)
      rw [dite_eq_right ht', dite_eq_right ht]
      exact congrFun (congrFun ((hu.2 ⟨t, ht⟩).op_eq_of_eq
        (K := (L.place D).onsite ⟨t.1, ht'⟩) (dite_eq_left t.2) _ _) _) _
  dsimp only
  rw [hG, Finset.prod_congr rfl fun s _ ↦ hsplit s, Finset.prod_mul_distrib,
    Fintype.prod_ite_mem, ← Finset.prod_coe_sort D, Fintype.prod_congr _ _ hin,
    Fintype.prod_boole]
  by_cases hyx : ∀ v ∉ D, y v = x v
  · rw [ite_eq_left hyx, ite_eq_left fun v ↦ (em (v ∈ D)).imp_right (hyx v), mul_one]
  · rw [ite_eq_right hyx, ite_eq_right fun h ↦ hyx fun v hv ↦ (h v).resolve_left hv,
      mul_zero, mul_zero]

end Layer

namespace UnitaryCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S} {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] {D : Finset S}

/-- **Placement on a region.** A unitary circuit on the cells inside `D`, as a geometry on the
sites of `D`, as a unitary circuit on `Γ` with the identity outside `D`. -/
def place (D : Finset S) (c : UnitaryCircuit (Γ.restrict D) (fun s ↦ X s.1)) :
    UnitaryCircuit Γ X :=
  ⟨c.layers.map (Layer.place D), fun L hL ↦ by
    obtain ⟨L', hL', rfl⟩ := List.mem_map.mp hL
    exact Layer.forall_isUnitary_place (c.isUnitary L' hL')⟩

variable (c : UnitaryCircuit (Γ.restrict D) (fun s ↦ X s.1))

/-- The operator of a circuit placed on `D` is the placement of its operator. -/
theorem op_place : (c.place D).op = ManyBody.place D c.op :=
  op_eq_of_forall₂ (ManyBody.place D) place_one (fun A B ↦ place_mul A B) <|
    List.forall₂_map_right_iff.mpr <| List.forall₂_same.mpr fun L hL i i' ↦
      Layer.kraus_place (c.isUnitary L hL) i' i

omit [Fintype S] in
theorem isIn_place : (c.place D).IsIn D := fun L hL ↦ by
  obtain ⟨L', -, rfl⟩ := List.mem_map.mp hL
  exact Layer.isIn_place

theorem depth_place : (c.place D).depth = c.depth := by
  simp only [depth_eq_sum, place, List.map_map, Function.comp_def, Layer.depth_place]

theorem gateCount_place : (c.place D).gateCount = c.gateCount := by
  simp only [gateCount_eq_sum, place, List.map_map, Function.comp_def, Layer.gateCount_place]

end UnitaryCircuit

section PlaceClasses

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S} {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] {D : Finset S} {T K : ℕ}
  {V : Matrix (RegionConfig X D) (RegionConfig X D) ℂ}

/-- A product of gates on the cells inside `D`, placed on `D`, is a product of gates of the same
cost on `Γ`. -/
theorem IsGateProduct.of_restrict (h : IsGateProduct (Γ.restrict D) K V) :
    IsGateProduct Γ K (ManyBody.place D V) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c.place D, (c.gateCount_place).trans_le hc, c.op_place⟩

/-- A unitary circuit of depth `T` on the cells inside `D`, placed on `D`, is a unitary circuit of
depth `T` inside `D`. -/
theorem IsUnitaryCircuit.isUnitaryCircuitOn_of_restrict (h : IsUnitaryCircuit (Γ.restrict D) T V) :
    IsUnitaryCircuitOn Γ D T (ManyBody.place D V) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c.place D, c.isIn_place, (c.depth_place).trans_le hc, c.op_place⟩

/-- **Gate count bounds depth inside a region.** A product of gates of cost `K` on the cells
inside `D`, placed on `D`, is a unitary circuit of depth `K` inside `D`. -/
theorem IsGateProduct.isUnitaryCircuitOn_of_restrict (h : IsGateProduct (Γ.restrict D) K V) :
    IsUnitaryCircuitOn Γ D K (ManyBody.place D V) :=
  h.isUnitaryCircuit.isUnitaryCircuitOn_of_restrict

end PlaceClasses

/-! ### Relabelling along a bijection of sites -/

namespace Layer

variable {T S : Type} [Fintype T] [DecidableEq T] [Fintype S] [DecidableEq S] {Δ : Geometry T}
  {Γ : Geometry S} {e : T ≃ S} (h : Δ.Hom Γ e.toEmbedding) {Y : S → Type}
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

omit [Fintype T] [DecidableEq T] [Fintype S] [DecidableEq S] in
private theorem mem_cell_iff {c : Δ.Cell} {b : Γ.Cell} (hc : h.cellMap c = b) (t : T) :
    t ∈ Δ.cell c ↔ e t ∈ Γ.cell b := by
  rw [← hc, h.cell_cellMap]
  exact (Finset.mem_map' e.toEmbedding).symm

/-- The gate of a relabelled layer on the image `b` of the cell `c`. -/
private def relabelGate (L : Layer Δ KrausGate (fun t ↦ Y (e t)) (fun t ↦ Y (e t)))
    {b : Γ.Cell} (c : L.cells) (hc : h.cellMap c.1 = b) : KrausGate (Γ.cell b) Y Y :=
  (L.gate c).reindex
    (regionConfigurationEquiv (Δ.cell c.1) (Γ.cell b) e (mem_cell_iff h hc)
      fun _ ↦ Equiv.refl _).symm
    (regionConfigurationEquiv (Δ.cell c.1) (Γ.cell b) e (mem_cell_iff h hc)
      fun _ ↦ Equiv.refl _).symm

/-- The onsite family of a relabelled layer at the image of the site `t`: that of the layer, or
the identity at a site met by a cell. -/
private def relabelOnsite (L : Layer Δ KrausGate (fun t ↦ Y (e t)) (fun t ↦ Y (e t))) (t : T) :
    KrausFamily (Y (e t)) (Y (e t)) :=
  if ht : t ∈ L.cells.biUnion Δ.cell then KrausFamily.single 1 else L.onsite ⟨t, ht⟩

/-- A layer on the system `t ↦ Y (e t)` relabelled along the bijection of sites `e` and the
morphism of geometries `h`: the image cells with the gates on the relabelled configurations, and
the onsite family of the site `t` at the site `e t`. -/
noncomputable def relabel (L : Layer Δ KrausGate (fun t ↦ Y (e t)) (fun t ↦ Y (e t))) :
    Layer Γ KrausGate Y Y where
  cells := L.cells.map h.cellMap
  pairwiseDisjoint := h.pairwiseDisjoint_map L.pairwiseDisjoint
  gate b := relabelGate h L ((L.cells.equivMap h.cellMap).symm b)
    (congrArg Subtype.val ((L.cells.equivMap h.cellMap).apply_symm_apply b))
  onsite s := Equiv.piCongrLeft (fun s ↦ KrausFamily (Y s) (Y s)) e (relabelOnsite L) s.1

variable {L : Layer Δ KrausGate (fun t ↦ Y (e t)) (fun t ↦ Y (e t))}

omit [Fintype T] [Fintype S] in
theorem forall_isUnitary_relabel (hu : L.Forall KrausGate.ev KrausFamily.IsUnitary) :
    (L.relabel h).Forall KrausGate.ev KrausFamily.IsUnitary := by
  have key : ∀ s, KrausFamily.IsUnitary
      (Equiv.piCongrLeft (fun s ↦ KrausFamily (Y s) (Y s)) e (relabelOnsite L) s) := by
    intro s
    obtain ⟨t, rfl⟩ := e.surjective s
    rw [Equiv.piCongrLeft_apply_apply]
    unfold relabelOnsite
    split_ifs
    · exact KrausFamily.isUnitary_single (one_mem _)
    · exact hu.2 _
  exact ⟨fun _ ↦ (hu.1 _).reindex _ _, fun s ↦ key s.1⟩

omit [Fintype T] [Fintype S] [∀ s, Fintype (Y s)] in
theorem gateCount_relabel (hcost : ∀ b, Γ.cost (h.cellMap b) = Δ.cost b) :
    (L.relabel h).gateCount = L.gateCount := by
  rw [gateCount_eq_sum, gateCount_eq_sum]
  exact (Finset.sum_map _ _ _).trans (Finset.sum_congr rfl fun b _ ↦ hcost b)

omit [Fintype T] [Fintype S] [∀ s, Fintype (Y s)] in
theorem depth_relabel (hcost : ∀ b, Γ.cost (h.cellMap b) = Δ.cost b) :
    (L.relabel h).depth = L.depth := by
  simp only [depth, relabel, Finset.filter_map, Finset.map_nonempty, Function.comp_def, hcost]

/-- The Kraus operator of a unitary layer relabelled along `e` is its Kraus operator on the
relabelled configurations. -/
theorem kraus_relabel (hu : L.Forall KrausGate.ev KrausFamily.IsUnitary)
    (i : (L.relabel h).Index) (i' : L.Index) :
    (L.relabel h).kraus KrausGate.ev i =
      reindex (siteConfigurationEquiv e fun _ ↦ Equiv.refl _)
        (siteConfigurationEquiv e fun _ ↦ Equiv.refl _) (L.kraus KrausGate.ev i') := by
  ext y x
  rw [reindex_apply, submatrix_apply, kraus_apply, kraus_apply, prod_free, prod_free]
  refine congrArg₂ (· * ·) (((L.cells.equivMap h.cellMap).prod_comp _).symm.trans
    (Fintype.prod_congr _ _ fun c ↦ ?_)) ((e.prod_comp _).symm.trans
      (Fintype.prod_congr _ _ fun t ↦ ?_))
  · have key : ∀ c' : L.cells, c' = c → ∀ (hc : h.cellMap c'.1 = h.cellMap c.1) o,
        KrausGate.ev (relabelGate h L c' hc) o (fun v ↦ y v) (fun v ↦ x v) =
          KrausGate.ev (L.gate c) (i'.1 c) (fun v ↦ y (e v.1)) (fun v ↦ x (e v.1)) := by
      rintro c' rfl hc o
      exact congrFun (congrFun ((hu.1 c').op_eq_of_eq rfl _ _) _) _
    exact key _ ((L.cells.equivMap h.cellMap).symm_apply_apply c)
      (by rw [Equiv.symm_apply_apply]) _
  · have hmem : e t ∈ (L.relabel h).cells.biUnion Γ.cell ↔ t ∈ L.cells.biUnion Δ.cell := by
      rw [show (L.relabel h).cells = L.cells.map h.cellMap from rfl, h.biUnion_map]
      exact Finset.mem_map' e.toEmbedding
    by_cases ht : t ∈ L.cells.biUnion Δ.cell
    · rw [dite_eq_left (hmem.mpr ht), dite_eq_left ht]
    · rw [dite_eq_right (fun h' ↦ ht (hmem.mp h')), dite_eq_right ht]
      exact congrFun (congrFun ((hu.2 ⟨t, ht⟩).op_eq_of_eq
        (K := (L.relabel h).onsite ⟨e t, fun h' ↦ ht (hmem.mp h')⟩)
        ((Equiv.piCongrLeft_apply_apply (fun s ↦ KrausFamily (Y s) (Y s)) e (relabelOnsite L)
          t).trans (dite_eq_right ht)) _ _) _) _

end Layer

namespace UnitaryCircuit

variable {T S : Type} [Fintype T] [DecidableEq T] [Fintype S] [DecidableEq S] {Δ : Geometry T}
  {Γ : Geometry S} {e : T ≃ S} (h : Δ.Hom Γ e.toEmbedding) {Y : S → Type}
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- **Relabelling along a bijection of sites.** A unitary circuit on the system `t ↦ Y (e t)`
of a geometry on `T`, as a unitary circuit on the system `Y` of a geometry on `S`, the cells
moved along the morphism of geometries `h`. -/
noncomputable def relabel (c : UnitaryCircuit Δ (fun t ↦ Y (e t))) : UnitaryCircuit Γ Y :=
  ⟨c.layers.map (Layer.relabel h), fun L hL ↦ by
    obtain ⟨L', hL', rfl⟩ := List.mem_map.mp hL
    exact Layer.forall_isUnitary_relabel h (c.isUnitary L' hL')⟩

variable (c : UnitaryCircuit Δ (fun t ↦ Y (e t)))

/-- The operator of a relabelled circuit is its operator on the relabelled configurations. -/
theorem op_relabel :
    (c.relabel h).op = reindex (siteConfigurationEquiv e fun _ ↦ Equiv.refl _)
      (siteConfigurationEquiv e fun _ ↦ Equiv.refl _) c.op :=
  op_eq_of_forall₂ (fun A ↦ reindex (siteConfigurationEquiv e fun _ ↦ Equiv.refl _)
      (siteConfigurationEquiv e fun _ ↦ Equiv.refl _) A)
    (by rw [reindex_apply, submatrix_one_equiv])
    (fun A B ↦ by simp only [reindex_apply, submatrix_mul_equiv]) <|
    List.forall₂_map_right_iff.mpr <| List.forall₂_same.mpr fun L hL i i' ↦
      Layer.kraus_relabel h (c.isUnitary L hL) i' i

theorem depth_relabel (hcost : ∀ b, Γ.cost (h.cellMap b) = Δ.cost b) :
    (c.relabel h).depth = c.depth := by
  simp only [depth_eq_sum, relabel, List.map_map, Function.comp_def, Layer.depth_relabel h hcost]

theorem gateCount_relabel (hcost : ∀ b, Γ.cost (h.cellMap b) = Δ.cost b) :
    (c.relabel h).gateCount = c.gateCount := by
  simp only [gateCount_eq_sum, relabel, List.map_map, Function.comp_def,
    Layer.gateCount_relabel h hcost]

end UnitaryCircuit

section RelabelClasses

variable {T S : Type} [Fintype T] [DecidableEq T] [Fintype S] [DecidableEq S] {Δ : Geometry T}
  {Γ : Geometry S} {e : T ≃ S} (h : Δ.Hom Γ e.toEmbedding)
  (hcost : ∀ b, Γ.cost (h.cellMap b) = Δ.cost b) {Y : S → Type} [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] {T' K : ℕ}
  {V : Matrix (Config fun t ↦ Y (e t)) (Config fun t ↦ Y (e t)) ℂ}

include hcost

/-- A product of gates relabelled along a bijection of sites carrying cells to cells of the same
cost is a product of gates of the same cost. -/
theorem IsGateProduct.relabel (hV : IsGateProduct Δ K V) :
    IsGateProduct Γ K (reindex (siteConfigurationEquiv e fun _ ↦ Equiv.refl _)
      (siteConfigurationEquiv e fun _ ↦ Equiv.refl _) V) := by
  obtain ⟨c, hc, rfl⟩ := hV
  exact ⟨c.relabel h, (c.gateCount_relabel h hcost).trans_le hc, c.op_relabel h⟩

/-- A unitary circuit relabelled along a bijection of sites carrying cells to cells of the same
cost is a unitary circuit of the same depth. -/
theorem IsUnitaryCircuit.relabel (hV : IsUnitaryCircuit Δ T' V) :
    IsUnitaryCircuit Γ T' (reindex (siteConfigurationEquiv e fun _ ↦ Equiv.refl _)
      (siteConfigurationEquiv e fun _ ↦ Equiv.refl _) V) := by
  obtain ⟨c, hc, rfl⟩ := hV
  exact ⟨c.relabel h, (c.depth_relabel h hcost).trans_le hc, c.op_relabel h⟩

end RelabelClasses

/-! ### A circuit on a graph placed as a block -/

/-- A morphism of geometries into `Γ` over a map of sites into the region `D` is a morphism into
the cells inside `D`. -/
def Geometry.Hom.toRestrict {T S : Type} [DecidableEq S] {Δ : Geometry T} {Γ : Geometry S}
    {D : Finset S} {ι : T ↪ {s // s ∈ D}}
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

/-- A simple graph `G` maps into a geometry `Γ` along an injection of sites `ι` carrying the two
ends of every edge to the sites of a cell of cost `1`: the edges go to such cells, at equal
cost. -/
theorem Geometry.exists_hom_graph {W S : Type} [Fintype W] [DecidableEq W] [DecidableEq S]
    {G : SimpleGraph W} {Γ : Geometry S} (ι : W ↪ S)
    (hcell : ∀ u v, G.Adj u v → ∃ b, Γ.cell b = {ι u, ι v} ∧ Γ.cost b = 1) :
    ∃ h : (Geometry.graph G).Hom Γ ι, ∀ b, Γ.cost (h.cellMap b) = (Geometry.graph G).cost b := by
  have key : ∀ b : (Geometry.graph G).Cell,
      ∃ b' : Γ.Cell, Γ.cell b' = ((Geometry.graph G).cell b).map ι ∧ Γ.cost b' = 1 := by
    rintro ⟨b, hb⟩
    induction b using Sym2.ind with
    | _ u v =>
      obtain ⟨b', h₁, h₂⟩ := hcell u v hb
      refine ⟨b', ?_, h₂⟩
      rw [h₁, Geometry.graph_cell_mk hb, Finset.map_insert, Finset.map_singleton]
  choose f hf using key
  refine ⟨⟨⟨f, fun b₁ b₂ h₁₂ ↦ ?_⟩, fun b ↦ (hf b).1⟩, fun b ↦ (hf b).2⟩
  have hcells := Finset.map_injective ι
    (((hf b₁).1.symm.trans (congrArg Γ.cell h₁₂)).trans (hf b₂).1)
  refine Subtype.ext (Sym2.ext fun v ↦ ?_)
  have hv : v ∈ (Geometry.graph G).cell b₁ ↔ v ∈ (Geometry.graph G).cell b₂ := by rw [hcells]
  exact Geometry.mem_graph_cell.symm.trans (hv.trans Geometry.mem_graph_cell)

/-- The cells of the geometry of a graph are nonempty, so circuits on it run in parallel
(`IsUnitaryCircuitOn.par`). -/
theorem Geometry.graph_cell_nonempty {W : Type} [Fintype W] [DecidableEq W] {G : SimpleGraph W}
    (b : (Geometry.graph G).Cell) : ((Geometry.graph G).cell b).Nonempty :=
  ⟨(b : Sym2 W).out.1, Geometry.mem_graph_cell.mpr (Sym2.out_fst_mem _)⟩

/-- The cells of the ring are nonempty, so circuits on it run in parallel
(`IsUnitaryCircuitOn.par`). -/
theorem Geometry.ring_cell_nonempty {N : ℕ} (b : (Geometry.ring N).Cell) :
    ((Geometry.ring N).cell b).Nonempty :=
  Finset.insert_nonempty _ _

section Block

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S} {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] {D : Finset S} {T : Type} [Fintype T]
  [DecidableEq T] {K : ℕ}

/-- **A circuit placed as a block.** Let `e` identify the sites `T` of a geometry `Δ` with the
sites of the region `D`, cells of `Δ` going to cells of `Γ` of the same cost. A product of gates
of cost `K` on `Δ`, relabelled along `e` and placed on `D`, is a unitary circuit of depth at most
`K` inside `D` and a product of gates of cost `K` on `Γ`. -/
theorem IsGateProduct.isUnitaryCircuitOn_of_hom {Δ : Geometry T} (e : T ≃ {s // s ∈ D})
    (h : Δ.Hom Γ (e.toEmbedding.trans (Function.Embedding.subtype _)))
    (hcost : ∀ b, Γ.cost (h.cellMap b) = Δ.cost b)
    {V : Matrix (Config fun t ↦ X (e t).1) (Config fun t ↦ X (e t).1) ℂ}
    (hV : IsGateProduct Δ K V) :
    IsUnitaryCircuitOn Γ D K (ManyBody.place D (reindex
        (siteConfigurationEquiv e fun _ ↦ Equiv.refl _)
        (siteConfigurationEquiv e fun _ ↦ Equiv.refl _) V)) ∧
      IsGateProduct Γ K (ManyBody.place D (reindex
        (siteConfigurationEquiv e fun _ ↦ Equiv.refl _)
        (siteConfigurationEquiv e fun _ ↦ Equiv.refl _) V)) :=
  have hV' := hV.relabel (Y := fun s : {s // s ∈ D} ↦ X s.1) h.toRestrict hcost
  ⟨hV'.isUnitaryCircuitOn_of_restrict, hV'.of_restrict⟩

/-- **A circuit on a graph placed as a block.** Let `e` identify the vertices of a simple graph
`G` with the sites of the region `D`, the ends of every edge going to the two sites of a cell of
`Γ` of cost `1`. A product of gates of cost `K` on the edges of `G`, relabelled along `e` and
placed on `D`, is a unitary circuit of depth at most `K` inside `D` and a product of gates of
cost `K` on `Γ`. For the open chain `G = SimpleGraph.pathGraph m` the hypothesis says that
neighbouring sites go to the sites of a cell. -/
theorem IsGateProduct.isUnitaryCircuitOn_graph {G : SimpleGraph T} (e : T ≃ {s // s ∈ D})
    (hcell : ∀ u v, G.Adj u v → ∃ b, Γ.cell b = {(e u).1, (e v).1} ∧ Γ.cost b = 1)
    {V : Matrix (Config fun t ↦ X (e t).1) (Config fun t ↦ X (e t).1) ℂ}
    (hV : IsGateProduct (Geometry.graph G) K V) :
    IsUnitaryCircuitOn Γ D K (ManyBody.place D (reindex
        (siteConfigurationEquiv e fun _ ↦ Equiv.refl _)
        (siteConfigurationEquiv e fun _ ↦ Equiv.refl _) V)) ∧
      IsGateProduct Γ K (ManyBody.place D (reindex
        (siteConfigurationEquiv e fun _ ↦ Equiv.refl _)
        (siteConfigurationEquiv e fun _ ↦ Equiv.refl _) V)) :=
  let ⟨h, hcost⟩ := Geometry.exists_hom_graph (e.toEmbedding.trans (Function.Embedding.subtype _))
    hcell
  hV.isUnitaryCircuitOn_of_hom e h hcost

end Block

/-- **An open chain placed on consecutive sites of a ring.** If `e` identifies the open chain of
`m` sites with the sites of the region `D` of the ring of `N` sites, consecutive sites going to
consecutive sites, a product of gates of cost `K` on neighbouring sites of the open chain,
relabelled along `e` and placed on `D`, is a unitary circuit of depth at most `K` on the ring
inside `D`.

Source: arXiv:2307.01696, paragraph before "The sequential-RG circuit": each block unitary of
eq. (10) "can be implemented in `T=O(q)`". -/
theorem IsGateProduct.isUnitaryCircuitOn_ring {N : ℕ} [NeZero N] {X : Fin N → Type}
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] {m K : ℕ} {D : Finset (Fin N)}
    (e : Fin m ≃ {s // s ∈ D}) (hsucc : ∀ p p' : Fin m, p'.val = p.val + 1 → (e p').1 = (e p).1 + 1)
    {V : Matrix (Config fun t ↦ X (e t).1) (Config fun t ↦ X (e t).1) ℂ}
    (hV : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph m)) K V) :
    IsUnitaryCircuitOn (Geometry.ring N) D K (ManyBody.place D (reindex
      (siteConfigurationEquiv e fun _ ↦ Equiv.refl _)
      (siteConfigurationEquiv e fun _ ↦ Equiv.refl _) V)) := by
  refine (hV.isUnitaryCircuitOn_graph e fun u v huv ↦ ?_).1
  rcases SimpleGraph.pathGraph_adj.mp huv with h | h
  · exact ⟨(e u).1, by rw [Geometry.ring_cell, hsucc u v h.symm], rfl⟩
  · exact ⟨(e v).1, by rw [Geometry.ring_cell, hsucc v u h.symm, Finset.pair_comm], rfl⟩

/-- **An open chain placed on consecutive sites of a longer open chain.** If `e` identifies the
open chain of `m` sites with the sites of the region `D` of the open chain of `n` sites,
consecutive sites going to consecutive sites, a product of gates of cost `K` on neighbouring
sites of the short chain, relabelled along `e` and placed on `D`, is a product of gates of cost
`K` on neighbouring sites of the long chain. -/
theorem IsGateProduct.place_pathGraph {n : ℕ} {X : Fin n → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] {m K : ℕ} {D : Finset (Fin n)} (e : Fin m ≃ {s // s ∈ D})
    (hsucc : ∀ p p' : Fin m, p'.val = p.val + 1 → ((e p').1 : ℕ) = (e p).1 + 1)
    {V : Matrix (Config fun t ↦ X (e t).1) (Config fun t ↦ X (e t).1) ℂ}
    (hV : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph m)) K V) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) K (ManyBody.place D (reindex
      (siteConfigurationEquiv e fun _ ↦ Equiv.refl _)
      (siteConfigurationEquiv e fun _ ↦ Equiv.refl _) V)) := by
  refine (hV.isUnitaryCircuitOn_graph e fun u v huv ↦ ?_).2
  rcases SimpleGraph.pathGraph_adj.mp huv with h | h
  · exact ⟨Geometry.pathCell (hsucc u v h.symm), Geometry.pathCell_cell _, rfl⟩
  · exact ⟨Geometry.pathCell (hsucc v u h.symm), by rw [Geometry.pathCell_cell, Finset.pair_comm],
      rfl⟩

end QuantumCircuit
