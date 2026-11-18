/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Channel
import QICLean.Circuit.Core.Cost

/-!
# Moving circuits between sites, geometries and gate families

A circuit moves layer by layer. A *layer map* `LayerMap` sends every system `X` on the sites
`S` to a system on the sites `S'` and every layer to a layer between the images of its systems,
with an equivalence of Kraus indices; `Circuit.mapLayers` applies it to every layer of a circuit.
Unbranchedness, local properties, costs and Kraus operators move along
(`Circuit.isUnbranched_mapLayers`, `Circuit.forall_mapLayers`, `Circuit.total_mapLayers_le`,
`Circuit.kraus_mapLayers`) as soon as they move along each layer.

There are two layer maps, one for each kind of change. Both move the cells along a morphism of
geometries `Geometry.Hom` over a map of sites and put one gate on each image cell, so the gate
outcomes, the gate factor of the Kraus operators, the local properties of the gates and the
weights of gates of the image layer are computed once for both.

**On the same sites** (`Circuit.mapGate`). The cells move along a morphism of geometries over the
identity of the sites, and the gates along a morphism of gate families. The systems do not
change. This covers a coarser geometry, such as nearest-neighbour cells inside all pairs, and a
larger gate set, and both at once. When the morphism of gate families is compatible with the
interpretations, the Kraus operators are those of the original circuit.

**To other sites** (`Circuit.mapSites`). A circuit on the sites `S` moves to the sites `S'` along
an equivalence `e : S' ≃ S ⊕ R`: the sites of `S` become the sites `e.symm (inl s)` of `S'`, and
the sites of `R` are idle, with a fixed basis `W r` and the identity on it in every layer. A
system `X` on `S` becomes the system `extendSystem e W X` on `S'`. The cells move along a
morphism of geometries over `siteEmb e`, and the gates along a transport of gate families. This
covers a register inside a larger system (`S' = S ⊕ R`, `e = Equiv.refl`) and relabelling of
sites (`R = Empty`). The Kraus operator of the moved circuit along a branch is that of the
original tensored with the identity on the idle sites; it is stated with a Kronecker product
because a circuit may change its basis types, so that its Kraus operators need not be square.

## Main definitions

* `QuantumCircuit.Geometry.Hom` — a morphism of geometries over a map of sites.
* `QuantumCircuit.LayerMap`, `QuantumCircuit.Circuit.mapLayers` — circuits moved layer by layer.
* `QuantumCircuit.GateMorphism`, `QuantumCircuit.Circuit.mapGate` — the map on the same sites.
* `QuantumCircuit.extendSystem` — a system on other sites.
* `QuantumCircuit.GateTransport`, `QuantumCircuit.KrausGate.transport` — gates on other sites.
* `QuantumCircuit.Circuit.mapSites` — the map to other sites.

## Main results

* `QuantumCircuit.Circuit.kraus_mapLayers`, `QuantumCircuit.Circuit.kraus_mapGate`,
  `QuantumCircuit.Circuit.kraus_mapSites` — the Kraus operators of the image.
* `QuantumCircuit.Circuit.isUnbranched_mapLayers`, `QuantumCircuit.Circuit.forall_mapLayers`,
  `QuantumCircuit.Circuit.total_mapLayers_le` — what moves along each layer moves along the
  circuit; `Circuit.forall_mapGate` and `Circuit.forall_mapSites` are the local properties for the
  two maps.
* `QuantumCircuit.Layer.cellCost_mapGate`, `QuantumCircuit.Layer.cellCost_mapSites` — a weight of
  gates on a moved layer.
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit

/-! ### Morphisms of geometries -/

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

/-! ### Gates moved to an equal region -/

section Ndrec

variable {T : Type} {G : Finset T → (T → Type) → (T → Type) → Type 1} [GateFamily G]
  {X Y : T → Type} {D D' : Finset T}

/-- The outcomes of a gate moved to an equal region. -/
private def outcomeNdrec (hD : D = D') (g : G D X Y) :
    GateFamily.Outcome (Eq.ndrec (motive := fun D ↦ G D X Y) g hD) ≃ GateFamily.Outcome g := by
  subst hD; exact Equiv.refl _

omit [GateFamily G] in
/-- A function of gates takes the same value on a gate moved to an equal region. -/
private theorem fun_ndrec {α : Sort*} (w : ∀ ⦃D : Finset T⦄, G D X Y → α) (hD : D = D')
    (g : G D X Y) : w (Eq.ndrec (motive := fun D ↦ G D X Y) g hD) = w g := by
  subst hD; rfl

/-- The matrices of a gate moved to an equal region. -/
private theorem ev_ndrec {ev : Interpretation G} [∀ t, Fintype (X t)] [∀ t, DecidableEq (X t)]
    [∀ t, Fintype (Y t)] [∀ t, DecidableEq (Y t)] (hD : D = D') (g : G D X Y)
    (o : GateFamily.Outcome (Eq.ndrec (motive := fun D ↦ G D X Y) g hD))
    (y : Config Y) (x : Config X) :
    ev (Eq.ndrec (motive := fun D ↦ G D X Y) g hD) o (fun v ↦ y v) (fun v ↦ x v) =
      ev g (outcomeNdrec hD g o) (fun v ↦ y v) (fun v ↦ x v) := by
  subst hD; rfl

/-- A local property holds for a gate moved to an equal region when it holds for the gate. -/
private theorem prop_ndrec [DecidableEq T] {ev : Interpretation G}
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    [∀ t, Fintype (X t)] [∀ t, DecidableEq (X t)] [∀ t, Fintype (Y t)] [∀ t, DecidableEq (Y t)]
    (hD : D = D') (g : G D X Y)
    (hg : P (⟨GateFamily.Outcome g, ev g⟩ :
      KrausFamily (RegionConfig X D) (RegionConfig Y D))) :
    P (⟨GateFamily.Outcome (Eq.ndrec (motive := fun D ↦ G D X Y) g hD),
      ev (Eq.ndrec (motive := fun D ↦ G D X Y) g hD)⟩ :
        KrausFamily (RegionConfig X D') (RegionConfig Y D')) := by
  subst hD; exact hg

end Ndrec

/-! ### Layers on the image cells -/

section MapCells

variable {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']
  {Γ : Geometry S} {Γ' : Geometry S'} {ι : S ↪ S'} (h : Γ.Hom Γ' ι)
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]
  {G' : Finset S' → (S' → Type) → (S' → Type) → Type 1} [GateFamily G']
  {X Y : S → Type} {X' Y' : S' → Type}

namespace Layer

/-- The layer on the images of the cells of `L`, with the gate `g b` on the region `D b` of the
image of `b`, and the onsite families `o` at the remaining sites. -/
private noncomputable def mapCells (L : Layer Γ G X Y) (D : L.cells → Finset S')
    (hD : ∀ b, D b = Γ'.cell (h.cellMap b)) (g : (b : L.cells) → G' (D b) X' Y')
    (o : (s : {s' // s' ∉ (L.cells.map h.cellMap).biUnion Γ'.cell}) →
      KrausFamily (X' s) (Y' s)) : Layer Γ' G' X' Y' where
  cells := L.cells.map h.cellMap
  pairwiseDisjoint := h.pairwiseDisjoint_map L.pairwiseDisjoint
  gate b' := Eq.ndrec (motive := fun R ↦ G' R X' Y') (g ((L.cells.equivMap h.cellMap).symm b'))
    ((hD _).trans (congrArg (fun c ↦ Γ'.cell c.1)
      ((L.cells.equivMap h.cellMap).apply_symm_apply b')))
  onsite := o

variable (L : Layer Γ G X Y) (D : L.cells → Finset S') (hD : ∀ b, D b = Γ'.cell (h.cellMap b))
  (g : (b : L.cells) → G' (D b) X' Y')
  (o : (s : {s' // s' ∉ (L.cells.map h.cellMap).biUnion Γ'.cell}) → KrausFamily (X' s) (Y' s))

/-- The gate outcomes of the layer on the image cells are those of the gates `g b`. -/
private noncomputable def mapCellsGateEquiv :
    ((b' : (L.mapCells h D hD g o).cells) → GateFamily.Outcome ((L.mapCells h D hD g o).gate b')) ≃
      ((b : L.cells) → GateFamily.Outcome (g b)) :=
  (Equiv.piCongrLeft (fun b' ↦ GateFamily.Outcome ((L.mapCells h D hD g o).gate b'))
    (L.cells.equivMap h.cellMap)).symm.trans (Equiv.piCongrRight fun b ↦
      (outcomeNdrec _ _).trans (Equiv.cast (congrArg (fun c ↦ GateFamily.Outcome (g c))
        ((L.cells.equivMap h.cellMap).symm_apply_apply b))))

omit [Fintype S] [Fintype S'] [GateFamily G] in
/-- The gate factor of the Kraus operators of the layer on the image cells. -/
private theorem prod_mapCells {ev' : Interpretation G'} [∀ s, Fintype (X' s)]
    [∀ s, DecidableEq (X' s)] [∀ s, Fintype (Y' s)] [∀ s, DecidableEq (Y' s)]
    (i : (b' : (L.mapCells h D hD g o).cells) →
      GateFamily.Outcome ((L.mapCells h D hD g o).gate b'))
    (y : Config Y') (x : Config X') :
    ∏ b' : (L.mapCells h D hD g o).cells,
        ev' ((L.mapCells h D hD g o).gate b') (i b') (fun v ↦ y v) (fun v ↦ x v) =
      ∏ b : L.cells, ev' (g b) (mapCellsGateEquiv h L D hD g o i b) (fun v ↦ y v)
        (fun v ↦ x v) := by
  refine (Fintype.prod_equiv (L.cells.equivMap h.cellMap : L.cells ≃ (L.mapCells h D hD g o).cells)
    _ _ fun b ↦ ?_).symm
  refine Eq.trans ?_ (ev_ndrec _ _ _ y x).symm
  have key : ∀ {c₁ c₂ : L.cells} (hc : c₁ = c₂) (u : GateFamily.Outcome (g c₁)),
      ev' (g c₁) u (fun v ↦ y v) (fun v ↦ x v) = ev' (g c₂)
        (Equiv.cast (congrArg (fun c ↦ GateFamily.Outcome (g c)) hc) u)
          (fun v ↦ y v) (fun v ↦ x v) := by
    intro c₁ c₂ hc u; subst hc; rfl
  exact (key ((L.cells.equivMap h.cellMap).symm_apply_apply b) _).symm

omit [Fintype S] [Fintype S'] [GateFamily G] [GateFamily G'] in
/-- A weight of gates on the layer on the image cells is the sum of the weights of the gates
`g b`. -/
private theorem cellCost_mapCells (w : ∀ ⦃R : Finset S'⦄ ⦃X Y : S' → Type⦄, G' R X Y → ℕ) :
    (L.mapCells h D hD g o).cellCost (fun _ _ _ g ↦ w g) = ∑ b : L.cells, w (g b) := by
  unfold cellCost
  refine (Fintype.sum_equiv (L.cells.equivMap h.cellMap : L.cells ≃ (L.mapCells h D hD g o).cells)
    _ _ fun b ↦ ?_).symm
  have key : ∀ {c₁ c₂ : L.cells}, c₁ = c₂ → w (g c₁) = w (g c₂) := by rintro _ _ rfl; rfl
  exact (key ((L.cells.equivMap h.cellMap).symm_apply_apply b).symm).trans
    (fun_ndrec (G := G') (X := X') (Y := Y') (fun _ g ↦ w g) _ _).symm

omit [Fintype S] [Fintype S'] [GateFamily G] in
/-- The gates of the layer on the image cells have a local property when the gates `g b` have
it. -/
private theorem forall_gate_mapCells {ev' : Interpretation G'} [∀ s, Fintype (X' s)]
    [∀ s, DecidableEq (X' s)] [∀ s, Fintype (Y' s)] [∀ s, DecidableEq (Y' s)]
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hg : ∀ b, P (⟨GateFamily.Outcome (g b), ev' (g b)⟩ :
      KrausFamily (RegionConfig X' (D b)) (RegionConfig Y' (D b))))
    (b' : (L.mapCells h D hD g o).cells) :
    P (⟨GateFamily.Outcome ((L.mapCells h D hD g o).gate b'),
      ev' ((L.mapCells h D hD g o).gate b')⟩ :
        KrausFamily (RegionConfig X' (Γ'.cell b'.1)) (RegionConfig Y' (Γ'.cell b'.1))) :=
  prop_ndrec _ _ (hg _)

end Layer

end MapCells

/-! ### Circuits moved layer by layer -/

section LayerMap

variable {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']

/-- A map of layers from the geometry `Γ` with gates `G` on the sites `S` to the geometry `Γ'`
with gates `G'` on the sites `S'`: a system on `S'` for every system on `S`, and for every layer
a layer between the images of its systems, with an equivalence of Kraus indices. -/
structure LayerMap (Γ : Geometry S) (G : Finset S → (S → Type) → (S → Type) → Type 1)
    (Γ' : Geometry S') (G' : Finset S' → (S' → Type) → (S' → Type) → Type 1) [GateFamily G]
    [GateFamily G'] where
  /-- The image of a system. -/
  system : (S → Type) → (S' → Type)
  /-- The image of a finite system is finite. -/
  fintype : ∀ (X : S → Type) [∀ s, Fintype (X s)], ∀ s', Fintype (system X s')
  /-- The image of a system with decidable equality has decidable equality. -/
  decidableEq : ∀ (X : S → Type) [∀ s, DecidableEq (X s)], ∀ s', DecidableEq (system X s')
  /-- The image of a layer. -/
  layer : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)],
    Layer Γ G X Y → Layer Γ' G' (system X) (system Y)
  /-- The Kraus indices of the image of a layer are those of the layer. -/
  indexEquiv : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y),
    (layer L).Index ≃ L.Index

variable {Γ : Geometry S} {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]
  {Γ' : Geometry S'} {G' : Finset S' → (S' → Type) → (S' → Type) → Type 1} [GateFamily G']

instance LayerMap.instFintype (F : LayerMap Γ G Γ' G') (X : S → Type) [∀ s, Fintype (X s)]
    (s' : S') : Fintype (F.system X s') :=
  F.fintype X s'

instance LayerMap.instDecidableEq (F : LayerMap Γ G Γ' G') (X : S → Type)
    [∀ s, DecidableEq (X s)] (s' : S') : DecidableEq (F.system X s') :=
  F.decidableEq X s'

namespace Circuit

variable (F : LayerMap Γ G Γ' G')

/-- The circuit with every layer moved along `F`. -/
noncomputable def mapLayers : {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
    Circuit Γ G X Z → Circuit Γ' G' (F.system X) (F.system Z)
  | _, _, _, _, done _ => done _
  | _, _, _, _, step L next => step (F.layer L) fun i ↦ (next (F.indexEquiv L i)).mapLayers

/-- The branches of the moved circuit are those of the circuit. -/
noncomputable def mapIndexEquiv : {X Z : S → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → (c : Circuit Γ G X Z) → (c.mapLayers F).Index ≃ c.Index
  | _, _, _, _, done _ => Equiv.refl Unit
  | _, _, _, _, step L next =>
      Equiv.sigmaCongr (F.indexEquiv L) fun i ↦ (next (F.indexEquiv L i)).mapIndexEquiv

omit [Fintype S] [Fintype S'] in
theorem isUnbranched_mapLayers : {X Z : S → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → {c : Circuit Γ G X Z} → c.IsUnbranched →
      (c.mapLayers F).IsUnbranched
  | _, _, _, _, done _, _ => trivial
  | _, _, _, _, step L next, hc =>
    ⟨fun i j ↦ by
      change (next _).mapLayers F = (next _).mapLayers F
      rw [hc.1 _ _],
      fun _ ↦ isUnbranched_mapLayers (hc.2 _)⟩

omit [Fintype S] [Fintype S'] in
/-- A local property moves along every layer of a circuit when it moves along each layer. -/
theorem forall_mapLayers {ev : Interpretation G} {ev' : Interpretation G'}
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hL : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y),
      L.Forall ev P → (F.layer L).Forall ev' P) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      {c : Circuit Γ G X Z} → c.Forall ev P → (c.mapLayers F).Forall ev' P
  | _, _, _, _, done _, _ => trivial
  | _, _, _, _, step L _, hc => ⟨hL L hc.1, fun _ ↦ forall_mapLayers hL (hc.2 _)⟩

/-- A cost of the moved layers bounded by a cost of the layers bounds the cost of the moved
circuit. -/
theorem total_mapLayers_le (f : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ)
    (f' : ∀ ⦃X Y : S' → Type⦄, Layer Γ' G' X Y → ℕ)
    (hf : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y), f' (F.layer L) ≤ f L) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G X Z) → (c.mapLayers F).total f' ≤ c.total f
  | _, _, _, _, done _ => le_rfl
  | _, _, _, _, step L next => by
    change f' (F.layer L) +
        Finset.univ.sup (fun i ↦ ((next (F.indexEquiv L i)).mapLayers F).total f') ≤
      f L + Finset.univ.sup fun i ↦ (next i).total f
    exact add_le_add (hf L) (Finset.sup_le fun i _ ↦
      (total_mapLayers_le f f' hf _).trans (Finset.le_sup (f := fun i ↦ (next i).total f)
        (Finset.mem_univ _)))

/-- The Kraus operators of the moved circuit are the images of those of the circuit under a
multiplicative and unital map `Φ`, when this holds for every layer. -/
theorem kraus_mapLayers {ev : Interpretation G} {ev' : Interpretation G'}
    (Φ : ∀ ⦃X Z : S → Type⦄,
      Matrix (Config Z) (Config X) ℂ → Matrix (Config (F.system Z)) (Config (F.system X)) ℂ)
    (hone : ∀ ⦃X : S → Type⦄ [∀ s, DecidableEq (X s)],
      Φ (1 : Matrix (Config X) (Config X) ℂ) = 1)
    (hmul : ∀ ⦃X Y Z : S → Type⦄ [∀ s, Fintype (Y s)] (A : Matrix (Config Z) (Config Y) ℂ)
      (B : Matrix (Config Y) (Config X) ℂ), Φ (A * B) = Φ A * Φ B)
    (hL : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y) (i : (F.layer L).Index),
      (F.layer L).kraus ev' i = Φ (L.kraus ev (F.indexEquiv L i))) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G X Z) → (p : (c.mapLayers F).Index) →
      (c.mapLayers F).kraus ev' p = Φ (c.kraus ev (c.mapIndexEquiv F p))
  | _, _, _, _, done _, _ => (hone (X := _)).symm
  | _, _, _, _, step L next, q => by
    obtain ⟨i, p⟩ := q
    change ((next (F.indexEquiv L i)).mapLayers F).kraus ev' p * (F.layer L).kraus ev' i =
      Φ ((next (F.indexEquiv L i)).kraus ev ((next (F.indexEquiv L i)).mapIndexEquiv F p) *
        L.kraus ev (F.indexEquiv L i))
    rw [kraus_mapLayers Φ hone hmul hL _ p, hL L i, hmul]

end Circuit

end LayerMap


/-! ### Change of gate family on the same sites -/

section MapGate

variable {S : Type} [Fintype S] [DecidableEq S]
  {G₁ G₂ : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G₁] [GateFamily G₂]

/-- A morphism of gate families on the same sites: a map of gates with an equivalence of
outcomes. Compatibility with interpretations is the separate predicate `IsCompatible`, since the
cells and costs of the image do not depend on it. -/
structure GateMorphism (G₁ G₂ : Finset S → (S → Type) → (S → Type) → Type 1) [GateFamily G₁]
    [GateFamily G₂] where
  /-- The map of gates. -/
  map : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, G₁ D X Y → G₂ D X Y
  /-- The outcomes of the image are those of the gate. -/
  outcome : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄ (g : G₁ D X Y),
    GateFamily.Outcome (map g) ≃ GateFamily.Outcome g

/-- A morphism of gate families is compatible with interpretations `ev₁` and `ev₂` when the image
of a gate has, outcome by outcome, the matrix of the gate. -/
def GateMorphism.IsCompatible (φ : GateMorphism G₁ G₂) (ev₁ : Interpretation G₁)
    (ev₂ : Interpretation G₂) : Prop :=
  ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (g : G₁ D X Y) (o : GateFamily.Outcome (φ.map g)),
    ev₂ (φ.map g) o = ev₁ g (φ.outcome g o)

variable {Γ Δ : Geometry S} (h : Γ.Hom Δ (Function.Embedding.refl S)) (φ : GateMorphism G₁ G₂)

namespace Layer

variable {X Y : S → Type}

omit [Fintype S] [GateFamily G₁] in
private theorem mem_biUnion_mapGate (L : Layer Γ G₁ X Y) (s : S) :
    s ∈ (L.cells.map h.cellMap).biUnion Δ.cell ↔ s ∈ L.cells.biUnion Γ.cell := by
  rw [h.biUnion_map, Finset.map_refl]

omit [Fintype S] [DecidableEq S] in
private theorem cell_mapGate (b : Γ.Cell) : Γ.cell b = Δ.cell (h.cellMap b) :=
  ((h.cell_cellMap b).trans Finset.map_refl).symm

/-- The layer with its cells moved along `h` and its gates along `φ`, on the same sites and
systems. -/
noncomputable def mapGate (L : Layer Γ G₁ X Y) : Layer Δ G₂ X Y :=
  L.mapCells h (fun b ↦ Γ.cell b) (fun b ↦ cell_mapGate h b) (fun b ↦ φ.map (L.gate b))
    fun s ↦ L.onsite ⟨s.1, fun hs ↦ s.2 ((mem_biUnion_mapGate h L s.1).mpr hs)⟩

/-- The Kraus indices of a layer with its cells and gates moved. -/
noncomputable def mapGateIndexEquiv (L : Layer Γ G₁ X Y) : (L.mapGate h φ).Index ≃ L.Index :=
  Equiv.prodCongr
    ((mapCellsGateEquiv h L _ _ _ _).trans (Equiv.piCongrRight fun b ↦ φ.outcome (L.gate b)))
    (Equiv.piCongrLeft (fun s ↦ (L.onsite s).Index)
      (Equiv.subtypeEquivRight fun s ↦ not_congr (mem_biUnion_mapGate h L s)))

/-- With a compatible morphism of gate families, the moved layer has the Kraus operators of the
layer. -/
theorem kraus_mapGate [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] {ev₁ : Interpretation G₁} {ev₂ : Interpretation G₂}
    (hφ : φ.IsCompatible ev₁ ev₂) (L : Layer Γ G₁ X Y) (i : (L.mapGate h φ).Index) :
    (L.mapGate h φ).kraus ev₂ i = L.kraus ev₁ (L.mapGateIndexEquiv h φ i) := by
  ext y x
  exact congrArg₂ (· * ·) ((prod_mapCells h L _ _ _ _ i.1 y x).trans
      (Fintype.prod_congr _ _ fun b ↦ congrFun (congrFun (hφ _ _) _) _))
    (Fintype.prod_equiv (Equiv.subtypeEquivRight fun s ↦ not_congr (mem_biUnion_mapGate h L s) :
      (L.mapGate h φ).Free ≃ L.Free) _ _ fun _ ↦ rfl)

omit [Fintype S] in
/-- A local property invariant under relabelling of Kraus indices moves along a compatible
morphism of gate families. -/
theorem forall_mapGate [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] {ev₁ : Interpretation G₁} {ev₂ : Interpretation G₂}
    (hφ : φ.IsCompatible ev₁ ev₂)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hP : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (K : KrausFamily α β) {ι : Type} [Fintype ι] (u : ι ≃ K.Index),
        P K → P ⟨ι, fun i ↦ K.op (u i)⟩) {L : Layer Γ G₁ X Y} (hL : L.Forall ev₁ P) :
    (L.mapGate h φ).Forall ev₂ P := by
  refine ⟨forall_gate_mapCells h L _ _ _ _ fun b ↦ ?_, fun s ↦ hL.2 _⟩
  have := hP _ (φ.outcome _) (hL.1 b)
  convert this using 2
  exact funext (hφ _)

omit [Fintype S] in
/-- A weight of gates on the moved layer is the weight of the images of its gates. -/
theorem cellCost_mapGate (w : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, G₂ D X Y → ℕ)
    (L : Layer Γ G₁ X Y) :
    (L.mapGate h φ).cellCost (fun _ _ _ g ↦ w g) = L.cellCost fun _ _ _ g ↦ w (φ.map g) :=
  cellCost_mapCells h L _ _ _ _ w

end Layer

/-- The layer map of a morphism of geometries over the identity and a morphism of gate
families. -/
noncomputable abbrev LayerMap.ofGate : LayerMap Γ G₁ Δ G₂ where
  system X := X
  fintype _ _ := inferInstance
  decidableEq _ _ := inferInstance
  layer _ _ _ _ _ _ L := L.mapGate h φ
  indexEquiv _ _ _ _ _ _ L := L.mapGateIndexEquiv h φ

/-- A circuit with its cells moved along `h` and its gates along `φ`, on the same sites. -/
noncomputable def Circuit.mapGate {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (c : Circuit Γ G₁ X Z) : Circuit Δ G₂ X Z :=
  c.mapLayers (LayerMap.ofGate h φ)

namespace Circuit

variable {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- With a compatible morphism of gate families, the moved circuit has the Kraus operators of the
circuit. -/
theorem kraus_mapGate {ev₁ : Interpretation G₁} {ev₂ : Interpretation G₂}
    (hφ : φ.IsCompatible ev₁ ev₂) (c : Circuit Γ G₁ X Z)
    (p : (c.mapGate h φ).Index) :
    (c.mapGate h φ).kraus ev₂ p = c.kraus ev₁ (c.mapIndexEquiv (LayerMap.ofGate h φ) p) :=
  kraus_mapLayers (LayerMap.ofGate h φ) (fun _ _ A ↦ A) (fun _ _ ↦ rfl)
    (fun _ _ _ _ _ _ ↦ rfl) (fun _ _ _ _ _ _ L i ↦ L.kraus_mapGate h φ hφ i) c p

omit [Fintype S] in
/-- A local property invariant under relabelling of Kraus indices moves along a compatible
morphism of gate families. -/
theorem forall_mapGate {ev₁ : Interpretation G₁} {ev₂ : Interpretation G₂}
    (hφ : φ.IsCompatible ev₁ ev₂)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hP : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (K : KrausFamily α β) {ι : Type} [Fintype ι] (u : ι ≃ K.Index),
        P K → P ⟨ι, fun i ↦ K.op (u i)⟩) {c : Circuit Γ G₁ X Z} (hc : c.Forall ev₁ P) :
    (c.mapGate h φ).Forall ev₂ P :=
  forall_mapLayers _ (fun _ _ _ _ _ _ L hL ↦ L.forall_mapGate h φ hφ hP hL) hc

end Circuit

end MapGate

/-! ### Moving to other sites -/

section MapSites

variable {S S' R : Type}

/-- The site of `S'` of a site of `S`. -/
def siteEmb (e : S' ≃ S ⊕ R) : S ↪ S' :=
  ⟨fun s ↦ e.symm (.inl s), fun _ _ h ↦ Sum.inl_injective (e.symm.injective h)⟩

@[simp] theorem siteEmb_apply (e : S' ≃ S ⊕ R) (s : S) : siteEmb e s = e.symm (.inl s) :=
  rfl

/-- A system on `S` as a system on `S'`: the basis `X s` at the site `e.symm (inl s)`, and `W r`
at the idle site `e.symm (inr r)`. -/
abbrev extendSystem (e : S' ≃ S ⊕ R) (W : R → Type) (X : S → Type) : S' → Type :=
  fun s' ↦ Sum.elim X W (e s')

variable (e : S' ≃ S ⊕ R) (W : R → Type)

/-- The basis of `extendSystem e W X` at the site `siteEmb e s` is the basis of `s`. -/
private def extendSiteEquiv (X : S → Type) (s : S) : extendSystem e W X (siteEmb e s) ≃ X s :=
  Equiv.cast (congrArg (Sum.elim X W) (e.apply_symm_apply _))

/-- The configurations of `extendSystem e W X` are a configuration of `X` and one of the idle
sites. -/
def extendConfigEquiv (X : S → Type) :
    Config (extendSystem e W X) ≃ Config X × ((r : R) → W r) :=
  (Equiv.piCongrLeft (fun t ↦ Sum.elim X W t) e).trans (Equiv.sumPiEquivProdPi _)

private theorem extendConfigEquiv_fst (X : S → Type) (z : Config (extendSystem e W X)) (s : S) :
    (extendConfigEquiv e W X z).1 s =
      cast (congrArg (Sum.elim X W) (e.apply_symm_apply (.inl s))) (z (e.symm (.inl s))) := by
  change (Equiv.piCongrLeft (fun t ↦ Sum.elim X W t) e z) (.inl s) = _
  rw [Equiv.piCongrLeft_apply_eq_cast]

private theorem extendConfigEquiv_snd (X : S → Type) (z : Config (extendSystem e W X)) (r : R) :
    (extendConfigEquiv e W X z).2 r =
      cast (congrArg (Sum.elim X W) (e.apply_symm_apply (.inr r))) (z (e.symm (.inr r))) := by
  change (Equiv.piCongrLeft (fun t ↦ Sum.elim X W t) e z) (.inr r) = _
  rw [Equiv.piCongrLeft_apply_eq_cast]

/-- The configurations of the image of a region. -/
noncomputable def extendRegionEquiv (X : S → Type) (D : Finset S) :
    RegionConfig (extendSystem e W X) (D.map (siteEmb e)) ≃ RegionConfig X D :=
  (Equiv.piCongrLeft (fun v' : D.map (siteEmb e) ↦ extendSystem e W X v'.1)
    (D.equivMap (siteEmb e))).symm.trans (Equiv.piCongrRight fun v ↦ extendSiteEquiv e W X v.1)

private theorem extendRegionEquiv_restrict {Z : S → Type} (D : Finset S)
    (z : Config (extendSystem e W Z)) :
    extendRegionEquiv e W Z D (fun v : D.map (siteEmb e) ↦ z v.1) =
      fun v : D ↦ (extendConfigEquiv e W Z z).1 v.1 := by
  funext v
  change extendSiteEquiv e W Z v.1 (z (e.symm (.inl v.1))) =
    (Equiv.piCongrLeft (fun t ↦ Sum.elim Z W t) e z) (.inl v.1)
  rw [Equiv.piCongrLeft_apply_eq_cast]
  rfl

variable [∀ r, Fintype (W r)] [∀ r, DecidableEq (W r)]
  {G : Finset S → (S → Type) → (S → Type) → Type 1}
  {G' : Finset S' → (S' → Type) → (S' → Type) → Type 1} [GateFamily G] [GateFamily G']

/-- A transport of gates along `e`: a gate on `D` from `X` to `Y` gives a gate on the image of
`D` between the extended systems, with an equivalence of outcomes. -/
structure GateTransport (G : Finset S → (S → Type) → (S → Type) → Type 1)
    (G' : Finset S' → (S' → Type) → (S' → Type) → Type 1) [GateFamily G] [GateFamily G'] where
  /-- The transported gate. -/
  map : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, G D X Y →
    G' (D.map (siteEmb e)) (extendSystem e W X) (extendSystem e W Y)
  /-- Its outcomes are those of the gate. -/
  outcome : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄ (g : G D X Y),
    GateFamily.Outcome (map g) ≃ GateFamily.Outcome g

/-- A transport is compatible with interpretations `ev` and `ev'` when the transported gate
has, outcome by outcome, the matrix of the gate in the transported configurations. -/
def GateTransport.IsCompatible (φ : GateTransport e W G G') (ev : Interpretation G)
    (ev' : Interpretation G') : Prop :=
  ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (g : G D X Y) (o : GateFamily.Outcome (φ.map g)),
    ev' (φ.map g) o =
      (ev g (φ.outcome g o)).submatrix (extendRegionEquiv e W Y D) (extendRegionEquiv e W X D)

/-- The transport of plain gates. -/
noncomputable def KrausGate.transport : GateTransport e W (KrausGate (S := S))
    (KrausGate (S := S')) where
  map _ X Y g := ⟨g.Index, fun i ↦ (g.op i).submatrix (extendRegionEquiv e W Y _)
    (extendRegionEquiv e W X _)⟩
  outcome _ _ _ _ := Equiv.refl _

theorem KrausGate.isCompatible_transport :
    (KrausGate.transport e W).IsCompatible e W KrausGate.ev KrausGate.ev :=
  fun _ _ _ _ _ _ _ _ _ ↦ rfl

variable [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']
  {Γ : Geometry S} {Γ' : Geometry S'} (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')

namespace Layer

variable {X Y : S → Type}

/-- The onsite family of the moved layer at a site of `S ⊕ R`: that of the layer at a site of
`S`, the identity at an idle site. -/
private noncomputable def extendOnsite (L : Layer Γ G X Y) :
    (t : S ⊕ R) → (∀ s, t = .inl s → s ∉ L.cells.biUnion Γ.cell) →
      KrausFamily (Sum.elim X W t) (Sum.elim Y W t)
  | .inl s, hs => L.onsite ⟨s, hs s rfl⟩
  | .inr r, _ => KrausFamily.single (1 : Matrix (W r) (W r) ℂ)

omit [Fintype S] [Fintype S'] [GateFamily G] [GateFamily G'] in
private theorem not_mem_of_mapSites (L : Layer Γ G X Y) {s' : S'}
    (hs' : s' ∉ (L.cells.map h.cellMap).biUnion Γ'.cell) :
    ∀ s, e s' = .inl s → s ∉ L.cells.biUnion Γ.cell := by
  intro s hs hmem
  refine hs' ?_
  rw [h.biUnion_map, show s' = siteEmb e s by simp [← hs]]
  exact Finset.mem_map_of_mem _ hmem

/-- The layer moved along `e`, the morphism of geometries `h` and the transport `φ`: the
transported gates on the image cells, the onsite families at the sites of `S`, and the identity
at the idle sites. -/
noncomputable def mapSites (L : Layer Γ G X Y) :
    Layer Γ' G' (extendSystem e W X) (extendSystem e W Y) :=
  L.mapCells h (fun b ↦ (Γ.cell b).map (siteEmb e)) (fun b ↦ (h.cell_cellMap b).symm)
    (fun b ↦ φ.map (L.gate b)) fun s' ↦ extendOnsite W L (e s') (not_mem_of_mapSites e h L s'.2)

/-- The free sites of the layer and the idle sites are the free sites of the moved layer. -/
private noncomputable def freeEquiv (L : Layer Γ G X Y) : L.Free ⊕ R ≃ (L.mapSites e W h φ).Free :=
  Equiv.ofBijective
    (Sum.elim (fun s ↦ ⟨siteEmb e s.1, fun hmem ↦ by
        rw [show (L.mapSites e W h φ).cells = L.cells.map h.cellMap from rfl, h.biUnion_map]
          at hmem
        exact s.2 ((Finset.mem_map' _).mp hmem)⟩)
      (fun r ↦ ⟨e.symm (.inr r), fun hmem ↦ by
        rw [show (L.mapSites e W h φ).cells = L.cells.map h.cellMap from rfl, h.biUnion_map]
          at hmem
        obtain ⟨t, -, hts⟩ := Finset.mem_map.mp hmem
        simp at hts⟩)) (by
    constructor
    · rintro (a | a) (b | b) hab
      · simp only [Sum.elim_inl, Subtype.mk.injEq, siteEmb_apply, EmbeddingLike.apply_eq_iff_eq,
          Sum.inl.injEq] at hab
        exact congrArg _ (Subtype.ext hab)
      · simp [siteEmb_apply] at hab
      · simp [siteEmb_apply] at hab
      · simp only [Sum.elim_inr, Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
          Sum.inr.injEq] at hab
        exact congrArg _ hab
    · rintro ⟨s', hs'⟩
      rcases hes : e s' with s | r
      · refine ⟨.inl ⟨s, not_mem_of_mapSites e h L hs' s hes⟩, Subtype.ext ?_⟩
        simp [← hes]
      · exact ⟨.inr r, Subtype.ext (by simp [← hes])⟩)

omit [Fintype S] [Fintype S'] [∀ r, Fintype (W r)] in
private theorem freeEquiv_inl (L : Layer Γ G X Y) (a : L.Free) :
    e (L.freeEquiv e W h φ (.inl a)).1 = .inl a.1 :=
  e.apply_symm_apply _

omit [Fintype S] [Fintype S'] [∀ r, Fintype (W r)] in
private theorem freeEquiv_inr (L : Layer Γ G X Y) (r : R) :
    e (L.freeEquiv e W h φ (.inr r)).1 = .inr r :=
  e.apply_symm_apply _

/-- The Kraus indices of the onsite family of the moved layer at a site of `S`. -/
private def extendOnsiteIndexEquiv (L : Layer Γ G X Y) {t : S ⊕ R}
    (ht : ∀ s, t = .inl s → s ∉ L.cells.biUnion Γ.cell) {s : S} (hts : t = .inl s) :
    (extendOnsite W L t ht).Index ≃ (L.onsite ⟨s, ht s hts⟩).Index := by
  subst hts; exact Equiv.refl _

/-- The Kraus index of the onsite family of the moved layer at an idle site is trivial. -/
private def extendOnsiteIndexEquivInr (L : Layer Γ G X Y) {t : S ⊕ R}
    (ht : ∀ s, t = .inl s → s ∉ L.cells.biUnion Γ.cell) {r : R} (htr : t = .inr r) :
    (extendOnsite W L t ht).Index ≃ Unit := by
  subst htr; exact Equiv.refl _

/-- The Kraus indices of the moved layer are those of the layer. -/
noncomputable def mapSitesIndexEquiv (L : Layer Γ G X Y) : (L.mapSites e W h φ).Index ≃ L.Index :=
  Equiv.prodCongr
    ((mapCellsGateEquiv h L _ _ _ _).trans (Equiv.piCongrRight fun b ↦ φ.outcome (L.gate b)))
    (((Equiv.piCongrLeft (fun s' ↦ ((L.mapSites e W h φ).onsite s').Index)
      (L.freeEquiv e W h φ)).symm.trans (Equiv.sumPiEquivProdPi _)).trans
      ((Equiv.prodCongr (Equiv.piCongrRight fun s ↦ extendOnsiteIndexEquiv W L _
          (L.freeEquiv_inl e W h φ s))
        (Equiv.piCongrRight fun r ↦ extendOnsiteIndexEquivInr W L _
          (L.freeEquiv_inr e W h φ r))).trans
        ((Equiv.prodCongr (Equiv.refl _) (Equiv.ofUnique (R → Unit) PUnit.{1})).trans
          (Equiv.prodPUnit _))))

omit [Fintype S] [∀ r, Fintype (W r)] [GateFamily G] in
private theorem extendOnsite_op_inl (L : Layer Γ G X Y) {t : S ⊕ R}
    (ht : ∀ s, t = .inl s → s ∉ L.cells.biUnion Γ.cell)
    {s : S} (hts : t = .inl s) (o : (extendOnsite W L t ht).Index) (a : Sum.elim Y W t)
    (b : Sum.elim X W t) :
    (extendOnsite W L t ht).op o a b = (L.onsite ⟨s, ht s hts⟩).op
      (extendOnsiteIndexEquiv W L ht hts o) (cast (congrArg (Sum.elim Y W) hts) a)
      (cast (congrArg (Sum.elim X W) hts) b) := by
  subst hts; rfl

omit [Fintype S] [∀ r, Fintype (W r)] [GateFamily G] in
private theorem extendOnsite_op_inr (L : Layer Γ G X Y) {t : S ⊕ R}
    (ht : ∀ s, t = .inl s → s ∉ L.cells.biUnion Γ.cell)
    {r : R} (htr : t = .inr r) (o : (extendOnsite W L t ht).Index) (a : Sum.elim Y W t)
    (b : Sum.elim X W t) :
    (extendOnsite W L t ht).op o a b = (1 : Matrix (W r) (W r) ℂ)
      (cast (congrArg (Sum.elim Y W) htr) a) (cast (congrArg (Sum.elim X W) htr) b) := by
  subst htr; rfl

/-- With a compatible transport, the Kraus operators of the moved layer are those of the layer
tensored with the identity on the idle sites. -/
theorem kraus_mapSites [Fintype R] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] {ev : Interpretation G} {ev' : Interpretation G'}
    (hφ : φ.IsCompatible e W ev ev') (L : Layer Γ G X Y) (i : (L.mapSites e W h φ).Index) :
    (L.mapSites e W h φ).kraus ev' i =
      (L.kraus ev (L.mapSitesIndexEquiv e W h φ i) ⊗ₖ (1 : Matrix ((r : R) → W r) _ ℂ)).submatrix
        (extendConfigEquiv e W Y) (extendConfigEquiv e W X) := by
  ext y x
  rw [submatrix_apply, kronecker_apply]
  simp only [kraus]
  rw [mul_assoc]
  refine congrArg₂ (· * ·) ((prod_mapCells h L _ _ _ _ i.1 y x).trans
    (Fintype.prod_congr _ _ fun b ↦ ?_)) ?_
  · refine (congrFun (congrFun (hφ _ _) _) _).trans ?_
    rw [submatrix_apply, extendRegionEquiv_restrict, extendRegionEquiv_restrict]
    rfl
  · rw [← Fintype.prod_equiv (L.freeEquiv e W h φ) _ _ fun _ ↦ rfl, Fintype.prod_sum_type]
    congr 1
    · refine Finset.prod_congr rfl fun a _ ↦ ?_
      refine (extendOnsite_op_inl W L _ (L.freeEquiv_inl e W h φ a) _ _ _).trans ?_
      rw [extendConfigEquiv_fst, extendConfigEquiv_fst]
      rfl
    · refine (Finset.prod_congr rfl fun r _ ↦
        extendOnsite_op_inr W L _ (L.freeEquiv_inr e W h φ r) _ _ _).trans ?_
      simp only [one_apply, Finset.prod_boole, Finset.mem_univ, true_implies]
      refine if_congr ?_ rfl rfl
      rw [funext_iff]
      simp only [extendConfigEquiv_snd]
      exact Iff.rfl

omit [Fintype S] [Fintype S'] in
/-- A local property invariant under relabelling of bases and of Kraus indices, held by the
identity, moves along a compatible transport. -/
theorem forall_mapSites [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] {ev : Interpretation G} {ev' : Interpretation G'}
    (hφ : φ.IsCompatible e W ev ev')
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hP : ∀ {α β α' β' ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β'] [Fintype ι]
      (K : KrausFamily α β) (u : ι ≃ K.Index) (a : α' ≃ α) (b : β' ≃ β),
      P K → P ⟨ι, fun i ↦ (K.op (u i)).submatrix b a⟩)
    (hone : ∀ {α : Type} [Fintype α] [DecidableEq α], P (KrausFamily.single (1 : Matrix α α ℂ)))
    {L : Layer Γ G X Y} (hL : L.Forall ev P) : (L.mapSites e W h φ).Forall ev' P := by
  refine ⟨forall_gate_mapCells h L _ _ _ _ fun b ↦ ?_, fun s' ↦ ?_⟩
  · have := hP _ (φ.outcome _) (extendRegionEquiv e W _ _) (extendRegionEquiv e W _ _) (hL.1 b)
    convert this using 2
    exact funext (hφ _)
  · have key : ∀ (t : S ⊕ R) (ht : ∀ s, t = .inl s → s ∉ L.cells.biUnion Γ.cell),
        P (extendOnsite W L t ht) := by
      rintro (s | r) ht
      · exact hL.2 _
      · exact hone
    exact key _ _

omit [Fintype S] [Fintype S'] [∀ r, Fintype (W r)] in
/-- A weight of gates on the moved layer is the weight of the transported gates. -/
theorem cellCost_mapSites
    (w : ∀ ⦃D : Finset S'⦄ ⦃X Y : S' → Type⦄, G' D X Y → ℕ) (L : Layer Γ G X Y) :
    (L.mapSites e W h φ).cellCost (fun _ _ _ g ↦ w g) = L.cellCost fun _ _ _ g ↦ w (φ.map g) :=
  cellCost_mapCells h L _ _ _ _ w

end Layer

/-- The layer map of a site map `e`, a morphism of geometries over `siteEmb e` and a transport of
gates. -/
noncomputable abbrev LayerMap.ofSites : LayerMap Γ G Γ' G' where
  system := extendSystem e W
  fintype _ _ _ := inferInstance
  decidableEq _ _ _ := inferInstance
  layer _ _ _ _ _ _ L := L.mapSites e W h φ
  indexEquiv _ _ _ _ _ _ L := L.mapSitesIndexEquiv e W h φ

/-- The circuit moved along `e`, the morphism of geometries `h` and the transport `φ`. -/
noncomputable def Circuit.mapSites {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] (c : Circuit Γ G X Z) :
    Circuit Γ' G' (extendSystem e W X) (extendSystem e W Z) :=
  c.mapLayers (LayerMap.ofSites e W h φ)

namespace Circuit

variable {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- With a compatible transport, the Kraus operators of the moved circuit are those of the
circuit tensored with the identity on the idle sites. -/
theorem kraus_mapSites [Fintype R] {ev : Interpretation G} {ev' : Interpretation G'}
    (hφ : φ.IsCompatible e W ev ev') (c : Circuit Γ G X Z) (p : (c.mapSites e W h φ).Index) :
    (c.mapSites e W h φ).kraus ev' p =
      (c.kraus ev (c.mapIndexEquiv (LayerMap.ofSites e W h φ) p) ⊗ₖ
        (1 : Matrix ((r : R) → W r) _ ℂ)).submatrix (extendConfigEquiv e W Z)
          (extendConfigEquiv e W X) := by
  classical
  refine kraus_mapLayers (LayerMap.ofSites e W h φ)
    (fun _ _ K ↦ (K ⊗ₖ (1 : Matrix ((r : R) → W r) _ ℂ)).submatrix
      (extendConfigEquiv e W _) (extendConfigEquiv e W _)) (fun _ _ ↦ ?_)
    (fun _ _ _ _ A B ↦ ?_) (fun _ _ _ _ _ _ L i ↦ L.kraus_mapSites e W h φ hφ i) c p
  · rw [one_kronecker_one, submatrix_one_equiv]
  · have := submatrix_mul_equiv (A ⊗ₖ (1 : Matrix ((r : R) → W r) _ ℂ)) (B ⊗ₖ 1)
      (extendConfigEquiv e W _) (extendConfigEquiv e W _) (extendConfigEquiv e W _)
    rw [← mul_kronecker_mul, Matrix.mul_one] at this
    exact this.symm

omit [Fintype S] [Fintype S'] in
/-- A local property invariant under relabelling of bases and of Kraus indices, held by the
identity, moves along a compatible transport. -/
theorem forall_mapSites {ev : Interpretation G} {ev' : Interpretation G'}
    (hφ : φ.IsCompatible e W ev ev')
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hP : ∀ {α β α' β' ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β'] [Fintype ι]
      (K : KrausFamily α β) (u : ι ≃ K.Index) (a : α' ≃ α) (b : β' ≃ β),
      P K → P ⟨ι, fun i ↦ (K.op (u i)).submatrix b a⟩)
    (hone : ∀ {α : Type} [Fintype α] [DecidableEq α], P (KrausFamily.single (1 : Matrix α α ℂ)))
    {c : Circuit Γ G X Z} (hc : c.Forall ev P) : (c.mapSites e W h φ).Forall ev' P :=
  forall_mapLayers _ (fun _ _ _ _ _ _ _ hL ↦ Layer.forall_mapSites e W h φ hφ hP hone hL) hc

end Circuit

end MapSites

end QuantumCircuit
