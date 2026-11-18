/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Seq
import QICLean.ManyBody.Sites.RegionUnion

/-!
# Layers of gates on several cells

A layer of gates on a finite set of pairwise disjoint cells, with the identity elsewhere, is the
parallel application of the gates. Its Kraus operator at an index is the product, in the order
of any enumeration of the cells, of the placements of the matrices of the gates at that index,
and its map is the composite, in the same order, of the maps of the placed gates. The gates need
not be unitary: when they are trace-preserving the layer is trace-preserving
(`Layer.forall_ofCells` with `Layer.isTP_krausFamily`), hence a quantum channel. The layer of
one gate, `Layer.single`, is the case of one cell.

The product is formed along a list of cells, not over the cells as a finite set, because the
placed matrices need not commute in general and the statement must fix their order; the block
factorization of `Layer.kraus_eq_submatrix` splits a layer into two factors, which does not give
a product of one placement per cell.

## Main definitions

* `QuantumCircuit.Layer.ofCells` — gates on disjoint cells, the identity elsewhere.
* `QuantumCircuit.Layer.placeFamily` — the placement of a Kraus family on a region.

## Main results

* `QuantumCircuit.Layer.kraus_ofCells` — the Kraus operators, as products of placements.
* `QuantumCircuit.Layer.map_ofCells` — the map, as a composite of the maps of placed gates.
* `QuantumCircuit.Layer.forall_ofCells`, `QuantumCircuit.Layer.nonempty_index_ofCells`.
* `QuantumCircuit.Layer.single_eq_ofCells` and its cases `QuantumCircuit.Layer.forall_single`,
  `QuantumCircuit.Layer.nonempty_index_single`, `QuantumCircuit.Layer.gateCount_single`,
  `QuantumCircuit.Layer.depth_single`.
-/

open Matrix ManyBody Function
open scoped Kronecker

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {X : S → Type}

namespace Layer

section Definition

variable [∀ s, DecidableEq (X s)]

/-- The gates `g b` on the pairwise disjoint cells `b ∈ cells`, with the identity elsewhere. -/
def ofCells (cells : Finset Γ.Cell) (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell)
    (g : (b : cells) → G (Γ.cell b) X X) : Layer Γ G X X where
  cells := cells
  pairwiseDisjoint := h
  gate := g
  onsite _ := KrausFamily.single 1

omit [Fintype S] [GateFamily G] in
/-- A layer of one gate is the layer of gates on one cell. -/
theorem single_eq_ofCells (b : Γ.Cell) (g : G (Γ.cell b) X X) :
    single b g = ofCells {b} (by simp) fun c ↦ (Finset.mem_singleton.mp c.2).symm ▸ g :=
  rfl

omit [Fintype S] in
/-- A layer of gates with outcomes has a Kraus index. -/
theorem nonempty_index_ofCells (cells : Finset Γ.Cell)
    (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell) (g : (b : cells) → G (Γ.cell b) X X)
    (hg : ∀ b, Nonempty (GateFamily.Outcome (g b))) : Nonempty (ofCells cells h g).Index :=
  ⟨(fun b ↦ Classical.choice (hg b), fun _ ↦ ())⟩

omit [Fintype S] in
/-- A layer of gates satisfying `P`, with the identity elsewhere, satisfies `P` locally when the
identity does. -/
theorem forall_ofCells [∀ s, Fintype (X s)] (ev : Interpretation G)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hone : ∀ {α : Type} [Fintype α] [DecidableEq α], P (KrausFamily.single (1 : Matrix α α ℂ)))
    (cells : Finset Γ.Cell) (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell)
    (g : (b : cells) → G (Γ.cell b) X X)
    (hg : ∀ b : cells, P (⟨GateFamily.Outcome (g b), ev (g b)⟩ :
      KrausFamily (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)))) :
    (ofCells cells h g).Forall ev P :=
  ⟨hg, fun _ ↦ hone⟩

omit [Fintype S] in
/-- A layer of one gate with an outcome has a Kraus index. -/
theorem nonempty_index_single (b : Γ.Cell) (g : G (Γ.cell b) X X)
    [hg : Nonempty (GateFamily.Outcome g)] : Nonempty (single b g).Index := by
  rw [single_eq_ofCells]
  refine nonempty_index_ofCells _ _ _ fun c ↦ ?_
  obtain ⟨c, hc⟩ := c
  obtain rfl := Finset.mem_singleton.mp hc
  exact hg

omit [Fintype S] in
/-- A layer of one gate satisfying `P` satisfies `P` locally when the identity does. -/
theorem forall_single [∀ s, Fintype (X s)] (ev : Interpretation G)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hone : ∀ {α : Type} [Fintype α] [DecidableEq α], P (KrausFamily.single (1 : Matrix α α ℂ)))
    (b : Γ.Cell) (g : G (Γ.cell b) X X)
    (hg : P (⟨GateFamily.Outcome g, ev g⟩ :
      KrausFamily (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)))) :
    (single b g).Forall ev P := by
  rw [single_eq_ofCells]
  refine forall_ofCells ev hone _ _ _ fun c ↦ ?_
  obtain ⟨c, hc⟩ := c
  obtain rfl := Finset.mem_singleton.mp hc
  exact hg

omit [Fintype S] [GateFamily G] in
/-- A layer of one gate has the weight of its gate. -/
theorem cellCost_single (w : ∀ ⦃X Y : S → Type⦄ (b : Γ.Cell), G (Γ.cell b) X Y → ℕ)
    (b : Γ.Cell) (g : G (Γ.cell b) X X) : (single b g).cellCost w = w b g := by
  let : Unique (single b g).cells :=
    ⟨⟨⟨b, Finset.mem_singleton_self b⟩⟩, fun c ↦ Subtype.ext (Finset.mem_singleton.mp c.2)⟩
  rw [cellCost, Fintype.sum_unique]
  rfl

omit [Fintype S] [GateFamily G] in
/-- A layer of one gate has the gate count of its cell. -/
theorem gateCount_single (b : Γ.Cell) (g : G (Γ.cell b) X X) :
    (single b g).gateCount = Γ.cost b :=
  cellCost_single _ b g

omit [Fintype S] [GateFamily G] in
/-- A layer of one gate on a cell of positive cost has depth `1`. -/
theorem depth_single (b : Γ.Cell) (g : G (Γ.cell b) X X) (hb : 0 < Γ.cost b) :
    (single b g).depth = 1 := by
  simp [depth, single, Finset.filter_singleton, hb]

end Definition

section Product

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] {ι : Type} (r : ι → Finset S)

/-- The union of the regions `r c` of a list. -/
private def unionOf (l : List ι) : Finset S :=
  l.foldr (fun c U ↦ r c ∪ U) ∅

omit [Fintype S] in
private theorem mem_unionOf {l : List ι} {v : S} : v ∈ unionOf r l ↔ ∃ c ∈ l, v ∈ r c := by
  induction l with
  | nil => simp [unionOf]
  | cons c l ih =>
    change v ∈ r c ∪ unionOf r l ↔ _
    simp [ih]

omit [Fintype S] in
private theorem disjoint_unionOf {c : ι} {l : List ι} (hl : (c :: l).Pairwise (Disjoint on r)) :
    Disjoint (r c) (unionOf r l) := by
  refine Finset.disjoint_left.mpr fun v hv hv' ↦ ?_
  obtain ⟨c', hc', hv'⟩ := (mem_unionOf r).mp hv'
  exact Finset.disjoint_left.mp ((List.pairwise_cons.mp hl).1 c' hc') hv hv'

/-- The product of matrices on pairwise disjoint regions, as a matrix on their union. -/
private noncomputable def prodOn
    (V : (c : ι) → Matrix (RegionConfig X (r c)) (RegionConfig X (r c)) ℂ) :
    (l : List ι) → l.Pairwise (Disjoint on r) →
      Matrix (RegionConfig X (unionOf r l)) (RegionConfig X (unionOf r l)) ℂ
  | [], _ => 1
  | c :: l, hl => reindex (regionUnionEquiv (disjoint_unionOf r hl)).symm
      (regionUnionEquiv (disjoint_unionOf r hl)).symm (V c ⊗ₖ prodOn V l hl.of_cons)

private theorem prod_place_eq_place_prodOn
    (V : (c : ι) → Matrix (RegionConfig X (r c)) (RegionConfig X (r c)) ℂ) :
    (l : List ι) → (hl : l.Pairwise (Disjoint on r)) →
      (l.map fun c ↦ place (r c) (V c)).prod = place (unionOf r l) (prodOn r V l hl)
  | [], _ => by
    rw [List.map_nil, List.prod_nil]
    exact (place_one (X := X) (D := ∅)).symm
  | c :: l, hl => by
    rw [List.map_cons, List.prod_cons, prod_place_eq_place_prodOn V l hl.of_cons]
    exact (place_union_kronecker (disjoint_unionOf r hl) _ _).symm

omit [Fintype S] [∀ s, Fintype (X s)] in
private theorem prodOn_apply
    (V : (c : ι) → Matrix (RegionConfig X (r c)) (RegionConfig X (r c)) ℂ)
    (y x : Config X) : (l : List ι) → (hl : l.Pairwise (Disjoint on r)) →
      prodOn r V l hl (fun v ↦ y v) (fun v ↦ x v) =
        (l.map fun c ↦ V c (fun v ↦ y v) (fun v ↦ x v)).prod
  | [], _ => by
    simp only [prodOn, one_apply, List.map_nil, List.prod_nil, ite_eq_left_iff, zero_ne_one,
      imp_false, not_not]
    exact funext fun v ↦ absurd v.2 (Finset.notMem_empty _)
  | c :: l, hl => by
    change (V c ⊗ₖ prodOn r V l hl.of_cons)
      (regionUnionEquiv (disjoint_unionOf r hl) fun v ↦ y v)
      (regionUnionEquiv (disjoint_unionOf r hl) fun v ↦ x v) = _
    rw [kroneckerMap_apply, List.map_cons, List.prod_cons]
    exact congrArg _ (prodOn_apply V y x l hl.of_cons)

/-- The composite of the maps of Kraus families along a list is the map of the family of
products of their operators, indexed by a choice of an index at every position. -/
private theorem prod_map_apply {α : Type} [Fintype α] [DecidableEq α]
    (F : ι → KrausFamily α α) : (l : List ι) → ∀ ρ, (l.map fun c ↦ (F c).map).prod ρ =
      ∑ f : (k : Fin l.length) → (F (l.get k)).Index,
        (List.ofFn fun k ↦ (F (l.get k)).op (f k)).prod * ρ *
          ((List.ofFn fun k ↦ (F (l.get k)).op (f k)).prod)ᴴ
  | [], ρ => by simp
  | c :: l, ρ => by
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, prod_map_apply F l,
      KrausFamily.map_apply]
    refine Eq.trans ?_ ((Fin.consEquiv fun k : Fin (l.length + 1) ↦
      (F ((c :: l).get k)).Index).sum_comp _)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun f _ ↦ ?_
    simp only [List.ofFn_succ, List.prod_cons, Fin.consEquiv_apply, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rfl

end Product

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The Kraus operator of a layer of gates on disjoint cells at the index `i` is the product of
the placements of the matrices of the gates at `i`, in the order of any enumeration `l` of the
cells. -/
theorem kraus_ofCells (ev : Interpretation G) (cells : Finset Γ.Cell)
    (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell) (g : (b : cells) → G (Γ.cell b) X X)
    (l : List cells) (hl : l.Nodup) (hall : ∀ c, c ∈ l) (i : (ofCells cells h g).Index) :
    (ofCells cells h g).kraus ev i =
      (l.map fun c : cells ↦ place (Γ.cell c) (ev (g c) (i.1 c))).prod := by
  have hpw : l.Pairwise (Disjoint on fun c : cells ↦ Γ.cell c) :=
    hl.pairwise_of_forall_ne fun a _ b _ hab ↦ h a.2 b.2 fun e ↦ hab (Subtype.ext e)
  have hmem : ∀ v, v ∈ unionOf (fun c : cells ↦ Γ.cell c) l ↔ v ∈ cells.biUnion Γ.cell :=
    fun v ↦ by
      rw [mem_unionOf, Finset.mem_biUnion]
      exact ⟨fun ⟨c, _, hv⟩ ↦ ⟨c, c.2, hv⟩, fun ⟨b, hb, hv⟩ ↦ ⟨⟨b, hb⟩, hall _, hv⟩⟩
  rw [prod_place_eq_place_prodOn (fun c : cells ↦ Γ.cell c) _ l hpw]
  ext y x
  rw [place_apply, prodOn_apply _ _ y x l hpw, ← List.prod_toFinset _ hl,
    Finset.eq_univ_of_forall fun c ↦ List.mem_toFinset.mpr (hall c)]
  change (∏ b : cells, ev (g b) (i.1 b) (fun v ↦ y v) (fun v ↦ x v)) *
    ∏ s : {s // s ∉ cells.biUnion Γ.cell},
      (KrausFamily.single (1 : Matrix (X s) (X s) ℂ)).op (i.2 s) (y s) (x s) = _
  have hfree : ∏ s : {s // s ∉ cells.biUnion Γ.cell},
      (KrausFamily.single (1 : Matrix (X s) (X s) ℂ)).op (i.2 s) (y s) (x s) =
        if ∀ v ∉ unionOf (fun c : cells ↦ Γ.cell c) l, y v = x v then 1 else 0 := by
    change ∏ s : {s // s ∉ cells.biUnion Γ.cell}, (1 : Matrix (X s) (X s) ℂ) (y s) (x s) = _
    simp only [one_apply]
    rw [Finset.prod_boole]
    simp only [Finset.mem_univ, true_implies, Subtype.forall, hmem]
  rw [hfree, mul_ite, mul_one, mul_zero]

/-- The Kraus family `K ↦ K ⊗ 1` of a Kraus family on a region. -/
noncomputable def placeFamily (D : Finset S)
    (K : KrausFamily (RegionConfig X D) (RegionConfig X D)) : KrausFamily (Config X) (Config X) :=
  ⟨K.Index, fun i ↦ place D (K.op i)⟩

/-- The map of a layer of gates on disjoint cells is the composite of the maps of the placed
gates, in the order of any enumeration `l` of the cells. The gates need not have one matrix, so
the layer may be a quantum channel that is not unitary. -/
theorem map_ofCells (ev : Interpretation G) (cells : Finset Γ.Cell)
    (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell) (g : (b : cells) → G (Γ.cell b) X X)
    (l : List cells) (hl : l.Nodup) (hall : ∀ c, c ∈ l) :
    ((ofCells cells h g).krausFamily ev).map =
      (l.map fun c : cells ↦ (placeFamily (Γ.cell c)
        ⟨GateFamily.Outcome (g c), ev (g c)⟩).map).prod := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [prod_map_apply, KrausFamily.map_apply]
  let e : ((k : Fin l.length) → GateFamily.Outcome (g (l.get k))) ≃ (ofCells cells h g).Index :=
    (Equiv.piCongrLeft (fun c ↦ GateFamily.Outcome (g c))
      (hl.getEquivOfForallMemList l hall)).trans
      (Equiv.prodUnique _ ((s : (ofCells cells h g).Free) → Unit)).symm
  refine (Fintype.sum_equiv e _ _ fun f ↦ ?_).symm
  have hK : (ofCells cells h g).kraus ev (e f) =
      (List.ofFn fun k ↦ place (Γ.cell (l.get k)) (ev (g (l.get k)) (f k))).prod := by
    rw [kraus_ofCells ev cells h g l hl hall, ← List.ofFn_getElem_eq_map]
    congr 1
    refine List.ofFn_inj.mpr (funext fun k ↦ ?_)
    change place _ (ev _ (Equiv.piCongrLeft (fun c ↦ GateFamily.Outcome (g c))
      (hl.getEquivOfForallMemList l hall) f (hl.getEquivOfForallMemList l hall k))) = _
    exact congrArg (fun o ↦ place (Γ.cell (l.get k)) (ev (g (l.get k)) o))
      (Equiv.piCongrLeft_apply_apply (fun c ↦ GateFamily.Outcome (g c))
        (hl.getEquivOfForallMemList l hall) f k)
  change _ = (ofCells cells h g).kraus ev (e f) * ρ * ((ofCells cells h g).kraus ev (e f))ᴴ
  rw [hK]
  rfl

end Layer

end QuantumCircuit
