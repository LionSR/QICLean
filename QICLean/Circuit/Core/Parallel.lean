/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Seq
import QICLean.ManyBody.Sites.RegionUnion

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

open Matrix ManyBody Function
open scoped Kronecker

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

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [GateFamily G] in
variable (Γ) in
/-- The sites of a list of cells. -/
def cellsUnion (l : List Γ.Cell) : Finset S :=
  l.foldr (fun b U ↦ Γ.cell b ∪ U) ∅

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [GateFamily G] in
theorem cellsUnion_eq (l : List Γ.Cell) : cellsUnion Γ l = l.toFinset.biUnion Γ.cell := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [cellsUnion, List.foldr_cons, ← cellsUnion, ih, List.toFinset_cons,
      Finset.biUnion_insert]

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [GateFamily G] in
theorem disjoint_cellsUnion {b : Γ.Cell} {l : List Γ.Cell}
    (hl : (b :: l).Pairwise (Disjoint on Γ.cell)) : Disjoint (Γ.cell b) (cellsUnion Γ l) := by
  rw [cellsUnion_eq, Finset.disjoint_biUnion_right]
  exact fun b' hb' ↦ (List.pairwise_cons.mp hl).1 b' (List.mem_toFinset.mp hb')

/-- The product of matrices on pairwise disjoint cells, as a matrix on their union. -/
noncomputable def cellsProd
    (V : (b : Γ.Cell) → Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ) :
    (l : List Γ.Cell) → l.Pairwise (Disjoint on Γ.cell) →
      Matrix (RegionConfig X (cellsUnion Γ l)) (RegionConfig X (cellsUnion Γ l)) ℂ
  | [], _ => 1
  | b :: l, hl => reindex (regionUnionEquiv (disjoint_cellsUnion hl)).symm
      (regionUnionEquiv (disjoint_cellsUnion hl)).symm (V b ⊗ₖ cellsProd V l hl.of_cons)

theorem prod_place_eq_place_cellsProd
    (V : (b : Γ.Cell) → Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ) :
    (l : List Γ.Cell) → (hl : l.Pairwise (Disjoint on Γ.cell)) →
      (l.map fun b ↦ place (Γ.cell b) (V b)).prod = place (cellsUnion Γ l) (cellsProd V l hl)
  | [], _ => by
    rw [List.map_nil, List.prod_nil]
    exact (place_one (X := X) (D := ∅)).symm
  | b :: l, hl => by
    rw [List.map_cons, List.prod_cons, prod_place_eq_place_cellsProd V l hl.of_cons]
    exact (place_union_kronecker (disjoint_cellsUnion hl) _ _).symm

omit [Fintype S] [(s : S) → Fintype (X s)] in
theorem cellsProd_apply
    (V : (b : Γ.Cell) → Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ)
    (y x : Config X) : (l : List Γ.Cell) → (hl : l.Pairwise (Disjoint on Γ.cell)) →
      cellsProd V l hl (fun v ↦ y v) (fun v ↦ x v) =
        (l.map fun b ↦ V b (fun v ↦ y v) (fun v ↦ x v)).prod
  | [], _ => by
    simp only [cellsProd, one_apply, List.map_nil, List.prod_nil, ite_eq_left_iff, zero_ne_one,
      imp_false, not_not]
    exact funext fun v ↦ absurd v.2 (Finset.notMem_empty _)
  | b :: l, hl => by
    change (V b ⊗ₖ cellsProd V l hl.of_cons)
      (regionUnionEquiv (disjoint_cellsUnion hl) fun v ↦ y v)
      (regionUnionEquiv (disjoint_cellsUnion hl) fun v ↦ x v) = _
    rw [kroneckerMap_apply, List.map_cons, List.prod_cons]
    exact congrArg _ (cellsProd_apply V y x l hl.of_cons)

/-- The single Kraus operator of a layer of plain gates `V b` on disjoint cells is the product
of their placements, in the order of any enumeration of the cells. -/
theorem kraus_ofCells (cells : Finset Γ.Cell) (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell)
    (V : (b : Γ.Cell) → Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ)
    (l : List Γ.Cell) (hl : l.Nodup) (hcells : l.toFinset = cells)
    (i : (ofCells (G := KrausGate) cells h fun b ↦ KrausFamily.single (V b)).Index) :
    (ofCells (G := KrausGate) cells h fun b ↦ KrausFamily.single (V b)).kraus KrausGate.ev i =
      (l.map fun b ↦ place (Γ.cell b) (V b)).prod := by
  have hpw : l.Pairwise (Disjoint on Γ.cell) := hl.pairwise_of_set_pairwise (by
    intro a ha b hb hab
    exact h (by rw [← hcells]; exact List.mem_toFinset.mpr ha)
      (by rw [← hcells]; exact List.mem_toFinset.mpr hb) hab)
  rw [prod_place_eq_place_cellsProd V l hpw]
  ext y x
  rw [place_apply, cellsProd_apply V y x l hpw, ← List.prod_toFinset _ hl, hcells]
  change (∏ b : cells, V b.1 (fun v ↦ y v) (fun v ↦ x v)) *
    ∏ s : {s // s ∉ cells.biUnion Γ.cell},
      (KrausFamily.single (1 : Matrix (X s) (X s) ℂ)).op (i.2 s) (y s) (x s) = _
  rw [Finset.prod_coe_sort cells fun b ↦ V b (fun v ↦ y v) (fun v ↦ x v)]
  have hfree : ∏ s : {s // s ∉ cells.biUnion Γ.cell},
      (KrausFamily.single (1 : Matrix (X s) (X s) ℂ)).op (i.2 s) (y s) (x s) =
        if ∀ v ∉ cellsUnion Γ l, y v = x v then 1 else 0 := by
    change ∏ s : {s // s ∉ cells.biUnion Γ.cell}, (1 : Matrix (X s) (X s) ℂ) (y s) (x s) = _
    simp only [one_apply]
    rw [Finset.prod_boole, cellsUnion_eq, hcells]
    simp only [Finset.mem_univ, true_implies, Subtype.forall]
  rw [hfree, mul_ite, mul_one, mul_zero]

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

omit [Fintype S] [(s : S) → Fintype (X s)] in
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
    L.adjoint.kraus KrausGate.ev i = (L.kraus KrausGate.ev i)ᴴ := by
  ext y x
  simp only [kraus, conjTranspose_apply, star_mul', star_prod]
  rfl

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
theorem adjoint_adjoint {Y : S → Type} (L : Layer Γ KrausGate X Y) : L.adjoint.adjoint = L := by
  obtain ⟨cells, hd, gate, onsite⟩ := L
  simp only [adjoint, KrausFamily.adjoint, conjTranspose_conjTranspose]
  rfl

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
    (seqAdjoint Ls).kraus KrausGate.ev p = ((Ls.map U).reverse.prod)ᴴ := by
  refine (kraus_seq KrausGate.ev (fun L' ↦ (U L'.adjoint)ᴴ) (Ls.reverse.map Layer.adjoint) ?_
    p).trans ?_
  rotate_left
  · rw [conjTranspose_list_prod]
    simp only [List.map_reverse, List.reverse_reverse, List.map_map, Function.comp_def,
      Layer.adjoint_adjoint]
  · intro L' hL' i
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hL'
    refine (Layer.kraus_adjoint L i).trans ?_
    rw [hU L (List.mem_reverse.mp hL) i, Layer.adjoint_adjoint]

/-- The adjoint sequence has the costs of the sequence, for every cost depending only on the
cells of the layers. -/
theorem total_seqAdjoint (f : ∀ ⦃X Y : S → Type⦄, Layer Γ KrausGate X Y → ℕ)
    (hf : ∀ ⦃X Y : S → Type⦄ (L : Layer Γ KrausGate X Y), f L.adjoint = f L)
    (Ls : List (Layer Γ KrausGate X X)) (hne : ∀ L ∈ Ls, Nonempty L.Index) :
    (seqAdjoint Ls).total f = (seq Ls).total f := by
  rw [seqAdjoint, total_seq f _ fun L' hL' ↦ ?_, total_seq f _ hne, List.map_map,
    Function.comp_def, List.map_congr_left fun L _ ↦ hf L, List.map_reverse, List.sum_reverse]
  obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hL'
  exact hne L (List.mem_reverse.mp hL)

end Circuit

end QuantumCircuit
