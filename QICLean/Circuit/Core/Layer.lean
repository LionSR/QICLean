/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausMap.KrausFamily
import QICLean.Circuit.Geometry.Basic
import QICLean.ManyBody.Sites.Placement

/-!
# Gate families and layers

A *system* on the sites `S` is a family `X : S → Type` of finite basis types, as in the Sites
layer; its space is `⊗_s ℂ^{X s}`. A *gate family* is a type `G D X Y` of gates on a region `D`
from the system `X` to the system `Y`, each with a finite type of outcomes. An *interpretation*
gives each outcome of each gate a matrix on the configurations of `D`. Plain gates,
`KrausGate`, are Kraus families on the configurations of a region and stand for themselves.
Keeping the matrices out of the syntax lets one circuit be evaluated against different
oracles, and lets gates carry syntax of their own, such as a weighted sum of circuits.

A *layer* from `X` to `Y` on a geometry `Γ` acts on a set of pairwise disjoint cells by gates,
and on every remaining site by a Kraus family from `X s` to `Y s`. Its Kraus operators are
indexed by a choice of one outcome for every cell and every remaining site, and each is the
product of the local entries:
`K_i(y, x) = ∏_b g_b(i_b)(y|_b, x|_b) · ∏_s k_s(i_s)(y_s, x_s)`.
The basis types may change, so a layer can prepare or discard ancillas and change the local
dimensions.

## Main definitions

* `QuantumCircuit.GateFamily`, `QuantumCircuit.Interpretation` — gate syntax and its matrices.
* `QuantumCircuit.KrausGate`, `QuantumCircuit.KrausGate.ev` — plain gates.
* `QuantumCircuit.Layer` — gates on disjoint cells and onsite families elsewhere.
* `QuantumCircuit.Layer.kraus`, `QuantumCircuit.Layer.krausFamily` — its Kraus operators.
* `QuantumCircuit.Layer.gateFamily` — the gate on a cell as a Kraus family.
* `QuantumCircuit.Layer.Forall` — every gate and onsite family satisfies a predicate.
* `QuantumCircuit.Layer.single` — one gate, with the identity elsewhere.
* `QuantumCircuit.Layer.lightCone` — a region together with the cells of the layer meeting it.

## Main results

* `QuantumCircuit.Layer.kraus_single` — a layer of one gate on the cell `b` is the placement
  `M ⊗ 1` of the matrix of the gate.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type}

/-- A family of gates: the syntax `G D X Y` of gates on the region `D` from the system `X` to
the system `Y`, and the finite type of outcomes of each gate. The matrices of the outcomes are
given by an `Interpretation`. -/
class GateFamily (G : Finset S → (S → Type) → (S → Type) → Type 1) where
  /-- The outcomes of a gate. -/
  Outcome : {D : Finset S} → {X Y : S → Type} → G D X Y → Type
  /-- A gate has finitely many outcomes. -/
  fintype : ∀ {D X Y} (g : G D X Y), Fintype (Outcome g)

instance GateFamily.instFintypeOutcome {G : Finset S → (S → Type) → (S → Type) → Type 1}
    [GateFamily G] {D : Finset S} {X Y : S → Type} (g : G D X Y) :
    Fintype (GateFamily.Outcome g) :=
  GateFamily.fintype g

/-- An interpretation of a gate family: a matrix for every outcome of every gate, from the
configurations of its region in the input system to those in the output system. -/
abbrev Interpretation (G : Finset S → (S → Type) → (S → Type) → Type 1) [GateFamily G] :=
  ∀ {D : Finset S} {X Y : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (g : G D X Y),
    GateFamily.Outcome g → Matrix (RegionConfig Y D) (RegionConfig X D) ℂ

/-- Plain gates: a Kraus family on the configurations of the region. -/
abbrev KrausGate (D : Finset S) (X Y : S → Type) : Type 1 :=
  KrausFamily (RegionConfig X D) (RegionConfig Y D)

instance : GateFamily (S := S) KrausGate where
  Outcome g := g.Index
  fintype g := g.fintype

/-- The interpretation of plain gates: a Kraus family stands for itself. -/
def KrausGate.ev : Interpretation (S := S) KrausGate :=
  fun g i ↦ g.op i

@[simp] theorem KrausGate.ev_apply {D : Finset S} {X Y : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (g : KrausGate D X Y)
    (i : GateFamily.Outcome g) : KrausGate.ev g i = g.op i :=
  rfl

variable [Fintype S] [DecidableEq S]

/-- A layer from the system `X` to the system `Y` on the geometry `Γ`: gates of the family `G` on
pairwise disjoint cells, and a Kraus family `X s → Y s` at every site met by no cell. -/
structure Layer (Γ : Geometry S) (G : Finset S → (S → Type) → (S → Type) → Type 1)
    (X Y : S → Type) : Type 1 where
  /-- The cells used by the layer. -/
  cells : Finset Γ.Cell
  /-- The cells are pairwise disjoint. -/
  pairwiseDisjoint : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell
  /-- The gate on each cell. -/
  gate : (b : cells) → G (Γ.cell b) X Y
  /-- The Kraus family at each site met by no cell. -/
  onsite : (s : {s // s ∉ cells.biUnion Γ.cell}) → KrausFamily (X s) (Y s)

namespace Layer

variable {Γ : Geometry S} {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]
  {X Y : S → Type}

/-- The sites met by no cell of the layer. -/
abbrev Free (L : Layer Γ G X Y) : Type := {s // s ∉ L.cells.biUnion Γ.cell}

omit [GateFamily G] in
/-- A product over the sites met by no cell of a layer, as a product over all sites. -/
theorem prod_free (L : Layer Γ G X Y) (f : L.Free → ℂ) :
    ∏ s, f s = ∏ s : S, if h : s ∈ L.cells.biUnion Γ.cell then 1 else f ⟨s, h⟩ := by
  simp only [Fintype.prod_dite, Finset.prod_const_one, one_mul]

/-- The Kraus indices of a layer: an outcome of every gate and of every onsite family. -/
def Index (L : Layer Γ G X Y) : Type :=
  ((b : L.cells) → GateFamily.Outcome (L.gate b)) × ((s : L.Free) → (L.onsite s).Index)

instance (L : Layer Γ G X Y) : Fintype L.Index := by
  unfold Index; infer_instance

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)]

/-- The Kraus operator of a layer for a choice of outcomes: the product of the entries of the
gates on the cells and of the onsite families at the remaining sites. -/
def kraus (ev : Interpretation G) (L : Layer Γ G X Y) (i : L.Index) :
    Matrix (Config Y) (Config X) ℂ :=
  fun y x ↦ (∏ b : L.cells, ev (L.gate b) (i.1 b) (fun v ↦ y v) (fun v ↦ x v)) *
    ∏ s : L.Free, (L.onsite s).op (i.2 s) (y s) (x s)

theorem kraus_apply (ev : Interpretation G) (L : Layer Γ G X Y) (i : L.Index) (y : Config Y)
    (x : Config X) :
    L.kraus ev i y x = (∏ b : L.cells, ev (L.gate b) (i.1 b) (fun v ↦ y v) (fun v ↦ x v)) *
      ∏ s : L.Free, (L.onsite s).op (i.2 s) (y s) (x s) :=
  rfl

/-- The Kraus family of a layer. -/
def krausFamily (ev : Interpretation G) (L : Layer Γ G X Y) :
    KrausFamily (Config X) (Config Y) :=
  ⟨L.Index, L.kraus ev⟩

end Layer

namespace Layer

variable {Γ : Geometry S} {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

/-- The gate of the layer on a cell, as a Kraus family under the interpretation `ev`. -/
def gateFamily (ev : Interpretation G) {X Y : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y)
    (b : L.cells) : KrausFamily (RegionConfig X (Γ.cell b)) (RegionConfig Y (Γ.cell b)) :=
  ⟨GateFamily.Outcome (L.gate b), ev (L.gate b)⟩

omit [Fintype S] in
/-- The gate of a layer of plain gates is its own Kraus family. -/
@[simp] theorem gateFamily_krausGate {X Y : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (L : Layer Γ KrausGate X Y) (b : L.cells) : L.gateFamily KrausGate.ev b = L.gate b :=
  rfl

/-- Every gate of the layer, as a Kraus family under the interpretation `ev`, and every onsite
family satisfies the predicate `P`. -/
def Forall (ev : Interpretation G)
    (P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop)
    {X Y : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y) : Prop :=
  (∀ b : L.cells, P (L.gateFamily ev b)) ∧ ∀ s, P (L.onsite s)

omit [Fintype S] in
/-- A local property passes to every property it implies. -/
theorem Forall.mono {ev : Interpretation G}
    {P Q : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hPQ : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (K : KrausFamily α β), P K → Q K)
    {X Y : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] {L : Layer Γ G X Y} (h : L.Forall ev P) : L.Forall ev Q :=
  ⟨fun b ↦ hPQ _ (h.1 b), fun s ↦ hPQ _ (h.2 s)⟩

/-- The backward light cone of the region `R` through a layer: `R` together with every cell of
the layer that meets `R`. -/
def lightCone {X Y : S → Type} (L : Layer Γ G X Y) (R : Finset S) : Finset S :=
  R ∪ (L.cells.filter fun b ↦ (Γ.cell b ∩ R).Nonempty).biUnion Γ.cell

/-- The layer with one gate `g` on the cell `b` and the identity at every other site. -/
def single {X : S → Type} [∀ s, DecidableEq (X s)] (b : Γ.Cell) (g : G (Γ.cell b) X X) :
    Layer Γ G X X where
  cells := {b}
  pairwiseDisjoint := by simp
  gate x := (Finset.mem_singleton.mp x.2).symm ▸ g
  onsite _ := KrausFamily.single 1

omit [Fintype S] [GateFamily G] in
theorem free_single_iff {X : S → Type} [∀ s, DecidableEq (X s)] (b : Γ.Cell)
    (g : G (Γ.cell b) X X) (s : S) :
    s ∉ (single b g).cells.biUnion Γ.cell ↔ s ∉ Γ.cell b := by
  simp [single]

/-- The Kraus operator of a layer of one gate `g` on the cell `b` is the placement `M ⊗ 1` of the
matrix `M` of `g` at the outcome of the index. -/
theorem kraus_single {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (ev : Interpretation G) (b : Γ.Cell) (g : G (Γ.cell b) X X) (i : (single b g).Index) :
    (single b g).kraus ev i =
      place (Γ.cell b) (ev g (i.1 ⟨b, Finset.mem_singleton_self b⟩)) := by
  ext y x
  rw [place_apply, kraus]
  have hb : ∀ c : (single b g).cells, c.1 = b := fun c ↦ Finset.mem_singleton.mp c.2
  let : Unique (single b g).cells :=
    ⟨⟨⟨b, Finset.mem_singleton_self b⟩⟩, fun c ↦ Subtype.ext (hb c)⟩
  rw [Fintype.prod_unique]
  have hcell : ev ((single b g).gate default) (i.1 default) (fun v ↦ y v) (fun v ↦ x v) =
      ev g (i.1 ⟨b, Finset.mem_singleton_self b⟩) (fun v ↦ y v) (fun v ↦ x v) := rfl
  rw [hcell]
  have hone : ∀ s : (single b g).Free,
      ((single b g).onsite s).op (i.2 s) (y s) (x s) = if y s = x s then 1 else 0 :=
    fun s ↦ one_apply
  rw [Finset.prod_congr rfl fun s _ ↦ hone s]
  by_cases h : ∀ v ∉ Γ.cell b, y v = x v
  · rw [Finset.prod_eq_one, mul_one]
    · exact (ite_eq_left h).symm
    intro s _
    simp only [h s ((free_single_iff b g s).mp s.2), ↓reduceIte]
  · simp only [h, ↓reduceIte]
    push Not at h
    obtain ⟨v, hv, hne⟩ := h
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨v, ?_⟩)
      (by simp only [hne, ↓reduceIte]))
    exact (free_single_iff b g v).mpr hv

end Layer

end QuantumCircuit
