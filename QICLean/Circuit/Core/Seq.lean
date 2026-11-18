/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Channel
import QICLean.Circuit.Core.Cost

/-!
# Sequences of layers

An unbranched sequence of layers `seq Ls` is the circuit most algorithms are written as. Its
Kraus operator along a branch is the product of the Kraus operators of the layers, the first
layer on the right, when every layer has a single Kraus operator, and its costs are the sums
of the costs of the layers when every layer has an outcome. Local properties and unbranchedness
hold by construction.

The adjoint of a layer of plain gates has the adjoint gates and onsite families on the same
cells, from the output system to the input system. The adjoint of a sequence of layers on one
system is the sequence of the adjoint layers in reverse order, and for layers of one operator
each its Kraus operator is the adjoint of that of the sequence. Only such sequences are reversed.
In a branching circuit the later layers depend on the outcomes of the earlier ones, and in the
reverse order they would have to be chosen before those outcomes exist, so the reversal is not a
circuit. An unbranched circuit whose systems change from layer to layer reverses to a chain of
layers through the same systems in the opposite order, which a list of layers on one system
cannot hold.

## Main definitions

* `QuantumCircuit.Layer.adjoint`, `QuantumCircuit.Circuit.seqAdjoint` — the adjoint of a layer of
  plain gates and of a sequence of such layers.

## Main results

* `QuantumCircuit.Circuit.kraus_seq`, `QuantumCircuit.Circuit.kraus_seq_map` — the Kraus
  operator of a sequence of single-operator layers.
* `QuantumCircuit.Circuit.total_seq` — the cost of a sequence of layers with outcomes.
* `QuantumCircuit.Circuit.total_comp_of_isUnbranched` — the cost of an unbranched circuit
  followed by another.
* `QuantumCircuit.Circuit.gateCount_seq_eq_length` — a sequence of layers of gate count `1`.
* `QuantumCircuit.Circuit.forall_seq`, `QuantumCircuit.Circuit.isUnbranched_seq`.
* `QuantumCircuit.Layer.kraus_adjoint`, `QuantumCircuit.Circuit.kraus_seqAdjoint` — the Kraus
  operators of the adjoints.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

namespace Circuit

variable {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- When every Kraus operator of the `k`-th layer of a sequence is `Us k`, the Kraus operator of
the sequence is the product of the `Us k`, the first layer on the right. -/
theorem kraus_seq (ev : Interpretation G) :
    {Ls : List (Layer Γ G X X)} → {Us : List (Matrix (Config X) (Config X) ℂ)} →
      List.Forall₂ (fun L U ↦ ∀ i, L.kraus ev i = U) Ls Us →
      ∀ p, (seq Ls).kraus ev p = Us.reverse.prod
  | [], [], .nil, _ => rfl
  | L :: Ls, _ :: _, .cons hL h, q => by
    obtain ⟨i, p⟩ := (q : (step L fun _ ↦ seq Ls).Index)
    change (step L fun _ ↦ seq Ls).kraus ev ⟨i, p⟩ = _
    rw [kraus_step, kraus_seq ev h p, hL i, List.reverse_cons, List.prod_append,
      List.prod_singleton]

/-- The Kraus operator of the sequence of layers `f a` along a list `l`, when every Kraus
operator of `f a` is `V a`, is the product of the `V a`, the first layer on the right. -/
theorem kraus_seq_map (ev : Interpretation G) {ι : Type} (f : ι → Layer Γ G X X)
    (V : ι → Matrix (Config X) (Config X) ℂ) (l : List ι)
    (h : ∀ a ∈ l, ∀ i, (f a).kraus ev i = V a) (p : (seq (l.map f)).Index) :
    (seq (l.map f)).kraus ev p = (l.map V).reverse.prod := by
  refine kraus_seq ev ?_ p
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr h

/-- The cost of a sequence of layers with outcomes is the sum of their costs. -/
theorem total_seq (f : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ) :
    (Ls : List (Layer Γ G X X)) → (∀ L ∈ Ls, Nonempty L.Index) →
      (seq Ls).total f = (Ls.map fun L ↦ f L).sum
  | [], _ => rfl
  | L :: Ls, h => by
    obtain ⟨i⟩ := h L List.mem_cons_self
    simp only [seq, total, List.map_cons, List.sum_cons]
    rw [Finset.sup_const ⟨i, Finset.mem_univ i⟩,
      total_seq f Ls fun L' hL' ↦ h L' (List.mem_cons_of_mem L hL')]

/-- A sequence of layers with outcomes, each of gate count `1`, has the gate count of its
length. -/
theorem gateCount_seq_eq_length (Ls : List (Layer Γ G X X))
    (hne : ∀ L ∈ Ls, Nonempty L.Index) (hcount : ∀ L ∈ Ls, L.gateCount = 1) :
    (seq Ls).gateCount = Ls.length := by
  rw [gateCount, total_seq _ Ls hne, List.map_congr_left hcount, List.map_const',
    List.sum_replicate, smul_eq_mul, mul_one]

/-- The cost of an unbranched circuit with a branch followed by a circuit is the sum of the
costs. -/
theorem total_comp_of_isUnbranched (f : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ) {Z : S → Type} :
    {X Y : S → Type} → {c : Circuit Γ G X Y} → c.IsUnbranched → Nonempty c.Index →
      (c' : Circuit Γ G Y Z) → (c.comp c').total f = c.total f + c'.total f
  | _, _, .done _, _, _, _ => (zero_add _).symm
  | _, _, step L next, hc, ⟨p⟩, c' => by
    obtain ⟨i, q⟩ := (p : Σ i : L.Index, (next i).Index)
    have hn : ∀ j, next j = next i := fun j ↦ hc.1 j i
    change f L + Finset.univ.sup (fun j ↦ ((next j).comp c').total f) =
      (f L + Finset.univ.sup fun j ↦ (next j).total f) + c'.total f
    simp only [hn]
    rw [Finset.sup_const ⟨i, Finset.mem_univ i⟩, Finset.sup_const ⟨i, Finset.mem_univ i⟩,
      total_comp_of_isUnbranched f (hc.2 i) ⟨q⟩ c', add_assoc]

omit [Fintype S] in
/-- A sequence of layers satisfying `P` locally satisfies `P` locally. -/
theorem forall_seq (ev : Interpretation G)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop} :
    (Ls : List (Layer Γ G X X)) → (∀ L ∈ Ls, L.Forall ev P) → (seq Ls).Forall ev P
  | [], _ => trivial
  | L :: Ls, h => ⟨h L List.mem_cons_self,
      fun _ ↦ forall_seq ev Ls fun L' hL' ↦ h L' (List.mem_cons_of_mem L hL')⟩

omit [Fintype S] in
/-- A sequence of layers is unbranched. -/
theorem isUnbranched_seq : (Ls : List (Layer Γ G X X)) → (seq Ls).IsUnbranched
  | [] => trivial
  | _ :: Ls => ⟨fun _ _ ↦ rfl, fun _ ↦ isUnbranched_seq Ls⟩

end Circuit

/-! ### Adjoints -/

namespace Layer

variable {X Y : S → Type}

/-- The adjoint of a layer of plain gates: the adjoint gates and onsite families on the same
cells. -/
def adjoint (L : Layer Γ KrausGate X Y) : Layer Γ KrausGate Y X where
  cells := L.cells
  pairwiseDisjoint := L.pairwiseDisjoint
  gate b := (L.gate b).adjoint
  onsite s := (L.onsite s).adjoint

/-- The Kraus operators of the adjoint layer are the adjoints of those of the layer. -/
theorem kraus_adjoint [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (L : Layer Γ KrausGate X Y) (i : L.adjoint.Index) :
    L.adjoint.kraus KrausGate.ev i = (L.kraus KrausGate.ev i)ᴴ := by
  ext y x
  simp only [kraus, conjTranspose_apply, star_mul', star_prod]
  rfl

end Layer

namespace Circuit

variable {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The adjoint of a sequence of layers of plain gates: the adjoint layers in reverse order. -/
def seqAdjoint (Ls : List (Layer Γ KrausGate X X)) : Circuit Γ KrausGate X X :=
  seq (Ls.reverse.map Layer.adjoint)

/-- When every Kraus operator of the `k`-th layer of a sequence is `Us[k]`, the Kraus operator of
the adjoint sequence is the adjoint of the product of the `Us[k]`. -/
theorem kraus_seqAdjoint {Ls : List (Layer Γ KrausGate X X)}
    {Us : List (Matrix (Config X) (Config X) ℂ)}
    (h : List.Forall₂ (fun L U ↦ ∀ i, L.kraus KrausGate.ev i = U) Ls Us)
    (p : (seqAdjoint Ls).Index) :
    (seqAdjoint Ls).kraus KrausGate.ev p = (Us.reverse.prod)ᴴ := by
  rw [conjTranspose_list_prod]
  refine kraus_seq KrausGate.ev ?_ p
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_reverse_iff]
  refine h.imp fun L U hL i ↦ ?_
  rw [Layer.kraus_adjoint]
  exact congrArg _ (hL i)

end Circuit

end QuantumCircuit
