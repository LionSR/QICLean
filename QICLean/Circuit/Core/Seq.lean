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
of the costs of the layers when no layer is empty. Local properties and unbranchedness hold by
construction.

For a layer of a single gate, the gate count and depth are given by the cost of its cell, and
its local properties by those of the gate.

## Main results

* `QuantumCircuit.Circuit.kraus_seq` — the Kraus operator of a sequence of single-operator
  layers.
* `QuantumCircuit.Circuit.total_seq` — the cost of a sequence of nonempty layers.
* `QuantumCircuit.Circuit.forall_seq`, `QuantumCircuit.Circuit.isUnbranched_seq`.
* `QuantumCircuit.Layer.forall_single`, `QuantumCircuit.Layer.gateCount_single`,
  `QuantumCircuit.Layer.depth_single`.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

theorem KrausFamily.isUnitary_single_one {α : Type} [Fintype α] [DecidableEq α] :
    (KrausFamily.single (1 : Matrix α α ℂ)).IsUnitary :=
  ⟨⟨inferInstanceAs (Unique Unit)⟩, fun _ ↦ by simp⟩

namespace Layer

variable {X : S → Type} [∀ s, DecidableEq (X s)]

omit [Fintype S] [GateFamily G] in
/-- A layer of a single gate has the gate count of its cell. -/
theorem gateCount_single (b : Γ.Cell) (g : G (Γ.cell b) X X) :
    (single b g).gateCount = Γ.cost b := by
  simp [gateCount_eq_sum, single]

omit [Fintype S] [GateFamily G] in
/-- A layer of a single gate on a cell of positive cost has depth `1`. -/
theorem depth_single (b : Γ.Cell) (g : G (Γ.cell b) X X) (hb : 0 < Γ.cost b) :
    (single b g).depth = 1 := by
  simp [depth, single, Finset.filter_singleton, hb]

omit [Fintype S] in
/-- A layer of a single gate with an outcome has a Kraus index. -/
theorem nonempty_index_single (b : Γ.Cell) (g : G (Γ.cell b) X X)
    [h : Nonempty (GateFamily.Outcome g)] : Nonempty (single b g).Index := by
  refine ⟨(fun c ↦ ?_, fun _ ↦ ())⟩
  obtain ⟨c, hc⟩ := c
  obtain rfl := Finset.mem_singleton.mp hc
  exact Classical.choice h

omit [Fintype S] in
/-- A layer of a single gate whose Kraus family satisfies `P`, with the identity elsewhere, has
`P` locally when the identity has it. -/
theorem forall_single [∀ s, Fintype (X s)] (ev : Interpretation G)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hone : ∀ {α : Type} [Fintype α] [DecidableEq α], P (KrausFamily.single (1 : Matrix α α ℂ)))
    (b : Γ.Cell) (g : G (Γ.cell b) X X)
    (hg : P (⟨GateFamily.Outcome g, ev g⟩ :
      KrausFamily (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)))) :
    (single b g).Forall ev P := by
  refine ⟨fun c ↦ ?_, fun _ ↦ hone⟩
  obtain ⟨c, hc⟩ := c
  obtain rfl := Finset.mem_singleton.mp hc
  exact hg

end Layer

namespace Circuit

variable {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The Kraus operator of a sequence of layers each with the single Kraus operator `U L` is the
product of these, the first layer on the right. -/
theorem kraus_seq (ev : Interpretation G) (U : Layer Γ G X X → Matrix (Config X) (Config X) ℂ) :
    (Ls : List (Layer Γ G X X)) → (∀ L ∈ Ls, ∀ i, L.kraus ev i = U L) →
      ∀ p, (seq Ls).kraus ev p = (Ls.map U).reverse.prod
  | [], _, _ => rfl
  | L :: Ls, h, ⟨i, p⟩ => by
    change (step L fun _ ↦ seq Ls).kraus ev ⟨i, p⟩ = _
    rw [kraus_step, kraus_seq ev U Ls (fun L' hL' ↦ h L' (List.mem_cons_of_mem L hL')) p,
      h L List.mem_cons_self i, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton]

omit [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
/-- The cost of a sequence of layers with nonempty index types is the sum of their costs. -/
theorem total_seq [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (f : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ) :
    (Ls : List (Layer Γ G X X)) → (∀ L ∈ Ls, Nonempty L.Index) →
      (seq Ls).total f = (Ls.map fun L ↦ f L).sum
  | [], _ => rfl
  | L :: Ls, h => by
    obtain ⟨i⟩ := h L List.mem_cons_self
    simp only [seq, total, List.map_cons, List.sum_cons]
    rw [Finset.sup_const ⟨i, Finset.mem_univ i⟩,
      total_seq f Ls fun L' hL' ↦ h L' (List.mem_cons_of_mem L hL')]

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

end QuantumCircuit
