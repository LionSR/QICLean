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

## Main results

* `QuantumCircuit.Circuit.kraus_seq` — the Kraus operator of a sequence of single-operator
  layers.
* `QuantumCircuit.Circuit.total_seq` — the cost of a sequence of layers with outcomes.
* `QuantumCircuit.Circuit.gateCount_seq_eq_length` — a sequence of layers of gate count `1`.
* `QuantumCircuit.Circuit.forall_seq`, `QuantumCircuit.Circuit.isUnbranched_seq`.
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
