/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Circuit

/-!
# Costs of circuits

A cost of layers, accumulated along the most expensive branch, is a cost of circuits. Depth,
gate count and the number of gates meeting a given site are its three instances:

* the depth of a layer is `1` if it uses a cell of positive cost and `0` otherwise;
* the gate count of a layer is the sum of the costs of its cells;
* a layer meets a site `s` as often as it has cells of positive cost containing `s`.

Onsite families cost nothing. A circuit is "of depth `T`" when its depth is at most `T`, so
statements are monotone in `T` without further proof. The cost of a composition is at most the
sum of the costs; this is proved once for every cost.

## Main definitions

* `QuantumCircuit.Circuit.total` — a cost of layers along the most expensive branch.
* `QuantumCircuit.Circuit.depth`, `QuantumCircuit.Circuit.gateCount`,
  `QuantumCircuit.Circuit.participation` — its instances.

## Main results

* `QuantumCircuit.Circuit.total_append` — subadditivity under composition.
* `QuantumCircuit.Circuit.depth_comp`, `QuantumCircuit.Circuit.gateCount_comp`,
  `QuantumCircuit.Circuit.participation_comp` — its three instances for `comp`.
* `QuantumCircuit.Circuit.depth_le_gateCount` — depth is at most the gate count.
* `QuantumCircuit.Circuit.total_seq_le` — the cost of a sequence of layers is at most the sum
  of their costs.
-/

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

namespace Layer

variable {X Y : S → Type}

/-- A layer has depth `1` when it uses a cell of positive cost, and `0` otherwise. -/
def depth (L : Layer Γ G X Y) : ℕ :=
  if (L.cells.filter fun b ↦ 0 < Γ.cost b).Nonempty then 1 else 0

/-- The gate count of a layer: the sum of the costs of its cells. -/
def gateCount (L : Layer Γ G X Y) : ℕ :=
  ∑ b ∈ L.cells, Γ.cost b

/-- The number of cells of positive cost of the layer containing the site `s`. -/
def meets (s : S) (L : Layer Γ G X Y) : ℕ :=
  (L.cells.filter fun b ↦ s ∈ Γ.cell b ∧ 0 < Γ.cost b).card

omit [Fintype S] [GateFamily G] in
theorem depth_le_gateCount (L : Layer Γ G X Y) : L.depth ≤ L.gateCount := by
  unfold depth gateCount
  split_ifs with h
  · obtain ⟨b, hb⟩ := h
    rw [Finset.mem_filter] at hb
    exact (Nat.one_le_iff_ne_zero.mpr hb.2.ne').trans
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hb.1)
  · exact Nat.zero_le _

end Layer

namespace Circuit

/-- A cost of layers accumulated along the most expensive branch of a circuit. -/
def total (f : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ) :
    {X Z : S → Type} → Circuit Γ G X Z → ℕ
  | _, _, done _ => 0
  | _, _, step L next => f L + Finset.univ.sup fun i ↦ (next i).total f

variable {X Y Z : S → Type}

/-- The depth of a circuit: the number of layers using a cell of positive cost, along the
deepest branch. -/
def depth (c : Circuit Γ G X Z) : ℕ :=
  c.total fun _ _ L ↦ L.depth

/-- The gate count of a circuit: the sum of the costs of the cells used, along the most
expensive branch. -/
def gateCount (c : Circuit Γ G X Z) : ℕ :=
  c.total fun _ _ L ↦ L.gateCount

/-- The number of gates of positive cost meeting the site `s`, along the branch with most such
gates. -/
def participation (c : Circuit Γ G X Z) (s : S) : ℕ :=
  c.total fun _ _ L ↦ L.meets s

@[simp] theorem total_done (f : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ) :
    (done X : Circuit Γ G X X).total f = 0 :=
  rfl

/-- The cost of `c.append k` is at most the cost of `c` plus the largest cost of a
continuation. -/
theorem total_append (f : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ) :
    {X Y : S → Type} → (c : Circuit Γ G X Y) → (k : c.Index → Circuit Γ G Y Z) →
      (c.append k).total f ≤ c.total f + Finset.univ.sup fun p ↦ (k p).total f
  | _, _, done _, k => by
    simp only [append, total, zero_add]
    exact Finset.le_sup (f := fun p ↦ (k p).total f) (Finset.mem_univ _)
  | _, _, step L next, k => by
    simp only [append, total, add_assoc]
    gcongr
    refine Finset.sup_le fun i _ ↦ (total_append f (next i) _).trans ?_
    gcongr
    · exact Finset.le_sup (f := fun i ↦ (next i).total f) (Finset.mem_univ i)
    · exact Finset.sup_le fun j _ ↦
        Finset.le_sup (f := fun p ↦ (k p).total f)
          (Finset.mem_univ (Sigma.mk (β := fun i ↦ (next i).Index) i j))

/-- The cost of a composition is at most the sum of the costs. -/
theorem total_comp (f : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ) (c : Circuit Γ G X Y)
    (c' : Circuit Γ G Y Z) : (c.comp c').total f ≤ c.total f + c'.total f :=
  (total_append f c fun _ ↦ c').trans (Nat.add_le_add_left (Finset.sup_le fun _ _ ↦ le_rfl) _)

theorem depth_comp (c : Circuit Γ G X Y) (c' : Circuit Γ G Y Z) :
    (c.comp c').depth ≤ c.depth + c'.depth :=
  total_comp _ c c'

theorem gateCount_comp (c : Circuit Γ G X Y) (c' : Circuit Γ G Y Z) :
    (c.comp c').gateCount ≤ c.gateCount + c'.gateCount :=
  total_comp _ c c'

theorem participation_comp (c : Circuit Γ G X Y) (c' : Circuit Γ G Y Z) (s : S) :
    (c.comp c').participation s ≤ c.participation s + c'.participation s :=
  total_comp _ c c'

/-- A cost bounded layer by layer by another is bounded by it. -/
theorem total_mono {f g : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ}
    (h : ∀ ⦃X Y : S → Type⦄ (L : Layer Γ G X Y), f L ≤ g L) :
    {X Z : S → Type} → (c : Circuit Γ G X Z) → c.total f ≤ c.total g
  | _, _, done _ => le_rfl
  | _, _, step L next => by
    simp only [total]
    gcongr with i
    · exact h L
    · exact total_mono h (next i)

/-- The depth of a circuit is at most its gate count. -/
theorem depth_le_gateCount (c : Circuit Γ G X Z) : c.depth ≤ c.gateCount :=
  total_mono (fun _ _ L ↦ L.depth_le_gateCount) c

/-- The cost of an unbranched sequence of layers is at most the sum of the costs of the
layers. -/
theorem total_seq_le [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (f : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ) :
    (Ls : List (Layer Γ G X X)) → (seq Ls).total f ≤ (Ls.map fun L ↦ f L).sum
  | [] => le_rfl
  | L :: Ls => by
    simp only [seq, total, List.map_cons, List.sum_cons]
    exact Nat.add_le_add_left (Finset.sup_le fun _ _ ↦ total_seq_le f Ls) _

theorem depth_seq_le [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (Ls : List (Layer Γ G X X)) : (seq Ls).depth ≤ (Ls.map Layer.depth).sum :=
  total_seq_le _ Ls

theorem gateCount_seq_le [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (Ls : List (Layer Γ G X X)) : (seq Ls).gateCount ≤ (Ls.map Layer.gateCount).sum :=
  total_seq_le _ Ls

end Circuit

end QuantumCircuit
