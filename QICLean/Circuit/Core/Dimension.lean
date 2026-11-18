/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Channel

/-!
# Bounded local bases

A circuit may change the basis of every site from layer to layer. It is bounded by `B` when
every basis of every system along every branch has between `1` and `B` elements. Bounds pass to
larger bounds and to compositions; the input is bounded, and so is the output along any branch.
A circuit without branches does not reach its output, so the output bound takes a branch. A
circuit whose gates and onsite families are trace-preserving, on nonempty finite bases, has a
bound: trace preservation keeps the bases nonempty.

## Main definitions

* `QuantumCircuit.Circuit.IsDimBounded` — every basis along the circuit has at most `B` elements.

## Main results

* `QuantumCircuit.Circuit.IsDimBounded.mono`, `QuantumCircuit.Circuit.IsDimBounded.comp`.
* `QuantumCircuit.Circuit.IsDimBounded.input`, `QuantumCircuit.Circuit.IsDimBounded.output`.
* `QuantumCircuit.Circuit.exists_isDimBounded` — a trace-preserving circuit has a bound.
-/

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {ev : Interpretation G}

namespace Circuit

/-- Every basis of every system along every branch has between `1` and `B` elements. -/
def IsDimBounded (B : ℕ) : {X Z : S → Type} → Circuit Γ G X Z → Prop
  | X, _, done _ => ∀ s, 0 < Nat.card (X s) ∧ Nat.card (X s) ≤ B
  | X, _, step _ next => (∀ s, 0 < Nat.card (X s) ∧ Nat.card (X s) ≤ B) ∧
      ∀ i, (next i).IsDimBounded B

omit [Fintype S] in
theorem IsDimBounded.input {B : ℕ} : {X Z : S → Type} → {c : Circuit Γ G X Z} →
    c.IsDimBounded B → ∀ s, 0 < Nat.card (X s) ∧ Nat.card (X s) ≤ B
  | _, _, done _, h => h
  | _, _, step _ _, h => h.1

omit [Fintype S] in
/-- The output bound needs a branch: a circuit without branches does not reach its output. -/
theorem IsDimBounded.output {B : ℕ} : {X Z : S → Type} → {c : Circuit Γ G X Z} →
    c.IsDimBounded B → c.Index → ∀ s, 0 < Nat.card (Z s) ∧ Nat.card (Z s) ≤ B
  | _, _, done _, h, _ => h
  | _, _, step _ next, h, p => IsDimBounded.output (c := next p.1) (h.2 p.1) p.2

omit [Fintype S] in
theorem IsDimBounded.mono {B C : ℕ} (hBC : B ≤ C) : {X Z : S → Type} →
    {c : Circuit Γ G X Z} → c.IsDimBounded B → c.IsDimBounded C
  | _, _, done _, h => fun s ↦ ⟨(h s).1, (h s).2.trans hBC⟩
  | _, _, step _ next, h =>
    ⟨fun s ↦ ⟨(h.1 s).1, (h.1 s).2.trans hBC⟩, fun i ↦ IsDimBounded.mono hBC (c := next i) (h.2 i)⟩

omit [Fintype S] in
theorem IsDimBounded.comp {B : ℕ} {Z : S → Type} : {X Y : S → Type} → {c : Circuit Γ G X Y} →
    {c' : Circuit Γ G Y Z} → c.IsDimBounded B → c'.IsDimBounded B → (c.comp c').IsDimBounded B
  | _, _, done _, _, _, h' => h'
  | _, _, step _ next, _, h, h' => ⟨h.1, fun i ↦ IsDimBounded.comp (c := next i) (h.2 i) h'⟩

omit [Fintype S] in
/-- A circuit with trace-preserving local families on nonempty finite bases is bounded by the
largest basis along it.

The input bases must be nonempty: `IsDimBounded` asks every basis to have an element, and on an
empty configuration space the empty Kraus family is trace-preserving, so a trace-preserving layer
on an empty basis may have no branches and leaves the later bases unconstrained. -/
theorem exists_isDimBounded [Finite S] : {X Z : S → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → [∀ s, Nonempty (X s)] → (c : Circuit Γ G X Z) →
    c.Forall ev KrausFamily.IsTP → ∃ B, c.IsDimBounded B
  | X, _, _, _, _, done _, _ => by
    have := Fintype.ofFinite S
    exact ⟨Finset.univ.sup fun s ↦ Nat.card (X s), fun s ↦
      ⟨Nat.card_pos, Finset.le_sup (f := fun s ↦ Nat.card (X s)) (Finset.mem_univ s)⟩⟩
  | X, _, _, _, _, step L next, h => by
    have := Fintype.ofFinite S
    have := (L.nonempty_of_forall_isTP ev h.1).2
    choose B hB using fun i ↦ exists_isDimBounded (next i) (h.2 i)
    refine ⟨max (Finset.univ.sup fun s ↦ Nat.card (X s)) (Finset.univ.sup B), fun s ↦
      ⟨Nat.card_pos, (Finset.le_sup (f := fun s ↦ Nat.card (X s)) (Finset.mem_univ s)).trans
        (le_max_left _ _)⟩, fun i ↦ (hB i).mono ?_⟩
    exact (Finset.le_sup (f := B) (Finset.mem_univ i)).trans (le_max_right _ _)

end Circuit

end QuantumCircuit
