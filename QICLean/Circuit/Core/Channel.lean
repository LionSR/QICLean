/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Circuit

/-!
# Local properties of circuits and trace preservation

Unitarity, trace preservation and contractivity are not separate types of circuits: they are
properties of the Kraus families out of which a circuit is built. `Circuit.Forall ev P` says
that every gate, under the interpretation `ev`, and every onsite family of every layer on every
branch has the property `P`. A circuit is *unbranched* when no continuation depends on an
outcome.

A circuit all of whose local families are trace-preserving is trace-preserving, hence a quantum
channel, whether or not it branches: measurement with classical feedback is the sum over the
outcomes. This is proved by induction from the trace preservation of a layer.

## Main definitions

* `QuantumCircuit.Circuit.Forall` — every local family satisfies a predicate.
* `QuantumCircuit.Circuit.IsUnbranched` — no continuation depends on an outcome.

## Main results

* `QuantumCircuit.Circuit.Forall.append`, `QuantumCircuit.Circuit.Forall.comp`,
  `QuantumCircuit.Circuit.IsUnbranched.comp` — both notions pass to compositions.
* `QuantumCircuit.Circuit.isTP_krausFamily` — local trace preservation gives trace
  preservation (Wolf, §2.1).
* `QuantumCircuit.Circuit.isKrausCPTP_map` — such a circuit is a quantum channel.
* `QuantumCircuit.Circuit.trace_map` — such a circuit preserves the trace.
-/

open Matrix ManyBody

namespace QuantumCircuit

namespace Circuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

/-- Every gate, as a Kraus family under the interpretation `ev`, and every onsite family of the
circuit satisfies the predicate `P`. -/
def Forall (ev : Interpretation G)
    (P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      Circuit Γ G X Z → Prop
  | _, _, _, _, done _ => True
  | _, _, _, _, step L next => L.Forall ev P ∧ ∀ i, (next i).Forall ev P

/-- A circuit is unbranched when no continuation depends on the outcome of a layer. -/
def IsUnbranched : {X Z : S → Type} → Circuit Γ G X Z → Prop
  | _, _, done _ => True
  | _, _, step _ next => (∀ i j, next i = next j) ∧ ∀ i, (next i).IsUnbranched

omit [Fintype S] in
/-- The local property `P` passes to `c.append k` from `c` and every continuation. -/
theorem Forall.append (ev : Interpretation G)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop} {Z : S → Type} : {X Y : S → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] → [∀ s, Fintype (Y s)] →
    [∀ s, DecidableEq (Y s)] → {c : Circuit Γ G X Y} → {k : c.Index → Circuit Γ G Y Z} →
    c.Forall ev P → (∀ p, (k p).Forall ev P) → (c.append k).Forall ev P
  | _, _, i₁, i₂, i₃, i₄, done _, _, _, hk => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    exact hk ()
  | _, _, _, _, _, _, step _ next, _, hc, hk =>
    ⟨hc.1, fun i ↦ Forall.append ev (c := next i) (hc.2 i) fun j ↦ hk ⟨i, j⟩⟩

omit [Fintype S] in
theorem Forall.comp (ev : Interpretation G)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop} {X Y Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    {c : Circuit Γ G X Y} {c' : Circuit Γ G Y Z} (hc : c.Forall ev P) (hc' : c'.Forall ev P) :
    (c.comp c').Forall ev P :=
  hc.append ev fun _ ↦ hc'

omit [Fintype S] in
/-- A composition of unbranched circuits is unbranched. -/
theorem IsUnbranched.comp {Z : S → Type} : {X Y : S → Type} → {c : Circuit Γ G X Y} →
    {c' : Circuit Γ G Y Z} → c.IsUnbranched → c'.IsUnbranched → (c.comp c').IsUnbranched
  | _, _, done _, _, _, hc' => hc'
  | _, _, step _ next, c', hc, hc' =>
    ⟨fun i j ↦ by
      change (next i).comp c' = (next j).comp c'
      rw [hc.1 i j],
      fun i ↦ IsUnbranched.comp (c := next i) (hc.2 i) hc'⟩

/-- A circuit whose local families are trace-preserving has Heisenberg picture fixing the
identity. -/
theorem dual_one_of_forall (ev : Interpretation G) : {X Z : S → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] → [∀ s, Fintype (Z s)] →
    [∀ s, DecidableEq (Z s)] → (c : Circuit Γ G X Z) → c.Forall ev KrausFamily.IsTP →
      c.dual ev 1 = 1
  | _, _, i₁, i₂, i₃, i₄, done _, _ => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    change ∑ _ : Unit, ((1 : Matrix _ _ ℂ))ᴴ * 1 * 1 = 1
    simp
  | _, _, _, _, _, _, step L next, h => by
    rw [dual_step]
    have hnext : ∀ i, (next i).dual ev 1 = 1 := fun i ↦ dual_one_of_forall ev (next i) (h.2 i)
    simp_rw [hnext]
    exact L.dual_one ev h.1

variable {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)]

/-- A circuit whose gates and onsite families are trace-preserving is trace-preserving. -/
theorem isTP_krausFamily (ev : Interpretation G) (c : Circuit Γ G X Z)
    (h : c.Forall ev KrausFamily.IsTP) : (c.krausFamily ev).IsTP := by
  classical
  have := c.dual_one_of_forall ev h
  simp only [dual, Matrix.mul_one] at this
  change ∑ p : c.Index, (c.kraus ev p)ᴴ * c.kraus ev p = 1
  convert this using 2

/-- A circuit whose gates and onsite families are trace-preserving is a quantum channel. -/
theorem isKrausCPTP_map [∀ s, DecidableEq (Z s)] (ev : Interpretation G) (c : Circuit Γ G X Z)
    (h : c.Forall ev KrausFamily.IsTP) : IsKrausCPTP (c.map ev) :=
  KrausFamily.isKrausCPTP_map (c.isTP_krausFamily ev h)

/-- A circuit whose gates and onsite families are trace-preserving preserves the trace. -/
theorem trace_map (ev : Interpretation G) (c : Circuit Γ G X Z)
    (h : c.Forall ev KrausFamily.IsTP) (ρ : Matrix (Config X) (Config X) ℂ) :
    (c.map ev ρ).trace = ρ.trace :=
  KrausFamily.trace_map (c.isTP_krausFamily ev h) ρ

end Circuit

end QuantumCircuit
