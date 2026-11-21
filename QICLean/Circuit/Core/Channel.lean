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
* `QuantumCircuit.Circuit.isUnbranched_ofLayer` — the circuit of one layer is unbranched.
* `QuantumCircuit.Circuit.isTP_krausFamily` — local trace preservation gives trace
  preservation (Wolf, §2.1).
* `QuantumCircuit.Circuit.isTraceNonincreasing_krausFamily`,
  `QuantumCircuit.Circuit.dual_one_le_of_forall`, `QuantumCircuit.Circuit.trace_map_le` —
  local trace nonincrease gives trace nonincrease and a sub-unital Heisenberg dual.
* `QuantumCircuit.Circuit.isKrausCPTP_map` — such a circuit is a quantum channel.
* `QuantumCircuit.Circuit.trace_map` — such a circuit preserves the trace.
* `QuantumCircuit.Circuit.nonempty_unique_index`,
  `QuantumCircuit.Circuit.dual_eq_of_subsingleton` — a circuit of local families with one index
  each has one branch, and its Heisenberg picture is conjugation by its Kraus operator.
-/

open Matrix ManyBody

open scoped ComplexOrder MatrixOrder

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

omit [Fintype S] in
/-- A local property passes to every property it implies. -/
theorem Forall.mono {ev : Interpretation G}
    {P Q : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hPQ : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (K : KrausFamily α β), P K → Q K) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      {c : Circuit Γ G X Z} → c.Forall ev P → c.Forall ev Q
  | _, _, _, _, done _, _ => trivial
  | _, _, _, _, step _ next, h => ⟨h.1.mono hPQ, fun i ↦ Forall.mono hPQ (c := next i) (h.2 i)⟩

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

omit [Fintype S] in
/-- The circuit of one layer is unbranched. -/
theorem isUnbranched_ofLayer {X Y : S → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (L : Layer Γ G X Y) : (ofLayer L).IsUnbranched :=
  ⟨fun _ _ ↦ rfl, fun _ ↦ trivial⟩

omit [Fintype S] in
/-- A circuit whose gates and onsite families each have a unique Kraus index has a unique
branch. A unitary local family has a unique index, so this applies to unitary circuits. -/
theorem nonempty_unique_index (ev : Interpretation G) : {X Z : S → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] → {c : Circuit Γ G X Z} →
      c.Forall ev (fun K ↦ Nonempty (Unique K.Index)) → Nonempty (Unique c.Index)
  | _, _, _, _, done _, _ => ⟨inferInstanceAs (Unique Unit)⟩
  | _, _, _, _, step L next, h => by
    obtain ⟨⟨hg, ho⟩, hn⟩ := (h : L.Forall ev _ ∧ ∀ i, (next i).Forall ev _)
    have i₁ : ∀ b : L.cells, Unique (GateFamily.Outcome (L.gate b)) := fun b ↦ (hg b).some
    have i₂ : ∀ s : L.Free, Unique (L.onsite s).Index := fun s ↦ (ho s).some
    let u : Unique L.Index :=
      { default := (fun b ↦ (i₁ b).default, fun s ↦ (i₂ s).default)
        uniq := fun ⟨f, g⟩ ↦ Prod.ext (funext fun b ↦ (i₁ b).uniq (f b))
          (funext fun s ↦ (i₂ s).uniq (g s)) }
    have hu := fun i ↦ (nonempty_unique_index ev (hn i)).some
    refine ⟨{ default := ⟨default, (hu default).default⟩, uniq := ?_ }⟩
    rintro ⟨i, j⟩
    obtain rfl := u.uniq i
    exact Sigma.ext rfl (heq_of_eq ((hu default).uniq j))

/-- The Heisenberg picture of a circuit with a single branch `p` is conjugation by its Kraus
operator. -/
theorem dual_eq_of_subsingleton (ev : Interpretation G) {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] (c : Circuit Γ G X Z) [Subsingleton c.Index]
    (p : c.Index) (A : Matrix (Config Z) (Config Z) ℂ) :
    c.dual ev A = (c.kraus ev p)ᴴ * A * c.kraus ev p :=
  Fintype.sum_subsingleton _ p

/-- A circuit whose local families are trace-preserving has Heisenberg picture fixing the
identity. -/
theorem dual_one_of_forall (ev : Interpretation G) : {X Z : S → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] → [∀ s, Fintype (Z s)] →
    [∀ s, DecidableEq (Z s)] → (c : Circuit Γ G X Z) → c.Forall ev KrausFamily.IsTP →
      c.dual ev 1 = 1
  | _, _, i₁, i₂, i₃, i₄, done _, _ => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    exact dual_done ev 1
  | _, _, _, _, _, _, step L next, h => by
    rw [dual_step]
    have hnext : ∀ i, (next i).dual ev 1 = 1 := fun i ↦ dual_one_of_forall ev (next i) (h.2 i)
    simp_rw [hnext]
    exact L.dual_one ev h.1

/-- Local trace nonincrease makes the Heisenberg picture sub-unital, including circuits
whose continuation depends on the preceding Kraus outcome. -/
theorem dual_one_le_of_forall (ev : Interpretation G) : {X Z : S → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] → [∀ s, Fintype (Z s)] →
    [∀ s, DecidableEq (Z s)] → (c : Circuit Γ G X Z) →
      c.Forall ev KrausFamily.IsTraceNonincreasing → c.dual ev 1 ≤ 1
  | _, _, i₁, i₂, i₃, i₄, done _, _ => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    rw [dual_done]
  | _, _, _, _, _, _, step L next, h => by
    rw [dual_step]
    calc
      _ ≤ ∑ i, (L.kraus ev i)ᴴ * 1 * L.kraus ev i := by
        apply Finset.sum_le_sum
        intro i _
        apply Matrix.le_iff.mpr
        have hn := Matrix.le_iff.mp (dual_one_le_of_forall ev (next i) (h.2 i))
        simpa only [Matrix.mul_sub, Matrix.sub_mul] using
          hn.conjTranspose_mul_mul_same (L.kraus ev i)
      _ ≤ 1 := L.dual_one_le ev h.1

variable {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)]

/-- The Heisenberg image of the identity is the circuit Kraus effect. -/
theorem dual_one_eq_effect [∀ s, DecidableEq (Z s)]
    (ev : Interpretation G) (c : Circuit Γ G X Z) :
    c.dual ev 1 = (c.krausFamily ev).effect := by
  simp only [dual, krausFamily, KrausFamily.effect, Matrix.mul_one]
  congr 1

/-- A circuit whose gates and onsite families are trace-preserving is trace-preserving. -/
theorem isTP_krausFamily (ev : Interpretation G) (c : Circuit Γ G X Z)
    (h : c.Forall ev KrausFamily.IsTP) : (c.krausFamily ev).IsTP := by
  classical
  rw [KrausFamily.isTP_iff_effect_eq_one, ← dual_one_eq_effect]
  exact c.dual_one_of_forall ev h

/-- A circuit whose gates and onsite families are trace-preserving is a quantum channel. -/
theorem isKrausCPTP_map [∀ s, DecidableEq (Z s)] (ev : Interpretation G) (c : Circuit Γ G X Z)
    (h : c.Forall ev KrausFamily.IsTP) : IsKrausCPTP (c.map ev) :=
  KrausFamily.isKrausCPTP_map (c.isTP_krausFamily ev h)

/-- A circuit whose gates and onsite families are trace-preserving preserves the trace. -/
theorem trace_map (ev : Interpretation G) (c : Circuit Γ G X Z)
    (h : c.Forall ev KrausFamily.IsTP) (ρ : Matrix (Config X) (Config X) ℂ) :
    (c.map ev ρ).trace = ρ.trace :=
  KrausFamily.trace_map (c.isTP_krausFamily ev h) ρ

/-- Local trace nonincrease gives trace nonincrease of the full branching Kraus family. -/
theorem isTraceNonincreasing_krausFamily (ev : Interpretation G) (c : Circuit Γ G X Z)
    (h : c.Forall ev KrausFamily.IsTraceNonincreasing) :
    (c.krausFamily ev).IsTraceNonincreasing := by
  classical
  rw [KrausFamily.IsTraceNonincreasing, ← dual_one_eq_effect]
  exact c.dual_one_le_of_forall ev h

/-- A locally trace-nonincreasing circuit decreases the trace of positive semidefinite
inputs; this does not assert sub-unitality of its Schrödinger map. -/
theorem trace_map_le (ev : Interpretation G) (c : Circuit Γ G X Z)
    (h : c.Forall ev KrausFamily.IsTraceNonincreasing)
    {ρ : Matrix (Config X) (Config X) ℂ} (hρ : ρ.PosSemidef) :
    (c.map ev ρ).trace ≤ ρ.trace :=
  KrausFamily.trace_map_le (c.isTraceNonincreasing_krausFamily ev h) hρ

end Circuit

end QuantumCircuit
