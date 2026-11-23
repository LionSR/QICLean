/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Geometry.Subsets
import QICLean.Circuit.Core.Update
import QICLean.Circuit.Core.SingleBranch

/-!
# Party circuits

A *party circuit* is a composition of operations on a finite set of parties: gates, each on a
set of parties (its cell) and possibly changing the basis types there, and local operations,
each at one party or at every party at once. The parties are the sites, and the registers of a
party are the factors of its basis type; the memory is the tensor product `⊗_p ℂ^{X p}` of the
parties' spaces, in which the order of the factors of different parties carries no information,
so no exchange of factors and no framing by untouched registers is part of the syntax.

Registers are finite basis types, and operators are matrices on configurations: the systems
carry `Fintype` and `DecidableEq` instances wherever an operator is formed, and every operation
records those of its output. This is the standing hypothesis of the source, polynomial-PEPS
manuscript, `04-compression.tex`, lines 17–19 ("Every Hilbert space below is finite dimensional,
but an unspecified dimension has no size bound") and lines 23–24 ("At every time the memory is a
tensor product of the parties' current Hilbert spaces"). The set of parties is finite
(`[Fintype P]`), as every set of parties of the source is.

The meaning of a party circuit is a circuit on the geometry of all finite sets of parties
(`PartyCircuit.toCircuit`): a gate is the layer `Layer.gateAt` of its cell, a local operation the
layer `Layer.onsiteOpAt` or an onsite layer, a composition the composition of circuits. That
circuit is unbranched and sequential, and it has one branch when every gate has one outcome; the
*operator* of the party circuit is the Kraus operator of that branch. The gates along the
circuit, their number, the gate count and the participations are read off the syntax; the gate
count and the participations are those of the circuit (`PartyCircuit.gateCount_toCircuit`,
`PartyCircuit.participation_toCircuit`).

## Main definitions

* `QuantumCircuit.Party.PartyCircuit` — the syntax: `done`, `gate`, `localOp`, `localOps`,
  `comp`.
* `QuantumCircuit.Party.PartyCircuit.toCircuit`, `QuantumCircuit.Party.PartyCircuit.op` — the
  circuit and the operator.
* `QuantumCircuit.Party.PartyCircuit.IsAllowed` — contractive operations and gates satisfying a
  condition.
* `QuantumCircuit.Party.PartyCircuit.gateLocations`, `participants`, `gates`, `gateCells`,
  `numGates`, `gateCount`, `participation`, `participationCount`, `ForallGate` — the gates and
  their counts.

## Main results

* `QuantumCircuit.Party.PartyCircuit.isSingle_toCircuit`,
  `QuantumCircuit.Party.PartyCircuit.isSequential_toCircuit` — one branch, one operation per
  step.
* `QuantumCircuit.Party.PartyCircuit.op_comp`, `op_gate`, `op_localOp`, `op_localOps` — the
  operator, constructor by constructor.
* `QuantumCircuit.Party.PartyCircuit.norm_op_le_one` — an allowed party circuit is a
  contraction.
* `QuantumCircuit.Party.PartyCircuit.gateCount_toCircuit`,
  `QuantumCircuit.Party.PartyCircuit.participation_toCircuit` — the counts of the circuit.
* `QuantumCircuit.Party.PartyCircuit.gateCount_eq_numGates`,
  `QuantumCircuit.Party.PartyCircuit.participation_eq_participationCount` — when no gate is
  private, every gate is counted.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1, `04-compression.tex`, lines 17–36.
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit

/-- A gate together with its cell and its input and output systems: one entry of the list of
gates of a party circuit. -/
abbrev GateOccurrence {S : Type} (G : Finset S → (S → Type) → (S → Type) → Type 1) : Type 1 :=
  Σ (D : Finset S) (X Y : S → Type), G D X Y

namespace Party

/-- A party circuit from the system `X` to the system `Y`, with gates of the family `G`. Source:
`04-compression.tex`, lines 21–36. Each operation records the `Fintype` and `DecidableEq`
instances of its output system. -/
inductive PartyCircuit {P : Type} (G : Finset P → (P → Type) → (P → Type) → Type 1) :
    (P → Type) → (P → Type) → Type 1
  /-- The empty circuit. -/
  | done (X : P → Type) : PartyCircuit G X X
  /-- One gate `g` on the cell `D`, from `X` to a system `Y` that agrees with `X` outside `D`;
  the other parties are spectators. The cell may be empty. -/
  | gate {X Y : P → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (D : Finset P)
      (hY : ∀ s ∉ D, Y s = X s) (g : G D X Y) : PartyCircuit G X Y
  /-- One local operation `A` of the party `p`, from `X p` to `Y p`, the identity at the other
  parties. -/
  | localOp {X Y : P → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (p : P)
      (hY : ∀ s ≠ p, Y s = X s) (A : Matrix (Y p) (X p) ℂ) : PartyCircuit G X Y
  /-- The local operations `A p` of every party `p` at once. -/
  | localOps {X Y : P → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
      (A : ∀ p, Matrix (Y p) (X p) ℂ) : PartyCircuit G X Y
  /-- Composition, in chronological order: first `c`, then `c'`. -/
  | comp {X Y Z : P → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
      (c : PartyCircuit G X Y) (c' : PartyCircuit G Y Z) : PartyCircuit G X Z

variable {P : Type} [Fintype P] [DecidableEq P]

namespace PartyCircuit

variable {G : Finset P → (P → Type) → (P → Type) → Type 1} [GateFamily G] {X Y Z : P → Type}

/-! ### The circuit and the operator -/

/-- The circuit of a party circuit, on the geometry of all finite sets of parties: a gate is the
layer of its cell, a local operation an onsite layer, a composition the composition of the
circuits. -/
def toCircuit : {X Y : P → Type} → [∀ s, DecidableEq (X s)] → PartyCircuit G X Y →
    Circuit (Geometry.subsets P) G X Y
  | _, _, _, done X => Circuit.done X
  | _, _, _, gate D hY g => Circuit.ofLayer (Layer.gateAt (Γ := Geometry.subsets P) D hY g)
  | _, _, _, localOp p hY A => Circuit.ofLayer (Layer.onsiteOpAt p hY A)
  | _, _, _, localOps A => Circuit.ofLayer (Layer.ofOnsite fun p ↦ KrausFamily.single (A p))
  | _, _, _, comp c c' => (toCircuit c).comp (toCircuit c')

omit [Fintype P] in
/-- The circuit of a party circuit is unbranched. -/
theorem isUnbranched_toCircuit : {X Y : P → Type} → [∀ s, DecidableEq (X s)] →
    (c : PartyCircuit G X Y) → (toCircuit c).IsUnbranched
  | _, _, _, done _ => trivial
  | _, _, _, gate _ _ _ => Circuit.isUnbranched_ofLayer _
  | _, _, _, localOp _ _ _ => Circuit.isUnbranched_ofLayer _
  | _, _, _, localOps _ => Circuit.isUnbranched_ofLayer _
  | _, _, _, comp c c' => (isUnbranched_toCircuit c).comp (isUnbranched_toCircuit c')

omit [Fintype P] in
/-- **One operation per step.** Every layer of the circuit of a party circuit has at most one
cell, and a layer with a cell is the identity at the other parties. -/
theorem isSequential_toCircuit : {X Y : P → Type} → [∀ s, DecidableEq (X s)] →
    (c : PartyCircuit G X Y) → (toCircuit c).IsSequential
  | _, _, _, done _ => trivial
  | _, _, _, gate _ hY g => Circuit.isSequential_ofLayer (Layer.isStep_gateAt _ hY g)
  | _, _, _, localOp p hY A => Circuit.isSequential_ofLayer (Layer.isStep_onsiteOpAt p hY A)
  | _, _, _, localOps _ => Circuit.isSequential_ofLayer (Layer.isStep_ofOnsite _)
  | _, _, _, comp c c' => (isSequential_toCircuit c).comp (isSequential_toCircuit c')

omit [Fintype P] in
/-- When every gate has one outcome, the circuit of a party circuit has one branch. -/
theorem isSingle_toCircuit [GateFamily.UniqueOutcome G] : {X Y : P → Type} →
    [∀ s, DecidableEq (X s)] → (c : PartyCircuit G X Y) → (toCircuit c).IsSingle
  | _, _, _, done _ => trivial
  | _, _, _, gate _ _ _ =>
    Circuit.isSingle_ofLayer _ fun _ ↦ ⟨inferInstanceAs (Unique Unit)⟩
  | _, _, _, localOp _ _ _ =>
    ⟨⟨fun b ↦ absurd b.2 (Finset.notMem_empty _), fun _ ↦ ⟨inferInstanceAs (Unique Unit)⟩⟩,
      fun _ ↦ trivial⟩
  | _, _, _, localOps _ =>
    ⟨⟨fun b ↦ absurd b.2 (Finset.notMem_empty _), fun _ ↦ ⟨inferInstanceAs (Unique Unit)⟩⟩,
      fun _ ↦ trivial⟩
  | _, _, _, comp c c' => (isSingle_toCircuit c).comp (isSingle_toCircuit c')

section Unique

variable [GateFamily.UniqueOutcome G]

/-- The operator of a party circuit: the Kraus operator of the unique branch of its circuit. -/
noncomputable def op (ev : Interpretation G) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (c : PartyCircuit G X Y) : Matrix (Config Y) (Config X) ℂ :=
  (toCircuit c).singleOp ev (isSingle_toCircuit c)

section Op

variable (ev : Interpretation G) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- The empty party circuit applies the identity. -/
@[simp] theorem op_done : (done X : PartyCircuit G X X).op ev = 1 :=
  rfl

/-- The operator of a composition is the product of the operators, the first on the right. -/
@[simp] theorem op_comp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (c : PartyCircuit G X Y)
    (c' : PartyCircuit G Y Z) : (comp c c').op ev = c'.op ev * c.op ev :=
  Circuit.singleOp_comp ev _ _ (isSingle_toCircuit c) (isSingle_toCircuit c')

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

omit [GateFamily.UniqueOutcome G] in
/-- The operator of a circuit of one layer with one branch is a Kraus operator of the layer. -/
private theorem exists_singleOp_ofLayer (L : Layer (Geometry.subsets P) G X Y)
    (h : (Circuit.ofLayer L).IsSingle) : ∃ i, (Circuit.ofLayer L).singleOp ev h = L.kraus ev i :=
  let ⟨u⟩ := h.nonempty_unique_index
  ⟨u.default.1, Circuit.singleOp_ofLayer ev L h _⟩

/-- The operator of one gate is the placement `M ⊗ 1` of its matrix between the two systems. -/
@[simp] theorem op_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : G D X Y) :
    (gate D hY g).op ev = placeBetween D hY (ev g (GateFamily.UniqueOutcome.outcome g)) := by
  obtain ⟨i, hi⟩ := exists_singleOp_ofLayer ev (Layer.gateAt (Γ := Geometry.subsets P) D hY g)
    (isSingle_toCircuit (gate D hY g))
  have hk := Layer.kraus_gateAt (Γ := Geometry.subsets P) ev D hY g i
  have ho : i.1 ⟨D, Finset.mem_singleton_self D⟩ = GateFamily.UniqueOutcome.outcome g :=
    GateFamily.UniqueOutcome.eq_outcome _
  rw [ho] at hk
  exact hi.trans hk

/-- The operator of one local operation is its placement at the party. -/
@[simp] theorem op_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s) (A : Matrix (Y p) (X p) ℂ) :
    (localOp (G := G) p hY A).op ev =
      placeBetween {p} (fun s hs ↦ hY s (Finset.notMem_singleton.mp hs))
        (A.submatrix (fun y ↦ y ⟨p, Finset.mem_singleton_self p⟩)
          (fun x ↦ x ⟨p, Finset.mem_singleton_self p⟩)) := by
  obtain ⟨i, hi⟩ := exists_singleOp_ofLayer ev (Layer.onsiteOpAt p hY A)
    (isSingle_toCircuit (localOp (G := G) p hY A))
  exact hi.trans (Layer.kraus_onsiteOpAt ev p hY A i)

/-- The operator of local operations at every party is their Kronecker product. -/
@[simp] theorem op_localOps (A : ∀ p, Matrix (Y p) (X p) ℂ) :
    (localOps (G := G) A).op ev = piKronecker A := by
  obtain ⟨i, hi⟩ := exists_singleOp_ofLayer ev
    (Layer.ofOnsite (Γ := Geometry.subsets P) (G := G) fun p ↦ KrausFamily.single (A p))
    (isSingle_toCircuit (localOps (G := G) A))
  exact hi.trans (Layer.kraus_ofOnsite ev _ i)

end Op

/-! ### Allowed circuits -/

/-- A party circuit is allowed when its local operations and gates are contractions and its
gates satisfy the condition `A` on their syntax. Source: `04-compression.tex`, lines 28
and 32–35. -/
def IsAllowed (ev : Interpretation G)
    (A : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G D X Y → Prop) :
    {X Y : P → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      PartyCircuit G X Y → Prop
  | _, _, _, _, done _ => True
  | _, _, _, _, gate _ _ g => ‖ev g (GateFamily.UniqueOutcome.outcome g)‖ ≤ 1 ∧ A g
  | _, _, _, _, localOp _ _ U => ‖U‖ ≤ 1
  | _, _, _, _, localOps U => ∀ p, ‖U p‖ ≤ 1
  | _, _, _, _, comp c c' => c.IsAllowed ev A ∧ c'.IsAllowed ev A

section Allowed

variable (ev : Interpretation G)
  {A : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G D X Y → Prop}

/-- The identity matrix is a trace-nonincreasing single family. -/
private theorem isTraceNonincreasing_single_one {α : Type} [Fintype α] [DecidableEq α] :
    (KrausFamily.single (1 : Matrix α α ℂ)).IsTraceNonincreasing :=
  (KrausFamily.isUnitary_single (one_mem _)).isTP.isTraceNonincreasing

omit [Fintype P] in
/-- The local operations and gates of the circuit of an allowed party circuit are
trace-nonincreasing. -/
theorem IsAllowed.forall_toCircuit : {X Y : P → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → {c : PartyCircuit G X Y} → c.IsAllowed ev A →
      (toCircuit c).Forall ev KrausFamily.IsTraceNonincreasing
  | _, _, _, _, done _, _ => trivial
  | _, _, _, _, gate D hY g, h => by
    refine ⟨?_, fun _ ↦ trivial⟩
    let : Unique (GateFamily.Outcome g) := (GateFamily.UniqueOutcome.nonempty_unique g).some
    exact Layer.forall_gateAt (Γ := Geometry.subsets P) (P := KrausFamily.IsTraceNonincreasing)
      ev isTraceNonincreasing_single_one D hY g
      ((KrausFamily.isTraceNonincreasing_iff_norm_le_one
        (⟨GateFamily.Outcome g, ev g⟩ : KrausFamily (RegionConfig _ D) (RegionConfig _ D))).mpr
        h.1)
  | _, _, _, _, localOp p hY U, h => by
    refine ⟨?_, fun _ ↦ trivial⟩
    exact Layer.forall_onsiteOpAt (P := KrausFamily.IsTraceNonincreasing) ev
      isTraceNonincreasing_single_one p hY U ((KrausFamily.isTraceNonincreasing_single_iff U).mpr h)
  | _, _, _, _, localOps U, h =>
    ⟨⟨fun b ↦ absurd b.2 (Finset.notMem_empty _),
      fun s ↦ (KrausFamily.isTraceNonincreasing_single_iff (U s.1)).mpr (h s.1)⟩,
      fun _ ↦ trivial⟩
  | _, _, _, _, comp _ _, h => (IsAllowed.forall_toCircuit h.1).comp ev
      (IsAllowed.forall_toCircuit h.2)

/-- **An allowed party circuit is a contraction.** Source: `04-compression.tex`, line 28
("Gates are linear contractions") and lines 215–216 (products of contractions). -/
theorem norm_op_le_one [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
    {c : PartyCircuit G X Y} (hc : c.IsAllowed ev A) : ‖c.op ev‖ ≤ 1 :=
  Circuit.norm_singleOp_le_one ev _ _ hc.forall_toCircuit

end Allowed

end Unique

/-! ### Gates along the circuit and their counts -/

section Counts

/-- The gate occurrences of a party circuit, kept distinct even when two gates coincide: one for
each gate, none for a local operation, and those of both parts for a composition. -/
def gateLocations : {X Y : P → Type} → PartyCircuit G X Y → Type
  | _, _, done _ => Empty
  | _, _, gate _ _ _ => Unit
  | _, _, localOp _ _ _ => Empty
  | _, _, localOps _ => Empty
  | _, _, comp c c' => gateLocations c ⊕ gateLocations c'

/-- A party circuit has finitely many gate occurrences. -/
instance instFintypeGateLocations : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    Fintype (gateLocations c)
  | _, _, done _ => inferInstanceAs (Fintype Empty)
  | _, _, gate _ _ _ => inferInstanceAs (Fintype Unit)
  | _, _, localOp _ _ _ => inferInstanceAs (Fintype Empty)
  | _, _, localOps _ => inferInstanceAs (Fintype Empty)
  | _, _, comp c c' =>
    letI := instFintypeGateLocations c
    letI := instFintypeGateLocations c'
    inferInstanceAs (Fintype (gateLocations c ⊕ gateLocations c'))

/-- The parties taking part in a gate occurrence: its cell. Source: `04-compression.tex`,
lines 25–27. -/
def participants : {X Y : P → Type} → (c : PartyCircuit G X Y) → gateLocations c → Finset P
  | _, _, done _ => Empty.elim
  | _, _, gate D _ _ => fun _ ↦ D
  | _, _, localOp _ _ _ => Empty.elim
  | _, _, localOps _ => Empty.elim
  | _, _, comp c c' => Sum.elim (participants c) (participants c')

/-- The gates of a party circuit, with their cells and systems, in chronological order. -/
def gates : {X Y : P → Type} → PartyCircuit G X Y → List (GateOccurrence G)
  | _, _, done _ => []
  | X, Y, gate D _ g => [⟨D, X, Y, g⟩]
  | _, _, localOp _ _ _ => []
  | _, _, localOps _ => []
  | _, _, comp c c' => gates c ++ gates c'

/-- The cells of the gates of a party circuit, in chronological order. -/
def gateCells : {X Y : P → Type} → PartyCircuit G X Y → List (Finset P)
  | _, _, done _ => []
  | _, _, gate D _ _ => [D]
  | _, _, localOp _ _ _ => []
  | _, _, localOps _ => []
  | _, _, comp c c' => gateCells c ++ gateCells c'

/-- The number of gates of a party circuit, private ones and those on the empty cell
included. Source: `04-compression.tex`, lines 199–202. -/
def numGates : {X Y : P → Type} → PartyCircuit G X Y → ℕ
  | _, _, done _ => 0
  | _, _, gate _ _ _ => 1
  | _, _, localOp _ _ _ => 0
  | _, _, localOps _ => 0
  | _, _, comp c c' => numGates c + numGates c'

/-- The gate count of a party circuit: the sum of the costs of its cells, that is, the number of
its gates that are not private (a cell of one party costs nothing, any other cell, the empty
one included, costs `1`). -/
def gateCount : {X Y : P → Type} → PartyCircuit G X Y → ℕ
  | _, _, done _ => 0
  | _, _, gate D _ _ => (Geometry.subsets P).cost D
  | _, _, localOp _ _ _ => 0
  | _, _, localOps _ => 0
  | _, _, comp c c' => gateCount c + gateCount c'

/-- The participation of the party `p`: the number of gates that are not private and contain
`p`. -/
def participation (p : P) : {X Y : P → Type} → PartyCircuit G X Y → ℕ
  | _, _, done _ => 0
  | _, _, gate D _ _ => if p ∈ D ∧ 0 < (Geometry.subsets P).cost D then 1 else 0
  | _, _, localOp _ _ _ => 0
  | _, _, localOps _ => 0
  | _, _, comp c c' => participation p c + participation p c'

/-- The number of gates containing the party `p`, private ones included. Source:
`04-compression.tex`, lines 140–142. -/
def participationCount (p : P) : {X Y : P → Type} → PartyCircuit G X Y → ℕ
  | _, _, done _ => 0
  | _, _, gate D _ _ => if p ∈ D then 1 else 0
  | _, _, localOp _ _ _ => 0
  | _, _, localOps _ => 0
  | _, _, comp c c' => participationCount p c + participationCount p c'

/-- Every gate of the party circuit satisfies the condition `A` on its syntax. -/
def ForallGate (A : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄, G D X Y → Prop) :
    {X Y : P → Type} → PartyCircuit G X Y → Prop
  | _, _, done _ => True
  | _, _, gate _ _ g => A g
  | _, _, localOp _ _ _ => True
  | _, _, localOps _ => True
  | _, _, comp c c' => ForallGate A c ∧ ForallGate A c'

omit [Fintype P] [DecidableEq P] [GateFamily G] in
/-- The cells along a party circuit are those of its gates. -/
theorem gateCells_eq_map_gates : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    c.gateCells = c.gates.map Sigma.fst
  | _, _, done _ => rfl
  | _, _, gate _ _ _ => rfl
  | _, _, localOp _ _ _ => rfl
  | _, _, localOps _ => rfl
  | _, _, comp c c' => by
    rw [gateCells, gates, List.map_append, gateCells_eq_map_gates c,
      gateCells_eq_map_gates c']

omit [Fintype P] [DecidableEq P] [GateFamily G] in
/-- The number of gates is the length of the list of gates. -/
theorem length_gates : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    c.gates.length = c.numGates
  | _, _, done _ => rfl
  | _, _, gate _ _ _ => rfl
  | _, _, localOp _ _ _ => rfl
  | _, _, localOps _ => rfl
  | _, _, comp c c' => by rw [gates, List.length_append, length_gates c, length_gates c']; rfl

omit [Fintype P] [DecidableEq P] [GateFamily G] in
/-- The number of gates is the number of gate occurrences. -/
theorem card_gateLocations : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    Fintype.card c.gateLocations = c.numGates
  | _, _, done _ => rfl
  | _, _, gate _ _ _ => rfl
  | _, _, localOp _ _ _ => rfl
  | _, _, localOps _ => rfl
  | _, _, comp c c' =>
    (Fintype.card_sum (α := gateLocations c) (β := gateLocations c')).trans
      (congrArg₂ _ (card_gateLocations c) (card_gateLocations c'))

omit [Fintype P] [GateFamily G] in
/-- The gate count is at most the number of gates. -/
theorem gateCount_le_numGates : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    c.gateCount ≤ c.numGates
  | _, _, done _ => le_rfl
  | _, _, gate D _ _ => Geometry.subsets_cost_le_one D
  | _, _, localOp _ _ _ => le_rfl
  | _, _, localOps _ => le_rfl
  | _, _, comp c c' => Nat.add_le_add (gateCount_le_numGates c) (gateCount_le_numGates c')

omit [Fintype P] [GateFamily G] in
/-- When no gate acts on exactly one party, the gate count is the number of gates. -/
theorem gateCount_eq_numGates : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    c.ForallGate (fun D _ _ _ ↦ D.card ≠ 1) → c.gateCount = c.numGates
  | _, _, done _, _ => rfl
  | _, _, gate _ _ _, h => ite_eq_right h
  | _, _, localOp _ _ _, _ => rfl
  | _, _, localOps _, _ => rfl
  | _, _, comp c c', h =>
    congrArg₂ (· + ·) (gateCount_eq_numGates c h.1) (gateCount_eq_numGates c' h.2)

omit [Fintype P] [GateFamily G] in
/-- When no gate acts on exactly one party, the participation of a party is the number of gates
containing it. -/
theorem participation_eq_participationCount (p : P) : {X Y : P → Type} →
    (c : PartyCircuit G X Y) → c.ForallGate (fun D _ _ _ ↦ D.card ≠ 1) →
      c.participation p = c.participationCount p
  | _, _, done _, _ => rfl
  | _, _, gate D _ _, h => by
    simp only [participation, participationCount]
    exact if_congr (and_iff_left ((Geometry.subsets_cost_pos_iff _).mpr h)) rfl rfl
  | _, _, localOp _ _ _, _ => rfl
  | _, _, localOps _, _ => rfl
  | _, _, comp c c', h => congrArg₂ (· + ·) (participation_eq_participationCount p c h.1)
      (participation_eq_participationCount p c' h.2)

omit [Fintype P] [GateFamily G] in
/-- One gate on the empty cell is counted: the empty cell costs `1`. -/
theorem gateCount_gate_empty [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (hY : ∀ s ∉ (∅ : Finset P), Y s = X s) (g : G ∅ X Y) : (gate ∅ hY g).gateCount = 1 :=
  rfl

/-- The cost of the circuit of one layer is the cost of the layer. -/
private theorem total_ofLayer [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (f : ∀ ⦃X Y : P → Type⦄, Layer (Geometry.subsets P) G X Y → ℕ)
    (L : Layer (Geometry.subsets P) G X Y) : (Circuit.ofLayer L).total f = f L := by
  change f L + Finset.univ.sup (fun _ ↦ 0) = f L
  exact (congrArg (f L + ·) ((Finset.sup_eq_bot_iff _ _).mpr fun _ _ ↦ rfl)).trans (add_zero _)

/-- The gate count of a party circuit is the gate count of its circuit. -/
theorem gateCount_toCircuit [GateFamily.UniqueOutcome G] : {X Y : P → Type} →
    [∀ s, DecidableEq (X s)] → (c : PartyCircuit G X Y) → (toCircuit c).gateCount = c.gateCount
  | _, _, _, done _ => rfl
  | _, _, _, gate D hY g =>
    (total_ofLayer _ _).trans (Layer.gateCount_gateAt (Γ := Geometry.subsets P) D hY g)
  | _, _, _, localOp p hY A => (total_ofLayer _ _).trans (Layer.gateCount_onsiteOpAt p hY A)
  | _, _, _, localOps _ => (total_ofLayer _ _).trans (by
      rw [Layer.gateCount, Layer.cellCost]
      exact Fintype.sum_eq_zero _ fun b ↦ absurd b.2 (Finset.notMem_empty _))
  | _, _, _, comp c c' =>
    (Circuit.total_comp_of_isUnbranched _ (isUnbranched_toCircuit c)
      ((isSingle_toCircuit c).nonempty_unique_index.map fun u ↦ u.default) _).trans
      (congrArg₂ (· + ·) (gateCount_toCircuit c) (gateCount_toCircuit c'))

/-- The participation of a party in a party circuit is its participation in the circuit. -/
theorem participation_toCircuit [GateFamily.UniqueOutcome G] (p : P) : {X Y : P → Type} →
    [∀ s, DecidableEq (X s)] → (c : PartyCircuit G X Y) →
      (toCircuit c).participation p = c.participation p
  | _, _, _, done _ => rfl
  | _, _, _, gate D hY g =>
    (total_ofLayer _ _).trans (Layer.meets_gateAt (Γ := Geometry.subsets P) D hY g p)
  | _, _, _, localOp q hY A => (total_ofLayer _ _).trans (Layer.meets_onsiteOpAt q hY A p)
  | _, _, _, localOps _ => (total_ofLayer _ _).trans (by
      rw [Layer.meets, Layer.cellCost]
      exact Fintype.sum_eq_zero _ fun b ↦ absurd b.2 (Finset.notMem_empty _))
  | _, _, _, comp c c' =>
    (Circuit.total_comp_of_isUnbranched _ (isUnbranched_toCircuit c)
      ((isSingle_toCircuit c).nonempty_unique_index.map fun u ↦ u.default) _).trans
      (congrArg₂ (· + ·) (participation_toCircuit p c) (participation_toCircuit p c'))

end Counts

end PartyCircuit

end Party

end QuantumCircuit
