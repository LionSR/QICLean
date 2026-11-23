/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Channel
import QICLean.Circuit.Core.Cost
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Circuits with one branch, conditions on gates, and the cells along a branch

A circuit whose gates each have one outcome and whose onsite families each have one member has
exactly one branch (`Circuit.IsSingle`). Its Kraus operator at that branch, `Circuit.singleOp`, is
the operator the circuit applies: the product of the matrices of its layers. It is multiplicative
under composition, and it is a contraction in the operator norm when every local family is
trace-nonincreasing. The condition `IsSingle` reads only the outcome and index types, so it
needs neither an interpretation of the gates nor finiteness of the basis types. A gate family
whose gates have one outcome each (`GateFamily.UniqueOutcome`), such as a family of gates given
by one matrix, gives circuits of one branch as soon as the onsite families have one member; a
family of one member is trace-nonincreasing exactly when its operator is a contraction.

A condition on the gates themselves, as syntax rather than as matrices, holds on a circuit when
every gate of every layer on every branch satisfies it (`Circuit.ForallGate'`). A condition that
evaluates a gate needs the finiteness and decidability of its basis types; `Circuit.ForallGate`
passes them to it.

The cells used along a branch, layer by layer, form the list `Circuit.gateCells`. Along any
branch the sum of their costs is at most the gate count, with equality for an unbranched circuit;
likewise for the number of cells of positive cost containing a site and the participation of the
site. The length of the list is not the gate count in general: cells of cost zero are listed.

## Main definitions

* `QuantumCircuit.GateFamily.UniqueOutcome` — gate families whose gates have one outcome.
* `QuantumCircuit.Circuit.IsSingle` — every gate has one outcome and every onsite family one
  member.
* `QuantumCircuit.Circuit.singleOp` — the Kraus operator of the unique branch.
* `QuantumCircuit.Circuit.ForallGate'`, `QuantumCircuit.Circuit.ForallGate` — every gate satisfies
  a condition on its syntax, without or with the instances of its basis types.
* `QuantumCircuit.Circuit.gateCells`, `QuantumCircuit.Circuit.gateSites` — the cells used along a
  branch, and their sites.

## Main results

* `KrausFamily.isTraceNonincreasing_iff_norm_le_one`, `KrausFamily.isTraceNonincreasing_single_iff`
  — a family of one member is trace-nonincreasing exactly when its operator is a contraction.
* `QuantumCircuit.Circuit.IsSingle.nonempty_unique_index` — one branch.
* `QuantumCircuit.Circuit.isSingle_ofLayer` — one layer of gates with one outcome.
* `QuantumCircuit.Circuit.isSingle_iff_forall` — `IsSingle` as a local property.
* `QuantumCircuit.Circuit.singleOp_eq_kraus`, `QuantumCircuit.Circuit.singleOp_done`,
  `QuantumCircuit.Circuit.singleOp_step`, `QuantumCircuit.Circuit.singleOp_ofLayer`,
  `QuantumCircuit.Circuit.singleOp_comp` — the operator, constructor by constructor.
* `QuantumCircuit.Circuit.norm_singleOp_le_one` — locally trace-nonincreasing circuits apply
  contractions.
* `QuantumCircuit.Circuit.sum_cost_gateCells_le`,
  `QuantumCircuit.Circuit.sum_cost_gateCells_eq_of_isUnbranched`,
  `QuantumCircuit.Circuit.participation_eq_of_isUnbranched` — costs along a branch.
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace QuantumCircuit

/-! ### Gate families with one outcome, and single operators -/

/-- A gate family whose every gate has exactly one outcome, as a gate given by one matrix has. -/
class GateFamily.UniqueOutcome {S : Type} (G : Finset S → (S → Type) → (S → Type) → Type 1)
    [GateFamily G] : Prop where
  /-- Every gate has exactly one outcome. -/
  nonempty_unique : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄ (g : G D X Y),
    Nonempty (Unique (GateFamily.Outcome g))

/-- The outcome of a gate of a family whose gates have one outcome. -/
noncomputable def GateFamily.UniqueOutcome.outcome {S : Type}
    {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] [GateFamily.UniqueOutcome G]
    {D : Finset S} {X Y : S → Type} (g : G D X Y) : GateFamily.Outcome g :=
  (GateFamily.UniqueOutcome.nonempty_unique g).some.default

/-- Every outcome of a gate of a family whose gates have one outcome is that outcome. -/
theorem GateFamily.UniqueOutcome.eq_outcome {S : Type}
    {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] [GateFamily.UniqueOutcome G]
    {D : Finset S} {X Y : S → Type} {g : G D X Y} (i : GateFamily.Outcome g) :
    i = GateFamily.UniqueOutcome.outcome g :=
  (GateFamily.UniqueOutcome.nonempty_unique g).some.uniq i

/-- A Kraus family with one member is trace-nonincreasing exactly when its operator is a
contraction in the operator norm. -/
theorem _root_.KrausFamily.isTraceNonincreasing_iff_norm_le_one {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] (K : KrausFamily α β) [Unique K.Index] :
    K.IsTraceNonincreasing ↔ ‖K.op default‖ ≤ 1 := by
  have heff : K.effect = (K.op default)ᴴ * K.op default := Fintype.sum_unique _
  rw [KrausFamily.IsTraceNonincreasing, heff, ← CStarAlgebra.norm_le_one_iff_of_nonneg _
    (posSemidef_conjTranspose_mul_self _).nonneg, l2_opNorm_conjTranspose_mul_self]
  constructor
  · intro h
    nlinarith [norm_nonneg (K.op default)]
  · intro h
    nlinarith [norm_nonneg (K.op default)]

/-- The family of one operator is trace-nonincreasing exactly when the operator is a
contraction. -/
theorem _root_.KrausFamily.isTraceNonincreasing_single_iff {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] (V : Matrix β α ℂ) : (KrausFamily.single V).IsTraceNonincreasing ↔ ‖V‖ ≤ 1 :=
  letI : Unique (KrausFamily.single V).Index := inferInstanceAs (Unique Unit)
  (KrausFamily.single V).isTraceNonincreasing_iff_norm_le_one

namespace Circuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {X Y Z : S → Type}

/-! ### Circuits with one branch -/

/-- Every gate of the circuit has a unique outcome and every onsite family a unique member. -/
def IsSingle : {X Z : S → Type} → Circuit Γ G X Z → Prop
  | _, _, done _ => True
  | _, _, step L next =>
      ((∀ b : L.cells, Nonempty (Unique (GateFamily.Outcome (L.gate b)))) ∧
        ∀ s, Nonempty (Unique (L.onsite s).Index)) ∧ ∀ i, (next i).IsSingle

omit [Fintype S] in
/-- The empty circuit has one branch. -/
theorem isSingle_done : (done X : Circuit Γ G X X).IsSingle :=
  trivial

omit [Fintype S] in
/-- A circuit whose gates and onsite families each have one Kraus index has a unique branch. -/
theorem IsSingle.nonempty_unique_index : {X Z : S → Type} → {c : Circuit Γ G X Z} →
    c.IsSingle → Nonempty (Unique c.Index)
  | _, _, done _, _ => ⟨inferInstanceAs (Unique Unit)⟩
  | _, _, step L next, h => by
    obtain ⟨⟨hg, ho⟩, hn⟩ := h
    have i₁ : ∀ b : L.cells, Unique (GateFamily.Outcome (L.gate b)) := fun b ↦ (hg b).some
    have i₂ : ∀ s : L.Free, Unique (L.onsite s).Index := fun s ↦ (ho s).some
    let u : Unique L.Index :=
      { default := (fun b ↦ (i₁ b).default, fun s ↦ (i₂ s).default)
        uniq := fun ⟨f, g⟩ ↦ Prod.ext (funext fun b ↦ (i₁ b).uniq (f b))
          (funext fun s ↦ (i₂ s).uniq (g s)) }
    have hu := fun i ↦ (IsSingle.nonempty_unique_index (hn i)).some
    refine ⟨{ default := ⟨default, (hu default).default⟩, uniq := ?_ }⟩
    rintro ⟨i, j⟩
    obtain rfl := u.uniq i
    exact Sigma.ext rfl (heq_of_eq ((hu default).uniq j))

omit [Fintype S] in
/-- `IsSingle` is the local property that every gate and onsite family has a unique index. -/
theorem isSingle_iff_forall (ev : Interpretation G) : {X Z : S → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] → (c : Circuit Γ G X Z) →
      (c.IsSingle ↔ c.Forall ev fun K ↦ Nonempty (Unique K.Index))
  | _, _, _, _, done _ => Iff.rfl
  | _, _, _, _, step _ next =>
    and_congr Iff.rfl (forall_congr' fun i ↦ isSingle_iff_forall ev (next i))

omit [Fintype S] in
/-- The local property `IsSingle` passes to `c.append k` from `c` and every continuation. -/
theorem IsSingle.append : {X Y : S → Type} → {c : Circuit Γ G X Y} →
    {k : c.Index → Circuit Γ G Y Z} → c.IsSingle → (∀ p, (k p).IsSingle) →
      (c.append k).IsSingle
  | _, _, done _, _, _, hk => hk ()
  | _, _, step _ next, _, hc, hk =>
    ⟨hc.1, fun i ↦ IsSingle.append (c := next i) (hc.2 i) fun j ↦ hk ⟨i, j⟩⟩

omit [Fintype S] in
/-- A composition of circuits with one branch has one branch. -/
theorem IsSingle.comp {c : Circuit Γ G X Y} {c' : Circuit Γ G Y Z} (hc : c.IsSingle)
    (hc' : c'.IsSingle) : (c.comp c').IsSingle :=
  hc.append fun _ ↦ hc'

omit [Fintype S] in
/-- The circuit of one layer of a gate family with one outcome per gate has one branch when
every onsite family of the layer has one member. -/
theorem isSingle_ofLayer [GateFamily.UniqueOutcome G] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y) (h : ∀ s, Nonempty (Unique (L.onsite s).Index)) :
    (ofLayer L).IsSingle :=
  ⟨⟨fun b ↦ GateFamily.UniqueOutcome.nonempty_unique (L.gate b), h⟩, fun _ ↦ trivial⟩

section SingleOp

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The operator of a circuit with one branch: the Kraus operator of that branch. -/
noncomputable def singleOp (ev : Interpretation G) (c : Circuit Γ G X Z) (h : c.IsSingle) :
    Matrix (Config Z) (Config X) ℂ :=
  c.kraus ev h.nonempty_unique_index.some.default

/-- The operator of a circuit with one branch is its Kraus operator at any branch. -/
theorem singleOp_eq_kraus (ev : Interpretation G) (c : Circuit Γ G X Z) (h : c.IsSingle)
    (p : c.Index) : c.singleOp ev h = c.kraus ev p :=
  congrArg (c.kraus ev) (h.nonempty_unique_index.some.uniq p).symm

@[simp] theorem singleOp_done (ev : Interpretation G) (h : (done X : Circuit Γ G X X).IsSingle) :
    (done X : Circuit Γ G X X).singleOp ev h = 1 :=
  rfl

/-- The operator of a circuit with one branch, layer by layer: the operator of the continuation
at any outcome of the first layer, times the Kraus operator of the layer at that outcome. -/
theorem singleOp_step [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (ev : Interpretation G)
    (L : Layer Γ G X Y) (next : L.Index → Circuit Γ G Y Z) (h : (step L next).IsSingle)
    (i : L.Index) : (step L next).singleOp ev h = (next i).singleOp ev (h.2 i) * L.kraus ev i := by
  have := (h.2 i).nonempty_unique_index.some
  rw [singleOp_eq_kraus ev _ h ⟨i, default⟩, kraus_step, singleOp_eq_kraus ev _ (h.2 i) default]

/-- The operator of the circuit of one layer with one branch is the Kraus operator of the layer
at any of its indices. -/
theorem singleOp_ofLayer [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (ev : Interpretation G)
    (L : Layer Γ G X Y) (h : (ofLayer L).IsSingle) (i : L.Index) :
    (ofLayer L).singleOp ev h = L.kraus ev i :=
  (singleOp_step ev L _ h i).trans (by rw [singleOp_done, Matrix.one_mul])

/-- The operator of a composition is the product of the operators. -/
theorem singleOp_comp [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (ev : Interpretation G)
    (c : Circuit Γ G X Y) (c' : Circuit Γ G Y Z) (hc : c.IsSingle) (hc' : c'.IsSingle) :
    (c.comp c').singleOp ev (hc.comp hc') = c'.singleOp ev hc' * c.singleOp ev hc := by
  have := (hc.comp hc').nonempty_unique_index.some
  rw [singleOp_eq_kraus ev _ _ default, kraus_comp, singleOp_eq_kraus ev c' hc',
    singleOp_eq_kraus ev c hc]

/-- A circuit with one branch whose gates and onsite families are trace-nonincreasing applies a
contraction: its operator has operator norm at most `1`. -/
theorem norm_singleOp_le_one [∀ s, Fintype (Z s)] (ev : Interpretation G) (c : Circuit Γ G X Z)
    (h : c.IsSingle) (hT : c.Forall ev KrausFamily.IsTraceNonincreasing) :
    ‖c.singleOp ev h‖ ≤ 1 := by
  obtain ⟨u⟩ := h.nonempty_unique_index
  let : Unique (c.krausFamily ev).Index := u
  rw [singleOp_eq_kraus ev c h default]
  exact ((c.krausFamily ev).isTraceNonincreasing_iff_norm_le_one).mp
    (c.isTraceNonincreasing_krausFamily ev hT)

end SingleOp

/-! ### Conditions on the gates -/

/-- Every gate of the circuit, on every branch, satisfies the condition `A` on its syntax. -/
def ForallGate' (A : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, G D X Y → Prop) :
    {X Z : S → Type} → Circuit Γ G X Z → Prop
  | _, _, done _ => True
  | _, _, step L next => (∀ b : L.cells, A (L.gate b)) ∧ ∀ i, (next i).ForallGate' A

/-- Every gate of the circuit, on every branch, satisfies the condition `A`, which may use the
finiteness and decidability of the basis types of the gate, as a condition evaluating the gate
does. -/
def ForallGate
    (A : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G D X Y → Prop) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      Circuit Γ G X Z → Prop
  | _, _, _, _, done _ => True
  | _, _, _, _, step L next => (∀ b : L.cells, A (L.gate b)) ∧ ∀ i, (next i).ForallGate A

omit [Fintype S] in
/-- A condition on gates passes to `c.append k` from `c` and every continuation. -/
theorem ForallGate'.append {A : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, G D X Y → Prop} :
    {X Y : S → Type} → {c : Circuit Γ G X Y} → {k : c.Index → Circuit Γ G Y Z} →
      c.ForallGate' A → (∀ p, (k p).ForallGate' A) → (c.append k).ForallGate' A
  | _, _, done _, _, _, hk => hk ()
  | _, _, step _ next, _, hc, hk =>
    ⟨hc.1, fun i ↦ ForallGate'.append (c := next i) (hc.2 i) fun j ↦ hk ⟨i, j⟩⟩

omit [Fintype S] in
/-- A condition on gates passes to compositions. -/
theorem ForallGate'.comp {A : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, G D X Y → Prop}
    {c : Circuit Γ G X Y} {c' : Circuit Γ G Y Z} (hc : c.ForallGate' A)
    (hc' : c'.ForallGate' A) : (c.comp c').ForallGate' A :=
  hc.append fun _ ↦ hc'

omit [Fintype S] in
/-- A condition on gates passes to `c.append k` from `c` and every continuation. -/
theorem ForallGate.append
    {A : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G D X Y → Prop} : {X Y : S → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] → [∀ s, Fintype (Y s)] →
    [∀ s, DecidableEq (Y s)] → {c : Circuit Γ G X Y} → {k : c.Index → Circuit Γ G Y Z} →
      c.ForallGate A → (∀ p, (k p).ForallGate A) → (c.append k).ForallGate A
  | _, _, i₁, i₂, i₃, i₄, done _, _, _, hk => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    exact hk ()
  | _, _, _, _, _, _, step _ next, _, hc, hk =>
    ⟨hc.1, fun i ↦ ForallGate.append (c := next i) (hc.2 i) fun j ↦ hk ⟨i, j⟩⟩

omit [Fintype S] in
/-- A condition on gates passes to compositions. -/
theorem ForallGate.comp [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)]
    {A : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G D X Y → Prop}
    {c : Circuit Γ G X Y} {c' : Circuit Γ G Y Z} (hc : c.ForallGate A) (hc' : c'.ForallGate A) :
    (c.comp c').ForallGate A :=
  hc.append fun _ ↦ hc'

/-! ### The cells along a branch -/

/-- The cells used along a branch, layer by layer; within a layer in the order of
`Finset.toList`. -/
noncomputable def gateCells : {X Z : S → Type} → (c : Circuit Γ G X Z) → c.Index → List Γ.Cell
  | _, _, done _, _ => []
  | _, _, step L next, p => L.cells.toList ++ (next p.1).gateCells p.2

/-- The sites of the cells used along a branch. -/
noncomputable def gateSites (c : Circuit Γ G X Z) (p : c.Index) : List (Finset S) :=
  (c.gateCells p).map Γ.cell

/-- Along a branch, the total weight of the cells used is at most the largest total weight over
the branches. -/
theorem sum_gateCells_le (w : Γ.Cell → ℕ) : {X Z : S → Type} → (c : Circuit Γ G X Z) →
    (p : c.Index) →
      ((c.gateCells p).map w).sum ≤ c.total fun _ _ L ↦ ∑ b ∈ L.cells, w b
  | _, _, done _, _ => le_rfl
  | _, _, step L next, p => by
    simp only [gateCells, total, List.map_append, List.sum_append, Finset.sum_map_toList]
    exact Nat.add_le_add_left ((sum_gateCells_le w (next p.1) p.2).trans
      (Finset.le_sup (f := fun i ↦ (next i).total _) (Finset.mem_univ p.1))) _

/-- In an unbranched circuit, the total weight of the cells used along any branch is the total
weight of the circuit. -/
theorem sum_gateCells_eq_of_isUnbranched (w : Γ.Cell → ℕ) : {X Z : S → Type} →
    (c : Circuit Γ G X Z) → c.IsUnbranched → (p : c.Index) →
      ((c.gateCells p).map w).sum = c.total fun _ _ L ↦ ∑ b ∈ L.cells, w b
  | _, _, done _, _, _ => rfl
  | _, _, step L next, hc, p => by
    simp only [gateCells, total, List.map_append, List.sum_append, Finset.sum_map_toList]
    rw [sum_gateCells_eq_of_isUnbranched w (next p.1) (hc.2 p.1) p.2]
    congr 1
    rw [show (fun i ↦ (next i).total fun _ _ L ↦ ∑ b ∈ L.cells, w b) =
        fun _ ↦ (next p.1).total fun _ _ L ↦ ∑ b ∈ L.cells, w b from
      funext fun i ↦ by rw [hc.1 i p.1]]
    exact (Finset.sup_const ⟨p.1, Finset.mem_univ p.1⟩ _).symm

/-- The gate count of a circuit is the total, along its most expensive branch, of the costs of
the cells of each layer. -/
theorem gateCount_eq_total_sum (c : Circuit Γ G X Z) :
    c.gateCount = c.total fun _ _ L ↦ ∑ b ∈ L.cells, Γ.cost b := by
  rw [gateCount]
  congr
  funext _ _ L
  exact L.gateCount_eq_sum

/-- The participation of a site is the total, along the branch with most such cells, of the
number of cells of positive cost containing it. -/
theorem participation_eq_total_sum (c : Circuit Γ G X Z) (s : S) :
    c.participation s = c.total fun _ _ L ↦
      ∑ b ∈ L.cells, if s ∈ Γ.cell b ∧ 0 < Γ.cost b then 1 else 0 := by
  rw [participation]
  congr
  funext _ _ L
  exact Finset.sum_coe_sort L.cells fun b ↦ if s ∈ Γ.cell b ∧ 0 < Γ.cost b then 1 else 0

/-- Along any branch, the costs of the cells used add up to at most the gate count. -/
theorem sum_cost_gateCells_le (c : Circuit Γ G X Z) (p : c.Index) :
    ((c.gateCells p).map Γ.cost).sum ≤ c.gateCount :=
  (c.gateCount_eq_total_sum) ▸ sum_gateCells_le Γ.cost c p

/-- In an unbranched circuit, the costs of the cells used along any branch add up to the gate
count. -/
theorem sum_cost_gateCells_eq_of_isUnbranched (c : Circuit Γ G X Z) (hc : c.IsUnbranched)
    (p : c.Index) : ((c.gateCells p).map Γ.cost).sum = c.gateCount :=
  (c.gateCount_eq_total_sum) ▸ sum_gateCells_eq_of_isUnbranched Γ.cost c hc p

/-- In an unbranched circuit, the participation of a site is the number of cells of positive
cost containing it along any branch. -/
theorem participation_eq_of_isUnbranched (c : Circuit Γ G X Z) (hc : c.IsUnbranched)
    (p : c.Index) (s : S) :
    c.participation s =
      ((c.gateCells p).map fun b ↦ if s ∈ Γ.cell b ∧ 0 < Γ.cost b then 1 else 0).sum :=
  (c.participation_eq_total_sum s) ▸ (sum_gateCells_eq_of_isUnbranched _ c hc p).symm

end Circuit

end QuantumCircuit
