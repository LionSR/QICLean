/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.PartyCircuit
import QICLean.Circuit.Core.Map
import QICLean.Analysis.Norm.MatrixKroneckerContraction

/-!
# Relabelling the bases and the gates of a party circuit

The relabelling of the bases of every party along bijections `e s : Y s ≃ X s` is one step of
local operations, the permutation matrices of the bijections; its operator is the matrix of the
bijection of configurations (`PartyCircuit.op_relabel`), and applying it after a matrix
reindexes the rows (`PartyCircuit.op_relabel_mul`). The replacement of every gate along a
morphism of gate families (`PartyCircuit.mapGates`) keeps the syntax otherwise; along a
morphism compatible with the interpretations it keeps the operator, and it keeps the cells and
the counts.

## Main definitions

* `QuantumCircuit.Party.PartyCircuit.relabel` — the relabelling of the bases.
* `QuantumCircuit.Party.PartyCircuit.mapGates` — the gates replaced along a morphism.

## Main results

* `QuantumCircuit.Party.PartyCircuit.op_relabel`,
  `QuantumCircuit.Party.PartyCircuit.op_relabel_mul`,
  `QuantumCircuit.Party.PartyCircuit.isAllowed_relabel` — relabellings.
* `QuantumCircuit.Party.PartyCircuit.op_mapGates`,
  `QuantumCircuit.Party.PartyCircuit.gates_mapGates`,
  `QuantumCircuit.Party.PartyCircuit.IsAllowed.mapGates` — replacing the gates.
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P]

namespace PartyCircuit

variable {G : Finset P → (P → Type) → (P → Type) → Type 1} [GateFamily G] {X Y Z : P → Type}

/-! ### Relabelling the bases -/

section Relabel

variable [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The relabelling of the bases along `e`: at every party the matrix of the bijection `e s`
from the basis `Y s` to the basis `X s`, read from `ℂ^{X s}` to `ℂ^{Y s}`; it maps the
configuration `e ∘ y` to `y`. -/
def relabel (e : ∀ s, Y s ≃ X s) : PartyCircuit G X Y :=
  localOps fun s ↦ (e s).toPEquiv.toMatrix

variable [GateFamily.UniqueOutcome G] [∀ p, Fintype (X p)] (ev : Interpretation G)

/-- The operator of a relabelling is the matrix of the bijection of configurations. -/
theorem op_relabel (e : ∀ s, Y s ≃ X s) :
    (relabel (G := G) e).op ev = (Equiv.piCongrRight e).toPEquiv.toMatrix := by
  rw [relabel, op_localOps]
  ext y x
  simp only [piKronecker_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Finset.prod_boole, Finset.mem_univ, forall_const]
  exact if_congr ⟨fun h ↦ funext h, fun h s ↦ congrFun h s⟩ rfl rfl

/-- Applying a relabelling after a matrix reindexes its rows: no inverse appears. -/
theorem op_relabel_mul (e : ∀ s, Y s ≃ X s) {W : Type} (M : Matrix (Config X) W ℂ) :
    (relabel (G := G) e).op ev * M = M.submatrix (Equiv.piCongrRight e) id := by
  rw [op_relabel, PEquiv.toMatrix_toPEquiv_mul]

/-- The relabelling along the inverses of `e : X s ≃ Y s`. -/
theorem op_relabel_symm (e : ∀ s, X s ≃ Y s) :
    (relabel (G := G) fun s ↦ (e s).symm).op ev =
      (Equiv.piCongrRight e).symm.toPEquiv.toMatrix := by
  rw [op_relabel]
  rfl

omit [Fintype P] [∀ p, Fintype (X p)] in
/-- A relabelling is allowed. -/
theorem isAllowed_relabel
    {A : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G D X Y → Prop}
    [∀ p, Fintype (X p)] (e : ∀ s, Y s ≃ X s) : (relabel (G := G) e).IsAllowed ev A :=
  fun s ↦ l2_opNorm_toMatrix_toPEquiv_le (e s)

end Relabel

/-! ### Replacing the gates -/

section MapGates

variable {G₂ : Finset P → (P → Type) → (P → Type) → Type 1} [GateFamily G₂]
  (φ : GateMorphism G G₂)

/-- The party circuit with every gate replaced by its image under the morphism `φ`. -/
def mapGates : {X Y : P → Type} → PartyCircuit G X Y → PartyCircuit G₂ X Y
  | _, _, done X => done X
  | _, _, gate D hY g => gate D hY (φ.map g)
  | _, _, localOp p hY A => localOp p hY A
  | _, _, localOps A => localOps A
  | _, _, comp c c' => comp (mapGates c) (mapGates c')

/-- A compatible morphism keeps the operator. -/
theorem op_mapGates [GateFamily.UniqueOutcome G] [GateFamily.UniqueOutcome G₂]
    {ev : Interpretation G} {ev₂ : Interpretation G₂} (hφ : φ.IsCompatible ev ev₂) :
    {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
      (c : PartyCircuit G X Y) → (c.mapGates φ).op ev₂ = c.op ev
  | _, _, _, _, done _ => rfl
  | _, _, _, _, gate D hY g => by
    rw [mapGates, op_gate, op_gate]
    exact congrArg (placeBetween D hY)
      ((hφ g _).trans (congrArg (ev g) (GateFamily.UniqueOutcome.eq_outcome _)))
  | _, _, _, _, localOp p hY A => by rw [mapGates, op_localOp, op_localOp]
  | _, _, _, _, localOps A => by rw [mapGates, op_localOps, op_localOps]
  | _, _, _, _, comp c c' => by
    rw [mapGates, op_comp, op_comp, op_mapGates hφ c, op_mapGates hφ c']

omit [Fintype P] [DecidableEq P] in
/-- The gates of the circuit with its gates replaced are the images of the gates. -/
theorem gates_mapGates : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    (c.mapGates φ).gates = c.gates.map fun o ↦ ⟨o.1, o.2.1, o.2.2.1, φ.map o.2.2.2⟩
  | _, _, done _ => rfl
  | _, _, gate _ _ _ => rfl
  | _, _, localOp _ _ _ => rfl
  | _, _, localOps _ => rfl
  | _, _, comp c c' => by
    rw [mapGates, gates, gates, List.map_append, gates_mapGates c, gates_mapGates c']

omit [Fintype P] [DecidableEq P] in
/-- Replacing the gates keeps the cells. -/
@[simp] theorem gateCells_mapGates : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    (c.mapGates φ).gateCells = c.gateCells
  | _, _, done _ => rfl
  | _, _, gate _ _ _ => rfl
  | _, _, localOp _ _ _ => rfl
  | _, _, localOps _ => rfl
  | _, _, comp c c' => by rw [mapGates, gateCells, gateCells, gateCells_mapGates c,
      gateCells_mapGates c']

omit [Fintype P] [DecidableEq P] in
/-- Replacing the gates keeps the number of gates. -/
@[simp] theorem numGates_mapGates : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    (c.mapGates φ).numGates = c.numGates
  | _, _, done _ => rfl
  | _, _, gate _ _ _ => rfl
  | _, _, localOp _ _ _ => rfl
  | _, _, localOps _ => rfl
  | _, _, comp c c' => by rw [mapGates, numGates, numGates, numGates_mapGates c,
      numGates_mapGates c']

omit [Fintype P] in
/-- Replacing the gates keeps the gate count. -/
@[simp] theorem gateCount_mapGates : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    (c.mapGates φ).gateCount = c.gateCount
  | _, _, done _ => rfl
  | _, _, gate _ _ _ => rfl
  | _, _, localOp _ _ _ => rfl
  | _, _, localOps _ => rfl
  | _, _, comp c c' => by rw [mapGates, gateCount, gateCount, gateCount_mapGates c,
      gateCount_mapGates c']

omit [Fintype P] in
/-- Replacing the gates keeps the participations. -/
@[simp] theorem participation_mapGates (p : P) : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    (c.mapGates φ).participation p = c.participation p
  | _, _, done _ => rfl
  | _, _, gate _ _ _ => rfl
  | _, _, localOp _ _ _ => rfl
  | _, _, localOps _ => rfl
  | _, _, comp c c' => by rw [mapGates, participation, participation,
      participation_mapGates p c, participation_mapGates p c']

omit [Fintype P] in
/-- Along a compatible morphism, an allowed circuit stays allowed when the condition on gates
passes to the images. -/
theorem IsAllowed.mapGates [GateFamily.UniqueOutcome G] [GateFamily.UniqueOutcome G₂]
    {ev : Interpretation G} {ev₂ : Interpretation G₂} (hφ : φ.IsCompatible ev ev₂)
    {A : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G D X Y → Prop}
    {A₂ : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G₂ D X Y → Prop}
    (hA : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (g : G D X Y), A g → A₂ (φ.map g)) :
    {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
      {c : PartyCircuit G X Y} → c.IsAllowed ev A → (c.mapGates φ).IsAllowed ev₂ A₂
  | _, _, _, _, done _, _ => trivial
  | _, _, _, _, gate D hY g, h => by
    refine ⟨?_, hA g h.2⟩
    have he : ev₂ (φ.map g) (GateFamily.UniqueOutcome.outcome (φ.map g)) =
        ev g (GateFamily.UniqueOutcome.outcome g) :=
      (hφ g _).trans (congrArg (ev g) (GateFamily.UniqueOutcome.eq_outcome _))
    exact (congrArg (fun M ↦ ‖M‖) he).trans_le h.1
  | _, _, _, _, localOp _ _ _, h => h
  | _, _, _, _, localOps _, h => h
  | _, _, _, _, comp _ _, h => ⟨IsAllowed.mapGates hφ hA h.1, IsAllowed.mapGates hφ hA h.2⟩

end MapGates

end PartyCircuit

end QuantumCircuit.Party
