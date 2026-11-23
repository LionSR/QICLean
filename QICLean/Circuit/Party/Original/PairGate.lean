/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Original.Basic

/-!
# Pair sources and pair effects as original gates

A normalized pair source or pair effect is a nonprivate gate on the cell of its two endpoints,
whose gate expansion is the one monomial "this gate" with coefficient one
(`WeightedGate.single`, `ChainGate.toMonomial`, `OriginalGate.ofChainGate`). This is how the
allowed monomials of Theorem 5.2 enter original circuits (`Original/FromWord`).

## Main definitions

* `QuantumCircuit.Party.SourceGate.restrictCell`, `PairEffectGate.restrictCell`,
  `ChainGate.restrictCell`, `ChainGate.toMonomial` — a pair source or effect read on the parties
  of its cell, as a one-gate monomial.
* `QuantumCircuit.Party.WeightedGate.single` — the gate expansion of one monomial with
  coefficient one.
* `QuantumCircuit.Party.OriginalGate.ofChainGate`,
  `QuantumCircuit.Party.OriginalCircuit.sourceCircuit`,
  `QuantumCircuit.Party.OriginalCircuit.effectCircuit`.

## Main results

* `QuantumCircuit.Party.OriginalCircuit.op_sourceCircuit`, `op_effectCircuit`.
* `QuantumCircuit.Party.ChainGate.op_toMonomial_inl`, `op_toMonomial_inr`,
  `effectCount_toMonomial_le_one`, `sourceCount_toMonomial_le_one`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 21–43 (allowed
  monomials).
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Pair sources and effects on the parties of their cell

`SourceGate.restrictCell g` is the restriction `SourceGate.restrict D subset_rfl g` of
`Syntax/Restrict` with the cell written `Finset.univ` rather than `D.subtype (· ∈ D)`, so that the
one-gate monomial of `g` acts on all parties of `↥D` and its operator is the matrix of `g` on the
cell with no reindexing (`ChainGate.op_toMonomial_inl`). `Syntax/Restrict` has no restriction of
pair effects, so `PairEffectGate.restrictCell` has no counterpart there. The direction is the
converse of `Word.onCell` (`Syntax/OnCell`), which runs a word on `↥D` inside all parties. -/

namespace SourceGate

variable {D : Finset P} {X Y : P → Type}

/-- A pair source read on the parties of its cell: the same data, the cell being all parties of `↥D`
(`SourceGate.restrict D subset_rfl` with the cell `Finset.univ`). -/
def restrictCell (g : SourceGate D X Y) :
    SourceGate (P := ↥D) Finset.univ (fun s ↦ X s) (fun s ↦ Y s) where
  left := ⟨g.left, g.left_mem⟩
  right := ⟨g.right, g.right_mem⟩
  distinct h := g.distinct (congrArg Subtype.val h)
  leftBasis := g.leftBasis
  rightBasis := g.rightBasis
  vector := g.vector
  cell_eq := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have hx : x.1 ∈ ({g.left, g.right} : Finset P) := g.cell_eq ▸ x.2
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    exact hx.imp Subtype.ext Subtype.ext
  leftEquiv := g.leftEquiv
  rightEquiv := g.rightEquiv
  outside s hs := absurd (Finset.mem_univ s) hs

/-- Reading the gate on its cell keeps its vector. -/
@[simp] theorem vector_restrictCell (g : SourceGate D X Y) :
    g.restrictCell.vector = g.vector :=
  rfl

end SourceGate

namespace PairEffectGate

variable {D : Finset P} {X Y : P → Type}

/-- A pair effect read on the parties of its cell. -/
def restrictCell (g : PairEffectGate D X Y) :
    PairEffectGate (P := ↥D) Finset.univ (fun s ↦ X s) (fun s ↦ Y s) where
  left := ⟨g.left, g.left_mem⟩
  right := ⟨g.right, g.right_mem⟩
  distinct h := g.distinct (congrArg Subtype.val h)
  leftBasis := g.leftBasis
  rightBasis := g.rightBasis
  vector := g.vector
  cell_eq := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have hx : x.1 ∈ ({g.left, g.right} : Finset P) := g.cell_eq ▸ x.2
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    exact hx.imp Subtype.ext Subtype.ext
  leftEquiv := g.leftEquiv
  rightEquiv := g.rightEquiv
  outside s hs := absurd (Finset.mem_univ s) hs

/-- Reading the gate on its cell keeps its vector. -/
@[simp] theorem vector_restrictCell (g : PairEffectGate D X Y) :
    g.restrictCell.vector = g.vector :=
  rfl

end PairEffectGate

namespace ChainGate

variable {D : Finset P} {X Y : P → Type}

/-- The pair data of a pair source or effect. -/
def pairSource : ChainGate D X Y → PairSource P
  | .inl g => g.toPairSource
  | .inr g => g.toPairSource

/-- The cell of a pair source or effect is the pair of its endpoints. -/
theorem cell_eq : (g : ChainGate D X Y) → D = {g.pairSource.left, g.pairSource.right}
  | .inl g => g.cell_eq
  | .inr g => g.cell_eq

/-- **A pair source or effect is not private**: its cell has two parties. Source:
`04-compression.tex`, lines 25–35. -/
theorem card_ne_one (g : ChainGate D X Y) : D.card ≠ 1 := by
  rw [g.cell_eq, Finset.card_pair g.pairSource.distinct]
  decide

/-- A pair source or effect read on the parties of its cell. -/
def restrictCell : ChainGate D X Y → ChainGate (P := ↥D) Finset.univ (fun s ↦ X s) (fun s ↦ Y s)
  | .inl g => .inl g.restrictCell
  | .inr g => .inr g.restrictCell

/-- A pair source or effect as the one-gate monomial on the parties of its cell. -/
def toMonomial [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (g : ChainGate D X Y) :
    Monomial D (fun s ↦ X s) (fun s ↦ Y s) :=
  PartyCircuit.gate Finset.univ (fun s hs ↦ absurd (Finset.mem_univ s) hs) g.restrictCell

/-- The one-gate monomial of a normalized pair source or effect is allowed. -/
theorem isAllowed_toMonomial [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (g : ChainGate D X Y)
    (hg : ‖g.pairSource.vector‖ = 1) : g.toMonomial.IsAllowed chainEv ChainGate.IsAllowed := by
  rcases g with g | g
  · exact ⟨(SourceGate.norm_ev_le g.restrictCell ()).trans hg.le, hg⟩
  · exact ⟨(PairEffectGate.norm_ev_le g.restrictCell ()).trans hg.le, hg⟩

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)]

/-- The one-gate monomial of a pair source has the matrix of the source on the cell. -/
theorem op_toMonomial_inl (g : SourceGate D X Y) :
    (toMonomial (.inl g : ChainGate D X Y)).op chainEv = g.regionMatrix := by
  change (PartyCircuit.gate (G := ChainGate) Finset.univ _ (ChainGate.restrictCell (.inl g))).op
    chainEv = _
  rw [PartyCircuit.op_gate (P := ↥D) (G := ChainGate)]
  ext y x
  rw [placeBetween_apply, ite_eq_left fun v hv ↦ absurd (Finset.mem_univ v) hv]
  rfl

/-- The one-gate monomial of a pair effect has the matrix of the effect on the cell. -/
theorem op_toMonomial_inr (g : PairEffectGate D X Y) :
    (toMonomial (.inr g : ChainGate D X Y)).op chainEv = g.regionMatrix := by
  change (PartyCircuit.gate (G := ChainGate) Finset.univ _ (ChainGate.restrictCell (.inr g))).op
    chainEv = _
  rw [PartyCircuit.op_gate (P := ↥D) (G := ChainGate)]
  ext y x
  rw [placeBetween_apply, ite_eq_left fun v hv ↦ absurd (Finset.mem_univ v) hv]
  rfl

end ChainGate

/-! ### One-monomial gates -/

namespace WeightedGate

variable {D : Finset P} {X Y : P → Type}

/-- The gate expansion consisting of one monomial with coefficient one. -/
def single (M : Monomial D (fun s ↦ X s) (fun s ↦ Y s)) : WeightedGate D X Y :=
  ⟨[(1, M)]⟩

/-- The matrix of a one-monomial gate is the operator of the monomial. -/
@[simp] theorem ev_single [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (M : Monomial D (fun s ↦ X s) (fun s ↦ Y s)) (o : Unit) :
    WeightedGate.ev (single M) o = M.op chainEv := by
  simp [WeightedGate.ev, single]

end WeightedGate

namespace OriginalGate

variable {D : Finset P} {X Y : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- A normalized pair source or effect as an original gate: the one-monomial expansion of the gate
on its cell. Source: `04-compression.tex`, lines 25–35. -/
noncomputable def ofChainGate (g : ChainGate D X Y) (hg : ‖g.pairSource.vector‖ = 1) :
    OriginalGate D X Y :=
  ofWeightedGate (WeightedGate.single g.toMonomial) g.card_ne_one
    (by
      intro t ht
      rw [WeightedGate.single, List.mem_singleton] at ht
      subst ht
      exact g.isAllowed_toMonomial hg)
    (by
      rw [WeightedGate.ev_single]
      exact PartyCircuit.norm_op_le_one (P := ↥D) (G := ChainGate) chainEv
        (g.isAllowed_toMonomial hg))

/-- The gate expansion of one pair source or effect is the one-gate monomial. -/
@[simp] theorem toWeightedGate_ofChainGate (g : ChainGate D X Y)
    (hg : ‖g.pairSource.vector‖ = 1) :
    (ofChainGate g hg).toWeightedGate = WeightedGate.single g.toMonomial :=
  rfl

end OriginalGate

/-! ### One pair source or effect as an original circuit -/

namespace OriginalCircuit

variable {D : Finset P} {X Y : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- A normalized pair source as a two-party nonprivate gate. Source: `04-compression.tex`, lines
25–35. -/
noncomputable def sourceCircuit (g : SourceGate D X Y) (hg : ‖g.vector‖ = 1) :
    OriginalCircuit X Y :=
  gate D g.outside (OriginalGate.ofChainGate (.inl g) hg)

/-- A normalized pair effect as a two-party nonprivate gate. Source: `04-compression.tex`, lines
25–35. -/
noncomputable def effectCircuit (g : PairEffectGate D X Y) (hg : ‖g.vector‖ = 1) :
    OriginalCircuit X Y :=
  gate D g.outside (OriginalGate.ofChainGate (.inr g) hg)

variable [Fintype P]

/-- The original circuit of one pair source prepares its vector. -/
theorem op_sourceCircuit (g : SourceGate D X Y) (hg : ‖g.vector‖ = 1) :
    (sourceCircuit g hg).op = prepMatrix g.configEquiv g.vector := by
  rw [sourceCircuit, op_gate]
  change placeBetween D g.outside (WeightedGate.ev (WeightedGate.single
    (ChainGate.toMonomial (.inl g : ChainGate D X Y))) ()) = _
  rw [WeightedGate.ev_single, ChainGate.op_toMonomial_inl, ← SourceGate.op_gate g,
    PartyCircuit.op_gate]
  rfl

/-- The original circuit of one pair effect applies its effect. -/
theorem op_effectCircuit (g : PairEffectGate D X Y) (hg : ‖g.vector‖ = 1) :
    (effectCircuit g hg).op = (effectMatrix g.vector (Config Y)).submatrix id g.configEquiv := by
  rw [effectCircuit, op_gate]
  change placeBetween D g.outside (WeightedGate.ev (WeightedGate.single
    (ChainGate.toMonomial (.inr g : ChainGate D X Y))) ()) = _
  rw [WeightedGate.ev_single, ChainGate.op_toMonomial_inr,
    ← PairEffectGate.op_gate_eq_effectMatrix g, PartyCircuit.op_gate]
  rfl

omit [Fintype P] in
/-- One pair source is one nonprivate gate. -/
@[simp] theorem nonprivateCount_sourceCircuit (g : SourceGate D X Y) (hg : ‖g.vector‖ = 1) :
    (sourceCircuit g hg).nonprivateCount = 1 :=
  nonprivateCount_gate _ _ _

omit [Fintype P] in
/-- One pair effect is one nonprivate gate. -/
@[simp] theorem nonprivateCount_effectCircuit (g : PairEffectGate D X Y) (hg : ‖g.vector‖ = 1) :
    (effectCircuit g hg).nonprivateCount = 1 :=
  nonprivateCount_gate _ _ _

end OriginalCircuit

/-! ### Facts on the one-gate monomials -/

namespace ChainGate

variable {D : Finset P} {X Y : P → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- The one-gate monomial of a pair source has no pair effect. -/
@[simp] theorem effectCount_toMonomial_inl (g : SourceGate D X Y) :
    (ChainGate.toMonomial (.inl g : ChainGate D X Y)).effectCount = 0 :=
  rfl

/-- The one-gate monomial of a pair effect has one pair effect. -/
@[simp] theorem effectCount_toMonomial_inr (g : PairEffectGate D X Y) :
    (ChainGate.toMonomial (.inr g : ChainGate D X Y)).effectCount = 1 :=
  rfl

/-- The one-gate monomial of a pair source has one pair source. -/
@[simp] theorem sourceCount_toMonomial_inl (g : SourceGate D X Y) :
    (ChainGate.toMonomial (.inl g : ChainGate D X Y)).sourceCount = 1 :=
  rfl

/-- The one-gate monomial of a pair effect has no pair source. -/
@[simp] theorem sourceCount_toMonomial_inr (g : PairEffectGate D X Y) :
    (ChainGate.toMonomial (.inr g : ChainGate D X Y)).sourceCount = 0 :=
  rfl

/-- A one-gate monomial has at most one pair effect. -/
theorem effectCount_toMonomial_le_one (g : ChainGate D X Y) : g.toMonomial.effectCount ≤ 1 := by
  rcases g with g | g
  · exact Nat.zero_le 1
  · exact le_rfl

/-- A one-gate monomial has at most one pair source. -/
theorem sourceCount_toMonomial_le_one (g : ChainGate D X Y) : g.toMonomial.sourceCount ≤ 1 := by
  rcases g with g | g
  · exact le_rfl
  · exact Nat.zero_le 1

end ChainGate

end QuantumCircuit.Party
