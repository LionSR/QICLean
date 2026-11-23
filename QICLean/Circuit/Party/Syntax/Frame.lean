/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Word
import QICLean.Circuit.Party.Syntax.EffectCircuit
import QICLean.Algebra.Combinatorics.TupleEquiv

/-!
# Party circuits beside spectator factors

`PartyCircuit.frame W c` runs the party circuit `c` beside an untouched spectator factor `W p`
at every party `p`, placed in front of the basis of `p`: from the system `fun p ↦ W p × X p` to
`fun p ↦ W p × Y p`. It is defined by recursion on the syntax: a gate is replaced by the framed
gate, a local operation `A` by `1 ⊗ A`. A spectator register of a party is a factor of its basis,
so no exchange of registers is needed.

A gate family runs beside spectator factors when it carries an instance of `GateFrame`; its
interpretation is compatible with framing (`GateFrame.IsCompatible`) when a framed gate acts as
`1 ⊗ M`. Pair sources, pair effects, the gates of monomials and weighted gates carry instances,
with compatible interpretations. Then the operator of a framed circuit is `1 ⊗ op c`, read along
the pairing of configurations `Equiv.arrowProdEquivProdArrow` (`PartyCircuit.op_frame`), and
framing keeps allowedness, the cells, the counts and the sources.

Framing by the trivial system `fun _ ↦ Unit` is not the circuit itself (the systems
`Unit × X p` and `X p` differ); `PartyCircuit.op_frame_unit` reads it back.

## Main definitions

* `QuantumCircuit.Party.GateFrame`, `QuantumCircuit.Party.GateFrame.IsCompatible`.
* `QuantumCircuit.Party.SourceGate.frame`, `QuantumCircuit.Party.PairEffectGate.frame`.
* `QuantumCircuit.Party.PartyCircuit.frame`.

## Main results

* `QuantumCircuit.Party.SourceGate.isCompatible_frame`,
  `QuantumCircuit.Party.PairEffectGate.isCompatible_frame`,
  `QuantumCircuit.Party.chainEv_isCompatible_frame`,
  `QuantumCircuit.Party.WeightedGate.isCompatible_frame` — compatible interpretations.
* `QuantumCircuit.Party.PartyCircuit.op_frame`, `QuantumCircuit.Party.PartyCircuit.op_frame_unit`
  — the operator.
* `QuantumCircuit.Party.PartyCircuit.isAllowed_frame`, `gateCells_frame`, `numGates_frame`,
  `gateCount_frame`, `participation_frame`, `QuantumCircuit.Party.Word.sources_frame`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 21–36
  (operations act on some registers and leave the others untouched).
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Gate families beside spectator factors -/

/-- A gate family that can be run beside spectator factors, the factor `W p` in front of the
basis of every party `p`. -/
class GateFrame (G : Finset P → (P → Type) → (P → Type) → Type 1) [GateFamily G] where
  /-- The gate beside the spectator factors `W`; it may read the finiteness of the bases of the
  spectators, of the input and of the output. -/
  frame : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ (W : P → Type) [∀ p, Fintype (W p)]
    [∀ p, DecidableEq (W p)] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
    [∀ p, DecidableEq (Y p)], G D X Y → G D (fun p ↦ W p × X p) (fun p ↦ W p × Y p)
  /-- The outcomes are unchanged. -/
  outcomeEquiv : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ (W : P → Type) [∀ p, Fintype (W p)]
    [∀ p, DecidableEq (W p)] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
    [∀ p, DecidableEq (Y p)] (g : G D X Y),
    GateFamily.Outcome (frame W g) ≃ GateFamily.Outcome g

/-- An interpretation is compatible with framing when a framed gate acts as `1 ⊗ M` on the
spectator factors of its cell and the cell, read along the pairing of configurations. -/
def GateFrame.IsCompatible (G : Finset P → (P → Type) → (P → Type) → Type 1) [GateFamily G]
    [GateFrame G] (ev : Interpretation G) : Prop :=
  ∀ ⦃D : Finset P⦄ ⦃X Y W : P → Type⦄ [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]
    (g : G D X Y) (o : GateFamily.Outcome (GateFrame.frame W g)),
    ev (GateFrame.frame W g) o =
      reindex (Equiv.arrowProdEquivProdArrow {v // v ∈ D} (fun v ↦ W v) (fun v ↦ Y v)).symm
        (Equiv.arrowProdEquivProdArrow {v // v ∈ D} (fun v ↦ W v) (fun v ↦ X v)).symm
        ((1 : Matrix (RegionConfig W D) (RegionConfig W D) ℂ) ⊗ₖ
          ev g (GateFrame.outcomeEquiv W g o))

/-! ### Pair sources and pair effects beside spectator factors -/

namespace SourceGate

variable {D : Finset P} {X Y : P → Type}

/-- A pair source beside spectator factors: the fresh factor goes in front of the spectator. -/
def frame (W : P → Type) (g : SourceGate D X Y) :
    SourceGate D (fun p ↦ W p × X p) (fun p ↦ W p × Y p) where
  toPairSource := g.toPairSource
  cell_eq := g.cell_eq
  leftEquiv := ((Equiv.refl _).prodCongr g.leftEquiv).trans (Equiv.prodLeftComm _ _ _)
  rightEquiv := ((Equiv.refl _).prodCongr g.rightEquiv).trans (Equiv.prodLeftComm _ _ _)
  outside s hs := congrArg (W s × ·) (g.outside s hs)

/-- A framed pair source has the pair data of the source. -/
@[simp] theorem toPairSource_frame (W : P → Type) (g : SourceGate D X Y) :
    (g.frame W).toPairSource = g.toPairSource :=
  rfl

/-- The matrix of a framed pair source is `1 ⊗ M` on the cell. -/
theorem regionMatrix_frame (W : P → Type) [∀ p, DecidableEq (W p)] [∀ s, DecidableEq (X s)]
    (g : SourceGate D X Y) :
    (g.frame W).regionMatrix =
      reindex (Equiv.arrowProdEquivProdArrow {v // v ∈ D} (fun v ↦ W v) (fun v ↦ Y v)).symm
        (Equiv.arrowProdEquivProdArrow {v // v ∈ D} (fun v ↦ W v) (fun v ↦ X v)).symm
        ((1 : Matrix (RegionConfig W D) (RegionConfig W D) ℂ) ⊗ₖ g.regionMatrix) := by
  ext y x
  have hD : ∀ v : {v // v ∈ D}, v = ⟨g.left, g.left_mem⟩ ∨ v = ⟨g.right, g.right_mem⟩ := by
    intro v
    have hv : v.1 ∈ ({g.left, g.right} : Finset P) := g.cell_eq ▸ v.2
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    exact hv.imp (fun h ↦ Subtype.ext h) (fun h ↦ Subtype.ext h)
  have hW : (fun v : {v // v ∈ D} ↦ (y v).1) = (fun v ↦ (x v).1) ↔
      (y ⟨g.left, g.left_mem⟩).1 = (x ⟨g.left, g.left_mem⟩).1 ∧
        (y ⟨g.right, g.right_mem⟩).1 = (x ⟨g.right, g.right_mem⟩).1 :=
    ⟨fun h ↦ ⟨congrFun h _, congrFun h _⟩, fun h ↦ funext fun v ↦ by
      rcases hD v with rfl | rfl
      exacts [h.1, h.2]⟩
  change (if ((y ⟨g.left, g.left_mem⟩).1, (g.leftEquiv (y ⟨g.left, g.left_mem⟩).2).2) =
        x ⟨g.left, g.left_mem⟩ ∧
      ((y ⟨g.right, g.right_mem⟩).1, (g.rightEquiv (y ⟨g.right, g.right_mem⟩).2).2) =
        x ⟨g.right, g.right_mem⟩ then
    g.vector ((g.leftEquiv (y ⟨g.left, g.left_mem⟩).2).1,
      (g.rightEquiv (y ⟨g.right, g.right_mem⟩).2).1) else 0) = _
  simp only [regionMatrix, reindex_apply, submatrix_apply, Equiv.symm_symm,
    Equiv.arrowProdEquivProdArrow_apply, kroneckerMap_apply, one_apply, Prod.ext_iff,
    ite_mul, one_mul, zero_mul]
  by_cases h : (fun v : {v // v ∈ D} ↦ (y v).1) = (fun v ↦ (x v).1)
  · have h' := hW.mp h
    simp only [h, h'.1, h'.2, true_and, ite_true]
  · have h' := mt hW.mpr h
    simp only [h, ite_false]
    exact ite_eq_right_iff.mpr fun hc ↦ absurd ⟨hc.1.1, hc.2.1⟩ h'

end SourceGate

namespace PairEffectGate

variable {D : Finset P} {X Y : P → Type}

/-- A pair effect beside spectator factors: the removed factor sits in front of the
spectator. -/
def frame (W : P → Type) (g : PairEffectGate D X Y) :
    PairEffectGate D (fun p ↦ W p × X p) (fun p ↦ W p × Y p) where
  toPairSource := g.toPairSource
  cell_eq := g.cell_eq
  leftEquiv := ((Equiv.refl _).prodCongr g.leftEquiv).trans (Equiv.prodLeftComm _ _ _)
  rightEquiv := ((Equiv.refl _).prodCongr g.rightEquiv).trans (Equiv.prodLeftComm _ _ _)
  outside s hs := congrArg (W s × ·) (g.outside s hs)

/-- A framed pair effect has the pair data of the effect. -/
@[simp] theorem toPairSource_frame (W : P → Type) (g : PairEffectGate D X Y) :
    (g.frame W).toPairSource = g.toPairSource :=
  rfl

/-- The matrix of a framed pair effect is `1 ⊗ M` on the cell. -/
theorem regionMatrix_frame (W : P → Type) [∀ p, DecidableEq (W p)] [∀ s, DecidableEq (Y s)]
    (g : PairEffectGate D X Y) :
    (g.frame W).regionMatrix =
      reindex (Equiv.arrowProdEquivProdArrow {v // v ∈ D} (fun v ↦ W v) (fun v ↦ Y v)).symm
        (Equiv.arrowProdEquivProdArrow {v // v ∈ D} (fun v ↦ W v) (fun v ↦ X v)).symm
        ((1 : Matrix (RegionConfig W D) (RegionConfig W D) ℂ) ⊗ₖ g.regionMatrix) := by
  rw [regionMatrix_eq_conjTranspose, regionMatrix_eq_conjTranspose]
  change (g.toSourceGate.frame W).regionMatrixᴴ = _
  rw [SourceGate.regionMatrix_frame, conjTranspose_reindex, conjTranspose_kronecker,
    conjTranspose_one]

end PairEffectGate

/-- Pair sources run beside spectator factors. -/
instance : GateFrame (P := P) SourceGate where
  frame _ _ _ W _ _ _ _ _ _ g := g.frame W
  outcomeEquiv _ _ _ _ _ _ _ _ _ _ _ := Equiv.refl Unit

/-- Pair effects run beside spectator factors. -/
instance : GateFrame (P := P) PairEffectGate where
  frame _ _ _ W _ _ _ _ _ _ g := g.frame W
  outcomeEquiv _ _ _ _ _ _ _ _ _ _ _ := Equiv.refl Unit

/-- The gates of monomials run beside spectator factors. -/
instance : GateFrame (ChainGate (P := P)) where
  frame _ _ _ W _ _ _ _ _ _ g := match g with
    | .inl g => .inl (g.frame W)
    | .inr g => .inr (g.frame W)
  outcomeEquiv _ _ _ _ _ _ _ _ _ _ g := match g with
    | .inl _ => Equiv.refl Unit
    | .inr _ => Equiv.refl Unit

/-- The interpretation of pair sources is compatible with framing. -/
theorem SourceGate.isCompatible_frame :
    GateFrame.IsCompatible (P := P) SourceGate SourceGate.ev :=
  fun _ _ _ W _ _ _ _ _ _ g _ ↦ g.regionMatrix_frame W

/-- The interpretation of pair effects is compatible with framing. -/
theorem PairEffectGate.isCompatible_frame :
    GateFrame.IsCompatible (P := P) PairEffectGate PairEffectGate.ev :=
  fun _ _ _ W _ _ _ _ _ _ g _ ↦ g.regionMatrix_frame W

/-- The interpretation of the gates of monomials is compatible with framing. -/
theorem chainEv_isCompatible_frame : GateFrame.IsCompatible (ChainGate (P := P)) chainEv
  | _, _, _, W, _, _, _, _, _, _, .inl g, _ => g.regionMatrix_frame W
  | _, _, _, W, _, _, _, _, _, _, .inr g, _ => g.regionMatrix_frame W

/-! ### Party circuits beside spectator factors -/

namespace PartyCircuit

variable {G : Finset P → (P → Type) → (P → Type) → Type 1} [GateFamily G] [GateFrame G]
  (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

/-- The party circuit `c` beside the spectator factors `W`, the factor `W p` in front of the
basis of every party `p`: every gate framed, every local operation `A` replaced by `1 ⊗ A`. -/
def frame : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    PartyCircuit G X Y → PartyCircuit G (fun p ↦ W p × X p) (fun p ↦ W p × Y p)
  | _, _, _, _, .done _ => .done _
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g =>
    .gate D (fun s hs ↦ congrArg (W s × ·) (hY s hs)) (GateFrame.frame W g)
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A =>
    .localOp p (fun s hs ↦ congrArg (W s × ·) (hY s hs)) ((1 : Matrix (W p) (W p) ℂ) ⊗ₖ A)
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ A =>
    .localOps fun p ↦ (1 : Matrix (W p) (W p) ℂ) ⊗ₖ A p
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' => .comp (frame c) (frame c')

omit [DecidableEq P] in
/-- Framing keeps the cells. -/
@[simp] theorem gateCells_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (c : PartyCircuit G X Y) →
    (c.frame W).gateCells = c.gateCells
  | _, _, _, _, .done _ => rfl
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' => congrArg₂ (· ++ ·) (gateCells_frame c) (gateCells_frame c')

omit [DecidableEq P] in
/-- Framing keeps the number of gates. -/
@[simp] theorem numGates_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (c : PartyCircuit G X Y) →
    (c.frame W).numGates = c.numGates
  | _, _, _, _, .done _ => rfl
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' => congrArg₂ (· + ·) (numGates_frame c) (numGates_frame c')

/-- Framing keeps the gate count. -/
@[simp] theorem gateCount_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (c : PartyCircuit G X Y) →
    (c.frame W).gateCount = c.gateCount
  | _, _, _, _, .done _ => rfl
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' => congrArg₂ (· + ·) (gateCount_frame c) (gateCount_frame c')

/-- Framing keeps the participations. -/
@[simp] theorem participation_frame (p : P) : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (c : PartyCircuit G X Y) →
    (c.frame W).participation p = c.participation p
  | _, _, _, _, .done _ => rfl
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' => congrArg₂ (· + ·) (participation_frame p c) (participation_frame p c')

/-- Framing keeps the number of gates containing a party. -/
@[simp] theorem participationCount_frame (p : P) : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : PartyCircuit G X Y) → (c.frame W).participationCount p = c.participationCount p
  | _, _, _, _, .done _ => rfl
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' =>
    congrArg₂ (· + ·) (participationCount_frame p c) (participationCount_frame p c')

section Op

variable [Fintype P] [GateFamily.UniqueOutcome G] (ev : Interpretation G)

omit [DecidableEq P] [∀ p, Fintype (W p)] [Fintype P] in
/-- A local operation beside a spectator factor, read on the one-party region. -/
private theorem submatrix_one_kronecker {X Y : P → Type} (p : P) (A : Matrix (Y p) (X p) ℂ) :
    ((1 : Matrix (W p) (W p) ℂ) ⊗ₖ A).submatrix
        (fun y : RegionConfig (fun s ↦ W s × Y s) {p} ↦ y ⟨p, Finset.mem_singleton_self p⟩)
        (fun x : RegionConfig (fun s ↦ W s × X s) {p} ↦ x ⟨p, Finset.mem_singleton_self p⟩) =
      reindex
        (Equiv.arrowProdEquivProdArrow {v // v ∈ ({p} : Finset P)} (fun v ↦ W v)
          (fun v ↦ Y v)).symm
        (Equiv.arrowProdEquivProdArrow {v // v ∈ ({p} : Finset P)} (fun v ↦ W v)
          (fun v ↦ X v)).symm
        ((1 : Matrix (RegionConfig W {p}) (RegionConfig W {p}) ℂ) ⊗ₖ
          A.submatrix (fun y ↦ y ⟨p, Finset.mem_singleton_self p⟩)
            (fun x ↦ x ⟨p, Finset.mem_singleton_self p⟩)) := by
  ext y x
  have hp : ∀ v : {v // v ∈ ({p} : Finset P)}, v = ⟨p, Finset.mem_singleton_self p⟩ :=
    fun v ↦ Subtype.ext (Finset.mem_singleton.mp v.2)
  simp only [submatrix_apply, reindex_apply, Equiv.symm_symm,
    Equiv.arrowProdEquivProdArrow_apply, kroneckerMap_apply, one_apply]
  congr 1
  exact if_congr ⟨fun h ↦ funext fun v ↦ by rw [hp v]; exact h, fun h ↦ congrFun h _⟩ rfl rfl

/-- **The operator of a framed circuit is `1 ⊗ op`**, read along the pairing of
configurations. -/
theorem op_frame (hev : GateFrame.IsCompatible G ev) : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → (c : PartyCircuit G X Y) →
      (c.frame W).op ev =
        reindex (Equiv.arrowProdEquivProdArrow P W Y).symm
          (Equiv.arrowProdEquivProdArrow P W X).symm
          ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ c.op ev)
  | _, _, _, _, done _ => by
    rw [frame, op_done, op_done, one_kronecker_one, reindex_apply, submatrix_one_equiv]
  | _, _, _, _, gate D hY g => by
    rw [frame, op_gate, op_gate, show ev (GateFrame.frame W g) _ = _ from hev g _,
      GateFamily.UniqueOutcome.eq_outcome (GateFrame.outcomeEquiv W g _)]
    exact placeBetween_reindex_one_kronecker hY _ _
  | _, _, _, _, localOp p hY A => by
    rw [frame, op_localOp, op_localOp, submatrix_one_kronecker]
    exact placeBetween_reindex_one_kronecker _ _ _
  | _, _, _, _, localOps A => by
    rw [frame, op_localOps, op_localOps, piKronecker_kronecker, piKronecker_one]
  | _, _, _, _, comp c c' => by
    rw [frame, op_comp, op_comp, op_frame hev c, op_frame hev c', reindex_apply, reindex_apply,
      reindex_apply, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul]

/-- Framing by the trivial system: the operator read back through the second factors. -/
theorem op_frame_unit (hev : GateFrame.IsCompatible G ev) {X Y : P → Type}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (c : PartyCircuit G X Y) :
    (c.frame fun _ ↦ Unit).op ev =
      (c.op ev).submatrix (fun y p ↦ (y p).2) (fun x p ↦ (x p).2) := by
  rw [op_frame _ ev hev]
  ext y x
  simp [kroneckerMap_apply, one_apply]

omit [Fintype P] in
/-- **A framed allowed circuit is allowed** when the condition on gates passes to framed
gates. -/
theorem isAllowed_frame (hev : GateFrame.IsCompatible G ev)
    {A : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G D X Y → Prop}
    (hA : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (g : G D X Y), A g → A (GateFrame.frame W g)) :
    {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
      {c : PartyCircuit G X Y} → c.IsAllowed ev A → (c.frame W).IsAllowed ev A
  | _, _, _, _, done _, _ => trivial
  | _, _, _, _, gate D hY g, h => by
    refine ⟨(congrArg norm (hev g _)).trans_le ?_, hA g h.2⟩
    rw [GateFamily.UniqueOutcome.eq_outcome (GateFrame.outcomeEquiv W g _)]
    exact (l2_opNorm_reindex_le _ _ _).trans ((l2_opNorm_one_kronecker_le _).trans h.1)
  | _, _, _, _, localOp _ _ _, h => (l2_opNorm_one_kronecker_le _).trans h
  | _, _, _, _, localOps _, h => fun p ↦ (l2_opNorm_one_kronecker_le _).trans (h p)
  | _, _, _, _, comp _ _, h => ⟨isAllowed_frame hev hA h.1, isAllowed_frame hev hA h.2⟩

end Op

end PartyCircuit

/-! ### Words beside spectator factors -/

namespace Word

variable (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

/-- Framing keeps the source list. -/
@[simp] theorem sources_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (w : Word X Y) →
    Word.sources (w.frame W) = w.sources
  | _, _, _, _, .done _ => rfl
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w' => congrArg₂ (· ++ ·) (sources_frame w') (sources_frame w)

/-- A framed allowed word is allowed. -/
theorem isAllowed_frame {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    {w : Word X Y} (hw : w.IsAllowed) : Word.IsAllowed (w.frame W) :=
  PartyCircuit.isAllowed_frame W _ SourceGate.isCompatible_frame (fun _ _ _ _ _ _ _ _ h ↦ h) hw

/-- The operator of a framed word is `1 ⊗ op`. -/
theorem op_frame [Fintype P] {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (w : Word X Y) :
    Word.op (w.frame W) =
      reindex (Equiv.arrowProdEquivProdArrow P W Y).symm (Equiv.arrowProdEquivProdArrow P W X).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ w.op) :=
  PartyCircuit.op_frame W _ SourceGate.isCompatible_frame w

end Word

/-! ### Weighted gates beside spectator factors -/

/-- A weighted gate beside spectator factors: every monomial framed by the spectator factors of
its cell. -/
instance : GateFrame (WeightedGate (P := P)) where
  frame D _ _ W _ _ _ _ _ _ g := ⟨g.terms.map fun t ↦ (t.1, t.2.frame fun s : ↥D ↦ W s)⟩
  outcomeEquiv _ _ _ _ _ _ _ _ _ _ _ := Equiv.refl Unit

/-- A weighted sum of framed monomials is `1 ⊗` the weighted sum of the monomials. -/
private theorem sum_map_op_frame {D : Finset P} {X Y W : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)] :
    (L : List (ℂ × Monomial D (fun s ↦ X s) (fun s ↦ Y s))) →
      (L.map fun t ↦ t.1 • (t.2.frame fun s : ↥D ↦ W s).op chainEv).sum =
        reindex (Equiv.arrowProdEquivProdArrow {v // v ∈ D} (fun v ↦ W v) (fun v ↦ Y v)).symm
          (Equiv.arrowProdEquivProdArrow {v // v ∈ D} (fun v ↦ W v) (fun v ↦ X v)).symm
          ((1 : Matrix (RegionConfig W D) (RegionConfig W D) ℂ) ⊗ₖ
            (L.map fun t ↦ t.1 • t.2.op chainEv).sum)
  | [] => by simp
  | t :: L => by
    rw [List.map_cons, List.sum_cons, sum_map_op_frame L,
      PartyCircuit.op_frame (fun s : ↥D ↦ W s) chainEv chainEv_isCompatible_frame t.2,
      List.map_cons, List.sum_cons, kronecker_add, kronecker_smul, reindex_apply, reindex_apply,
      reindex_apply, submatrix_add, submatrix_smul]
    rfl

/-- The interpretation of weighted gates is compatible with framing. -/
theorem WeightedGate.isCompatible_frame :
    GateFrame.IsCompatible (WeightedGate (P := P)) WeightedGate.ev :=
  fun _ _ _ W _ _ _ _ _ _ g _ ↦ by
    change ((g.terms.map _).map _).sum = _
    rw [List.map_map]
    exact sum_map_op_frame (W := W) g.terms

/-- Framing keeps allowed weighted gates allowed. -/
theorem WeightedGate.isAllowed_frame {D : Finset P} {X Y W : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] [∀ p, Fintype (W p)]
    [∀ p, DecidableEq (W p)] {g : WeightedGate D X Y} (hg : WeightedGate.IsAllowed g) :
    WeightedGate.IsAllowed (GateFrame.frame W g) := by
  intro t ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  exact PartyCircuit.isAllowed_frame _ _ chainEv_isCompatible_frame
    (fun _ _ _ _ _ _ _ g h ↦ by rcases g with g | g <;> exact h) (hg t' ht')

end QuantumCircuit.Party
