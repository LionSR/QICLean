/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Gates
import QICLean.Circuit.Party.Syntax.Relabel

/-!
# Weighted gates, effect circuits and original circuits

A gate of the party calculus on a cell `D` is given by a gate expansion: a weighted list of
monomials on the parties of `D` (`WeightedGate`), whose matrix is the weighted sum of the
operators of the monomials. An *effect circuit* is a party circuit of such gates.

## Original circuits: gates carrying their conditions

The conditions on the gates of an original circuit are fields of its gates, so that a proof by
recursion on the constructors of the party circuit has them in hand:

* `OriginalGate D X Y` — a weighted gate (its gate expansion) on the cell `D` with the fields
  `card_ne_one : D.card ≠ 1` (the gate is not private) and `monomials_allowed`,
  `norm_ev_le_one` (allowed monomials, a contraction), the last two quantified over the
  finiteness instances they read, as for prepared source gates;
* `OriginalCircuit X Y` — a structure: a party circuit over `OriginalGate` and the single field
  `localAllowed` (the local operations are contractions, `PartyCircuit.IsLocalContractive`).

The smart constructors `done`, `gate`, `localOp`, `localOps`, `comp` project to the constructors
of the party circuit by `rfl`, and `OriginalCircuit.induction` is an eliminator in their shape.
The effect circuit of an original circuit forgets the conditions (`toEffectCircuit`, a
`mapGates`). Theorems about original circuits carry no side hypothesis.

## Main definitions

* `QuantumCircuit.Party.OriginalGate`, `QuantumCircuit.Party.OriginalGate.ev`,
  `QuantumCircuit.Party.OriginalGate.ofWeightedGate` — an original gate from a gate expansion
  with allowed monomials that is a contraction.
* `QuantumCircuit.Party.OriginalCircuit`, its constructors `done`, `gate`, `localOp`,
  `localOps`, `comp`, `QuantumCircuit.Party.OriginalCircuit.op`,
  `QuantumCircuit.Party.OriginalCircuit.toEffectCircuit`.

## Main results

* `QuantumCircuit.Party.OriginalCircuit.induction` — the eliminator.
* `QuantumCircuit.Party.OriginalCircuit.op_done`, `op_comp`, `op_gate`, `op_localOp`,
  `op_localOps` — the operator, constructor by constructor.
* `QuantumCircuit.Party.OriginalCircuit.isAllowed`, `norm_op_le_one` — an original circuit is
  allowed and a contraction.
* `QuantumCircuit.Party.OriginalCircuit.forallGate_card_ne_one`, `nonprivate` — no gate is
  private (the former field `nonprivate`).
* `QuantumCircuit.Party.OriginalCircuit.op_toEffectCircuit`, `isAllowed_toEffectCircuit` — the
  effect circuit (the former field `toEffectCircuit` and `allowed`).

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 21–36 (gates and
  private operations), 53–57 (gate expansions), 199–216 (nonprivate gates).
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Monomials and weighted gates -/

/-- A gate on the cell `D`: a weighted list of monomials on the parties of `D`, its gate
expansion. Source: `04-compression.tex`, lines 25–35 and 53–57. -/
structure WeightedGate (D : Finset P) (X Y : P → Type) : Type 1 where
  /-- The coefficients and the monomials. -/
  terms : List (ℂ × Monomial D (fun s ↦ X s) (fun s ↦ Y s))

/-- A weighted gate has one outcome. -/
instance : GateFamily (S := P) WeightedGate where
  Outcome _ := Unit
  fintype _ := inferInstance

/-- Weighted gates have one outcome each. -/
instance : GateFamily.UniqueOutcome (S := P) WeightedGate where
  nonempty_unique _ _ _ _ := ⟨inferInstanceAs (Unique Unit)⟩

/-- The matrix of a weighted gate: the weighted sum of the operators of its monomials. -/
noncomputable def WeightedGate.ev : Interpretation (S := P) WeightedGate :=
  fun g _ ↦ (g.terms.map fun t ↦ t.1 • t.2.op chainEv).sum

/-- A weighted gate is allowed when every monomial is allowed: its local operations are
contractions and its pair sources and effects normalized. Source: `04-compression.tex`,
lines 32–35. -/
def WeightedGate.IsAllowed : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)],
    WeightedGate D X Y → Prop :=
  fun _ _ _ _ _ _ _ g ↦ ∀ t ∈ g.terms, t.2.IsAllowed chainEv ChainGate.IsAllowed

/-- Effect circuits: party circuits of weighted gates, with no side condition. -/
abbrev EffectCircuit (X Y : P → Type) := PartyCircuit (WeightedGate (P := P)) X Y

/-! ### Original gates -/

/-- An original nonprivate gate on the cell `D`: a weighted list of monomials on the parties of
`D` (its gate expansion), whose number of parties is not one, whose monomials are allowed and
whose matrix is a contraction. The last two conditions read the finiteness instances of the
systems and are stated for all of them. The empty cell is allowed. Source:
`04-compression.tex`, lines 21–36, 53–57 and 199–216. -/
structure OriginalGate (D : Finset P) (X Y : P → Type) : Type 1 where
  /-- The gate expansion. -/
  toWeightedGate : WeightedGate D X Y
  /-- The gate is not private: it does not act on exactly one party. Source: lines 25–27 and
  199–202. -/
  card_ne_one : D.card ≠ 1
  /-- The monomials of the expansion are allowed. Source: lines 32–35. -/
  monomials_allowed : ∀ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)], WeightedGate.IsAllowed toWeightedGate
  /-- The gate is a contraction. Source: line 28. -/
  norm_ev_le_one : ∀ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)], ‖WeightedGate.ev toWeightedGate ()‖ ≤ 1

/-- An original gate has one outcome. -/
instance : GateFamily (S := P) OriginalGate where
  Outcome _ := Unit
  fintype _ := inferInstance

/-- Original gates have one outcome each. -/
instance : GateFamily.UniqueOutcome (S := P) OriginalGate where
  nonempty_unique _ _ _ _ := ⟨inferInstanceAs (Unique Unit)⟩

/-- The interpretation of original gates: the matrix of the gate expansion. -/
noncomputable def OriginalGate.ev : Interpretation (S := P) OriginalGate :=
  fun g o ↦ WeightedGate.ev g.toWeightedGate o

/-- Forgetting the conditions of original gates. -/
def OriginalGate.toWeightedGateMorphism : GateMorphism (S := P) OriginalGate WeightedGate where
  map _ _ _ g := g.toWeightedGate
  outcome _ _ _ _ := Equiv.refl Unit

/-- Forgetting the conditions keeps the matrices. -/
theorem OriginalGate.isCompatible_toWeightedGateMorphism :
    (OriginalGate.toWeightedGateMorphism (P := P)).IsCompatible OriginalGate.ev
      WeightedGate.ev :=
  fun _ _ _ _ _ _ _ _ _ ↦ rfl

/-- An original gate from a gate expansion on a cell of a number of parties other than one, with
allowed monomials and a contraction, both conditions proved for the given finiteness and
decidability structures of the systems (any two such structures agree). -/
def OriginalGate.ofWeightedGate {D : Finset P} {X Y : P → Type} [iFX : ∀ p, Fintype (X p)]
    [iDX : ∀ p, DecidableEq (X p)] [iFY : ∀ p, Fintype (Y p)] [iDY : ∀ p, DecidableEq (Y p)]
    (g : WeightedGate D X Y) (hD : D.card ≠ 1) (hA : WeightedGate.IsAllowed g)
    (hN : ‖WeightedGate.ev g ()‖ ≤ 1) : OriginalGate D X Y where
  toWeightedGate := g
  card_ne_one := hD
  monomials_allowed := @fun i1 i2 i3 i4 ↦ by
    obtain rfl : i1 = iFX := Subsingleton.elim _ _
    obtain rfl : i2 = iDX := Subsingleton.elim _ _
    obtain rfl : i3 = iFY := Subsingleton.elim _ _
    obtain rfl : i4 = iDY := Subsingleton.elim _ _
    exact hA
  norm_ev_le_one := @fun i1 i2 i3 i4 ↦ by
    obtain rfl : i1 = iFX := Subsingleton.elim _ _
    obtain rfl : i2 = iDX := Subsingleton.elim _ _
    obtain rfl : i3 = iFY := Subsingleton.elim _ _
    obtain rfl : i4 = iDY := Subsingleton.elim _ _
    exact hN

/-- The gate expansion of an original gate built from a weighted gate is that weighted gate. -/
@[simp] theorem OriginalGate.toWeightedGate_ofWeightedGate {D : Finset P} {X Y : P → Type}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (g : WeightedGate D X Y) (hD : D.card ≠ 1) (hA : WeightedGate.IsAllowed g)
    (hN : ‖WeightedGate.ev g ()‖ ≤ 1) :
    (OriginalGate.ofWeightedGate g hD hA hN).toWeightedGate = g :=
  rfl

/-! ### Circuits of original gates -/

namespace PartyCircuit

variable {G : Finset P → (P → Type) → (P → Type) → Type 1}

/-- A circuit of original gates with contractive local operations is allowed: its gates are
contractions with allowed monomials. -/
theorem isAllowed_of_isLocalContractive :
    {X Y : P → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      {c : PartyCircuit OriginalGate X Y} → c.IsLocalContractive →
        c.IsAllowed OriginalGate.ev fun _ _ _ _ _ _ _ g ↦ WeightedGate.IsAllowed g.toWeightedGate
  | _, _, _, _, done _, _ => trivial
  | _, _, _, _, @gate _ _ _ _ _ _ _ _ g, _ => ⟨g.norm_ev_le_one, g.monomials_allowed⟩
  | _, _, _, _, localOp _ _ _, h => h
  | _, _, _, _, localOps _, h => h
  | _, _, _, _, comp _ _, h =>
    ⟨isAllowed_of_isLocalContractive h.1, isAllowed_of_isLocalContractive h.2⟩

/-- No gate of a circuit of original gates is private. -/
theorem forallGate_card_ne_one : {X Y : P → Type} → (c : PartyCircuit OriginalGate X Y) →
    c.ForallGate fun D _ _ _ ↦ D.card ≠ 1
  | _, _, done _ => trivial
  | _, _, gate _ _ g => g.card_ne_one
  | _, _, localOp _ _ _ => trivial
  | _, _, localOps _ => trivial
  | _, _, comp c c' => ⟨forallGate_card_ne_one c, forallGate_card_ne_one c'⟩

/-- Forgetting the conditions keeps the cells: no gate of the effect circuit is private. -/
theorem forallGate_card_ne_one_mapGates : {X Y : P → Type} →
    (c : PartyCircuit OriginalGate X Y) →
      (c.mapGates OriginalGate.toWeightedGateMorphism).ForallGate fun D _ _ _ ↦ D.card ≠ 1
  | _, _, done _ => trivial
  | _, _, gate _ _ g => g.card_ne_one
  | _, _, localOp _ _ _ => trivial
  | _, _, localOps _ => trivial
  | _, _, comp c c' =>
    ⟨forallGate_card_ne_one_mapGates c, forallGate_card_ne_one_mapGates c'⟩

end PartyCircuit

/-! ### Original circuits -/

/-- An original circuit: a party circuit of original gates whose local operations are
contractions. The conditions on the gates (not private, allowed monomials, contraction) are
fields of the gates. Source: `04-compression.tex`, lines 21–36 and 199–216. -/
structure OriginalCircuit (X Y : P → Type) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] :
    Type 1 where
  /-- The underlying party circuit. -/
  toPartyCircuit : PartyCircuit (OriginalGate (P := P)) X Y
  /-- The local operations are contractions. -/
  localAllowed : toPartyCircuit.IsLocalContractive

namespace OriginalCircuit

variable {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-! #### Constructors -/

/-- The empty original circuit (old `OriginalCircuit.id`). -/
def done (X : P → Type) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] : OriginalCircuit X X :=
  ⟨PartyCircuit.done X, trivial⟩

/-- Composition, in chronological order: first `w`, then `w'`. -/
def comp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (w : OriginalCircuit X Y)
    (w' : OriginalCircuit Y Z) : OriginalCircuit X Z :=
  ⟨w.toPartyCircuit.comp w'.toPartyCircuit, ⟨w.localAllowed, w'.localAllowed⟩⟩

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- One original gate on its cell, the other parties spectators (old `nonprivateGate`). -/
def gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : OriginalGate D X Y) :
    OriginalCircuit X Y :=
  ⟨PartyCircuit.gate D hY g, trivial⟩

/-- An arbitrary contraction of one party (old `privateMap`). -/
def localOp (p : P) (hY : ∀ s ≠ p, Y s = X s) (U : Matrix (Y p) (X p) ℂ) (hU : ‖U‖ ≤ 1) :
    OriginalCircuit X Y :=
  ⟨PartyCircuit.localOp p hY U, hU⟩

/-- Contractions of every party at once. -/
def localOps (U : ∀ p, Matrix (Y p) (X p) ℂ) (hU : ∀ p, ‖U p‖ ≤ 1) : OriginalCircuit X Y :=
  ⟨PartyCircuit.localOps U, hU⟩

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
@[simp] theorem toPartyCircuit_done : (done X).toPartyCircuit = PartyCircuit.done X :=
  rfl

@[simp] theorem toPartyCircuit_comp (w : OriginalCircuit X Y) (w' : OriginalCircuit Y Z) :
    (w.comp w').toPartyCircuit = w.toPartyCircuit.comp w'.toPartyCircuit :=
  rfl

@[simp] theorem toPartyCircuit_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : OriginalGate D X Y) : (gate D hY g).toPartyCircuit = PartyCircuit.gate D hY g :=
  rfl

@[simp] theorem toPartyCircuit_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (U : Matrix (Y p) (X p) ℂ) (hU : ‖U‖ ≤ 1) :
    (localOp p hY U hU).toPartyCircuit = PartyCircuit.localOp p hY U :=
  rfl

@[simp] theorem toPartyCircuit_localOps (U : ∀ p, Matrix (Y p) (X p) ℂ)
    (hU : ∀ p, ‖U p‖ ≤ 1) : (localOps U hU).toPartyCircuit = PartyCircuit.localOps U :=
  rfl

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)] in
/-- The constructor form of an original circuit, for the eliminator. -/
private theorem induction_aux
    {motive : ∀ {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)],
      OriginalCircuit X Y → Prop}
    (done : ∀ (X : P → Type) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)],
      motive (OriginalCircuit.done X))
    (comp : ∀ {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (w : OriginalCircuit X Y)
      (w' : OriginalCircuit Y Z), motive w → motive w' → motive (w.comp w'))
    (gate : ∀ {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
      (g : OriginalGate D X Y), motive (OriginalCircuit.gate D hY g))
    (localOp : ∀ {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (p : P) (hY : ∀ s ≠ p, Y s = X s)
      (U : Matrix (Y p) (X p) ℂ) (hU : ‖U‖ ≤ 1), motive (OriginalCircuit.localOp p hY U hU))
    (localOps : ∀ {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (U : ∀ p, Matrix (Y p) (X p) ℂ)
      (hU : ∀ p, ‖U p‖ ≤ 1), motive (OriginalCircuit.localOps U hU)) :
    ∀ {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      (c : PartyCircuit OriginalGate X Y) (hc : c.IsLocalContractive), motive ⟨c, hc⟩
  | _, _, _, _, PartyCircuit.done X, _ => done X
  | _, _, _, _, PartyCircuit.gate D hY g, _ => gate D hY g
  | _, _, _, _, PartyCircuit.localOp p hY U, hc => localOp p hY U hc
  | _, _, _, _, PartyCircuit.localOps U, hc => localOps U hc
  | _, _, _, _, PartyCircuit.comp c c', hc =>
    comp ⟨c, hc.1⟩ ⟨c', hc.2⟩
      (induction_aux done comp gate localOp localOps c hc.1)
      (induction_aux done comp gate localOp localOps c' hc.2)

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Induction on the constructors of `OriginalCircuit` (old `OriginalCircuit.induction`; the
old `swap` and `frame` cases are gone, `localOps` is new, the gate case carries its conditions
inside the gate `g`). -/
@[induction_eliminator, elab_as_elim]
theorem induction
    {motive : ∀ {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)],
      OriginalCircuit X Y → Prop}
    (done : ∀ (X : P → Type) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)],
      motive (OriginalCircuit.done X))
    (comp : ∀ {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (w : OriginalCircuit X Y)
      (w' : OriginalCircuit Y Z), motive w → motive w' → motive (w.comp w'))
    (gate : ∀ {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
      (g : OriginalGate D X Y), motive (OriginalCircuit.gate D hY g))
    (localOp : ∀ {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (p : P) (hY : ∀ s ≠ p, Y s = X s)
      (U : Matrix (Y p) (X p) ℂ) (hU : ‖U‖ ≤ 1), motive (OriginalCircuit.localOp p hY U hU))
    (localOps : ∀ {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (U : ∀ p, Matrix (Y p) (X p) ℂ)
      (hU : ∀ p, ‖U p‖ ≤ 1), motive (OriginalCircuit.localOps U hU))
    (w : OriginalCircuit X Y) : motive w :=
  induction_aux done comp gate localOp localOps w.toPartyCircuit w.localAllowed

/-! #### The operator -/

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The operator of an original circuit. -/
noncomputable def op [Fintype P] (w : OriginalCircuit X Y) : Matrix (Config Y) (Config X) ℂ :=
  w.toPartyCircuit.op OriginalGate.ev

section Op

variable [Fintype P]

/-- The empty original circuit applies the identity. -/
@[simp] theorem op_done : (done X).op = 1 :=
  rfl

/-- The operator of a composition is the product of the operators, the first on the right. -/
@[simp] theorem op_comp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (w : OriginalCircuit X Y)
    (w' : OriginalCircuit Y Z) : (w.comp w').op = w'.op * w.op :=
  PartyCircuit.op_comp _ _ _

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The operator of one original gate is the placement of the matrix of its expansion. -/
@[simp] theorem op_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : OriginalGate D X Y) :
    (gate D hY g).op = placeBetween D hY (WeightedGate.ev g.toWeightedGate ()) :=
  PartyCircuit.op_gate _ D hY g

/-- The operator of one private contraction is its placement at the party. -/
@[simp] theorem op_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s) (U : Matrix (Y p) (X p) ℂ)
    (hU : ‖U‖ ≤ 1) :
    (localOp p hY U hU).op =
      placeBetween {p} (fun s hs ↦ hY s (Finset.notMem_singleton.mp hs))
        (U.submatrix (fun y ↦ y ⟨p, Finset.mem_singleton_self p⟩)
          (fun x ↦ x ⟨p, Finset.mem_singleton_self p⟩)) :=
  PartyCircuit.op_localOp _ p hY U

/-- The operator of contractions at every party is their Kronecker product. -/
@[simp] theorem op_localOps (U : ∀ p, Matrix (Y p) (X p) ℂ) (hU : ∀ p, ‖U p‖ ≤ 1) :
    (localOps U hU).op = piKronecker U :=
  PartyCircuit.op_localOps _ U

end Op

/-! #### Allowedness and contraction -/

/-- An original circuit is allowed: contractive local operations and gates, allowed
monomials. Source: `04-compression.tex`, lines 28 and 32–35. -/
theorem isAllowed (w : OriginalCircuit X Y) :
    w.toPartyCircuit.IsAllowed OriginalGate.ev
      fun _ _ _ _ _ _ _ g ↦ WeightedGate.IsAllowed g.toWeightedGate :=
  PartyCircuit.isAllowed_of_isLocalContractive w.localAllowed

/-- **An original circuit is a contraction.** Source: `04-compression.tex`, line 28 and
lines 215–216. -/
theorem norm_op_le_one [Fintype P] [∀ p, Fintype (Y p)] (w : OriginalCircuit X Y) :
    ‖w.op‖ ≤ 1 :=
  PartyCircuit.norm_op_le_one _ w.isAllowed

/-- No gate of an original circuit acts on exactly one party (the former field
`nonprivate`, on the circuit of original gates). Source: `04-compression.tex`, lines 199–202. -/
theorem forallGate_card_ne_one (w : OriginalCircuit X Y) :
    w.toPartyCircuit.ForallGate fun D _ _ _ ↦ D.card ≠ 1 :=
  PartyCircuit.forallGate_card_ne_one _

/-! #### The effect circuit -/

/-- The effect circuit of an original circuit: the same syntax with the conditions forgotten
(the former field `toEffectCircuit`; old `produce`). Source: `04-compression.tex`,
lines 199–212. -/
def toEffectCircuit (w : OriginalCircuit X Y) : EffectCircuit X Y :=
  w.toPartyCircuit.mapGates OriginalGate.toWeightedGateMorphism

/-- The effect circuit has the operator of the original circuit (old `eval_produce`). -/
theorem op_toEffectCircuit [Fintype P] (w : OriginalCircuit X Y) :
    w.toEffectCircuit.op WeightedGate.ev = w.op :=
  PartyCircuit.op_mapGates _ OriginalGate.isCompatible_toWeightedGateMorphism _

/-- The effect circuit is allowed (the former field `allowed`; old `isAllowed_produce`). -/
theorem isAllowed_toEffectCircuit (w : OriginalCircuit X Y) :
    w.toEffectCircuit.IsAllowed WeightedGate.ev WeightedGate.IsAllowed :=
  PartyCircuit.IsAllowed.mapGates _ OriginalGate.isCompatible_toWeightedGateMorphism
    (fun _ _ _ _ _ _ _ _ h ↦ h) w.isAllowed

/-- No gate of the effect circuit is private (the former field `nonprivate`). -/
theorem nonprivate (w : OriginalCircuit X Y) :
    w.toEffectCircuit.ForallGate fun D _ _ _ ↦ D.card ≠ 1 :=
  PartyCircuit.forallGate_card_ne_one_mapGates _

end OriginalCircuit

end QuantumCircuit.Party
