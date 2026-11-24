/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.EffectCircuit
import QICLean.Circuit.Party.Syntax.Word

/-!
# Original circuits: counts, locations and expansion bounds

An original circuit (`QuantumCircuit.Party.OriginalCircuit`, in `Syntax/EffectCircuit`) is a
party circuit of original gates (gate expansions on cells of a number of parties other than one,
with allowed monomials, that are contractions) and contractive local operations. This file
collects what Theorem 5.2 reads off an original circuit:

* its *effect circuit* `toEffectCircuit`, with the same operator, the same gates
  and the same cells, gate occurrence by gate occurrence (`toEffectCircuitLocationsEquiv`,
  `participants_toEffectCircuitLocationsEquiv`);
* the number of nonprivate gates `nonprivateCount` (the gate count: every gate, the empty cell
  included, costs `1`) and the participation of a party;
* the bounds on the gate expansions: at most `r` pair effects and coefficient sum at most `S`
  (`IsExpansionBounded`), at most `K` monomials (`IsMonomialBounded`), at most `r` pair sources
  per monomial (`IsSourceBounded`), and the number of monomials of a gate (`monomialCount`).

The predicates are structural recursions on effect circuits (`EffectCircuit.IsExpansionBounded`,
…), read on original circuits through `toEffectCircuit`; their rules on the constructors hold by
`rfl`.

## Main definitions

* `QuantumCircuit.Party.EffectCircuit.IsExpansionBounded`, `IsMonomialBounded`,
  `IsSourceBounded`, `monomialCount`.
* `QuantumCircuit.Party.OriginalCircuit.nonprivateCount`, `nonprivateLocations`,
  `participants`, `participation`, `toEffectCircuitLocationsEquiv`, `IsExpansionBounded`,
  `IsMonomialBounded`, `IsSourceBounded`.

## Main results

* `QuantumCircuit.Party.OriginalCircuit.numGates_toEffectCircuit` — one gate of the effect
  circuit per nonprivate gate.
* `QuantumCircuit.Party.OriginalCircuit.card_participants_ne_one`.
* `QuantumCircuit.Party.OriginalCircuit.card_nonprivateLocations`,
  `QuantumCircuit.Party.OriginalCircuit.natCard_participants_mem`,
  `QuantumCircuit.Party.OriginalCircuit.forall_participants_of_nonprivateCount_eq_zero`.
* `QuantumCircuit.Party.OriginalCircuit.monomialCount_toEffectCircuit_le_of_isMonomialBounded`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2 `thm:compression`,
  `04-compression.tex`, lines 137–151 (statement) and 199–229 (proof).
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Bounds on the gate expansions of effect circuits -/

namespace EffectCircuit

/-- Every gate expansion has monomials with at most `r` pair effects and absolute coefficient sum at
most `S`. No restriction is imposed on the private memories. Source: `04-compression.tex`, lines
143–149 and 199–208. -/
def IsExpansionBounded (r : ℕ) (S : ℝ) : {X Y : P → Type} → EffectCircuit X Y → Prop
  | _, _, PartyCircuit.done _ => True
  | _, _, PartyCircuit.gate _ _ g =>
    (∀ t ∈ g.terms, t.2.effectCount ≤ r) ∧ (g.terms.map fun t ↦ ‖t.1‖).sum ≤ S
  | _, _, PartyCircuit.localOp _ _ _ => True
  | _, _, PartyCircuit.localOps _ => True
  | _, _, PartyCircuit.comp c c' => IsExpansionBounded r S c ∧ IsExpansionBounded r S c'

/-- Every gate expansion has at most `K` monomials. Source: `04-compression.tex`, lines 143–149 and
199–208. -/
def IsMonomialBounded (K : ℕ) : {X Y : P → Type} → EffectCircuit X Y → Prop
  | _, _, PartyCircuit.done _ => True
  | _, _, PartyCircuit.gate _ _ g => g.terms.length ≤ K
  | _, _, PartyCircuit.localOp _ _ _ => True
  | _, _, PartyCircuit.localOps _ => True
  | _, _, PartyCircuit.comp c c' => IsMonomialBounded K c ∧ IsMonomialBounded K c'

/-- Every monomial of every gate expansion has at most `r` pair sources. Source:
`04-compression.tex`, lines 143–147 ("There is a constant `r` bounding the number of pair sources,
pair effects, and polynomial-dimensional messages in each monomial"). -/
def IsSourceBounded (r : ℕ) : {X Y : P → Type} → EffectCircuit X Y → Prop
  | _, _, PartyCircuit.done _ => True
  | _, _, PartyCircuit.gate _ _ g => ∀ t ∈ g.terms, t.2.sourceCount ≤ r
  | _, _, PartyCircuit.localOp _ _ _ => True
  | _, _, PartyCircuit.localOps _ => True
  | _, _, PartyCircuit.comp c c' => IsSourceBounded r c ∧ IsSourceBounded r c'

/-- The number of monomials of the gate at an occurrence. -/
def monomialCount : {X Y : P → Type} → (c : EffectCircuit X Y) → c.gateLocations → ℕ
  | _, _, PartyCircuit.done _ => Empty.elim
  | _, _, PartyCircuit.gate _ _ g => fun _ ↦ g.terms.length
  | _, _, PartyCircuit.localOp _ _ _ => Empty.elim
  | _, _, PartyCircuit.localOps _ => Empty.elim
  | _, _, PartyCircuit.comp c c' => Sum.elim (monomialCount c) (monomialCount c')

variable {X Y Z : P → Type}

section Rules

variable [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

omit [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] in
/-- The empty circuit satisfies every expansion bound. -/
@[simp] theorem isExpansionBounded_done (r : ℕ) (S : ℝ) :
    IsExpansionBounded r S (PartyCircuit.done X : EffectCircuit X X) ↔ True :=
  Iff.rfl

/-- The expansion bound of one gate: few pair effects per monomial and a bounded coefficient sum. -/
@[simp] theorem isExpansionBounded_gate (r : ℕ) (S : ℝ) (D : Finset P)
    (hY : ∀ s ∉ D, Y s = X s) (g : WeightedGate D X Y) :
    IsExpansionBounded r S (PartyCircuit.gate D hY g : EffectCircuit X Y) ↔
      (∀ t ∈ g.terms, t.2.effectCount ≤ r) ∧ (g.terms.map fun t ↦ ‖t.1‖).sum ≤ S :=
  Iff.rfl

/-- A local operation satisfies every expansion bound. -/
@[simp] theorem isExpansionBounded_localOp (r : ℕ) (S : ℝ) (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (A : Matrix (Y p) (X p) ℂ) :
    IsExpansionBounded r S (PartyCircuit.localOp p hY A : EffectCircuit X Y) ↔ True :=
  Iff.rfl

/-- Local operations at every party satisfy every expansion bound. -/
@[simp] theorem isExpansionBounded_localOps (r : ℕ) (S : ℝ) (A : ∀ p, Matrix (Y p) (X p) ℂ) :
    IsExpansionBounded r S (PartyCircuit.localOps A : EffectCircuit X Y) ↔ True :=
  Iff.rfl

/-- A composition satisfies an expansion bound when both parts do. -/
@[simp] theorem isExpansionBounded_comp (r : ℕ) (S : ℝ) (c : EffectCircuit X Y)
    (c' : EffectCircuit Y Z) :
    IsExpansionBounded r S (PartyCircuit.comp c c') ↔
      IsExpansionBounded r S c ∧ IsExpansionBounded r S c' :=
  Iff.rfl

omit [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] in
/-- The empty circuit satisfies every monomial bound. -/
@[simp] theorem isMonomialBounded_done (K : ℕ) :
    IsMonomialBounded K (PartyCircuit.done X : EffectCircuit X X) ↔ True :=
  Iff.rfl

/-- A local operation satisfies every monomial bound. -/
@[simp] theorem isMonomialBounded_localOp (K : ℕ) (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (A : Matrix (Y p) (X p) ℂ) :
    IsMonomialBounded K (PartyCircuit.localOp p hY A : EffectCircuit X Y) ↔ True :=
  Iff.rfl

/-- Local operations at every party satisfy every monomial bound. -/
@[simp] theorem isMonomialBounded_localOps (K : ℕ) (A : ∀ p, Matrix (Y p) (X p) ℂ) :
    IsMonomialBounded K (PartyCircuit.localOps A : EffectCircuit X Y) ↔ True :=
  Iff.rfl

/-- The monomial bound of one gate: few monomials in its expansion. -/
@[simp] theorem isMonomialBounded_gate (K : ℕ) (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : WeightedGate D X Y) :
    IsMonomialBounded K (PartyCircuit.gate D hY g : EffectCircuit X Y) ↔ g.terms.length ≤ K :=
  Iff.rfl

/-- A composition satisfies a monomial bound when both parts do. -/
@[simp] theorem isMonomialBounded_comp (K : ℕ) (c : EffectCircuit X Y)
    (c' : EffectCircuit Y Z) :
    IsMonomialBounded K (PartyCircuit.comp c c') ↔
      IsMonomialBounded K c ∧ IsMonomialBounded K c' :=
  Iff.rfl

omit [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] in
/-- The empty circuit satisfies every pair-source bound. -/
@[simp] theorem isSourceBounded_done (r : ℕ) :
    IsSourceBounded r (PartyCircuit.done X : EffectCircuit X X) ↔ True :=
  Iff.rfl

/-- A local operation satisfies every pair-source bound. -/
@[simp] theorem isSourceBounded_localOp (r : ℕ) (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (A : Matrix (Y p) (X p) ℂ) :
    IsSourceBounded r (PartyCircuit.localOp p hY A : EffectCircuit X Y) ↔ True :=
  Iff.rfl

/-- Local operations at every party satisfy every pair-source bound. -/
@[simp] theorem isSourceBounded_localOps (r : ℕ) (A : ∀ p, Matrix (Y p) (X p) ℂ) :
    IsSourceBounded r (PartyCircuit.localOps A : EffectCircuit X Y) ↔ True :=
  Iff.rfl

/-- The pair-source bound of one gate: few pair sources in every monomial. -/
@[simp] theorem isSourceBounded_gate (r : ℕ) (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : WeightedGate D X Y) :
    IsSourceBounded r (PartyCircuit.gate D hY g : EffectCircuit X Y) ↔
      ∀ t ∈ g.terms, t.2.sourceCount ≤ r :=
  Iff.rfl

/-- A composition satisfies a pair-source bound when both parts do. -/
@[simp] theorem isSourceBounded_comp (r : ℕ) (c : EffectCircuit X Y) (c' : EffectCircuit Y Z) :
    IsSourceBounded r (PartyCircuit.comp c c') ↔ IsSourceBounded r c ∧ IsSourceBounded r c' :=
  Iff.rfl

/-- The number of monomials of one gate is the length of its expansion. -/
@[simp] theorem monomialCount_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : WeightedGate D X Y) (o : Unit) :
    monomialCount (PartyCircuit.gate D hY g : EffectCircuit X Y) o = g.terms.length :=
  rfl

/-- The number of monomials at an occurrence of the first part of a composition. -/
@[simp] theorem monomialCount_comp_inl (c : EffectCircuit X Y) (c' : EffectCircuit Y Z)
    (g : c.gateLocations) : monomialCount (PartyCircuit.comp c c') (.inl g) = monomialCount c g :=
  rfl

/-- The number of monomials at an occurrence of the second part of a composition. -/
@[simp] theorem monomialCount_comp_inr (c : EffectCircuit X Y) (c' : EffectCircuit Y Z)
    (g : c'.gateLocations) :
    monomialCount (PartyCircuit.comp c c') (.inr g) = monomialCount c' g :=
  rfl

end Rules

/-- Larger constants bound the expansions as well. Source: `04-compression.tex`, lines 199–208. -/
theorem IsExpansionBounded.mono {r r' : ℕ} {S S' : ℝ} (hr : r ≤ r') (hS : S ≤ S') :
    {X Y : P → Type} → {c : EffectCircuit X Y} → IsExpansionBounded r S c →
      IsExpansionBounded r' S' c
  | _, _, PartyCircuit.done _, _ => trivial
  | _, _, PartyCircuit.gate _ _ _, h => ⟨fun t ht ↦ (h.1 t ht).trans hr, h.2.trans hS⟩
  | _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, PartyCircuit.comp _ _, h => ⟨h.1.mono hr hS, h.2.mono hr hS⟩

/-- A larger constant bounds the number of monomials as well. -/
theorem IsMonomialBounded.mono {K K' : ℕ} (hK : K ≤ K') :
    {X Y : P → Type} → {c : EffectCircuit X Y} → IsMonomialBounded K c →
      IsMonomialBounded K' c
  | _, _, PartyCircuit.done _, _ => trivial
  | _, _, PartyCircuit.gate _ _ _, h => le_trans h hK
  | _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, PartyCircuit.comp _ _, h => ⟨h.1.mono hK, h.2.mono hK⟩

/-- A larger constant bounds the pair sources as well. -/
theorem IsSourceBounded.mono {r r' : ℕ} (hr : r ≤ r') :
    {X Y : P → Type} → {c : EffectCircuit X Y} → IsSourceBounded r c → IsSourceBounded r' c
  | _, _, PartyCircuit.done _, _ => trivial
  | _, _, PartyCircuit.gate _ _ _, h => fun t ht ↦ (h t ht).trans hr
  | _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, PartyCircuit.comp _ _, h => ⟨h.1.mono hr, h.2.mono hr⟩

/-- A circuit without gates satisfies every expansion bound. -/
theorem isExpansionBounded_of_numGates_eq_zero (r : ℕ) (S : ℝ) :
    {X Y : P → Type} → {c : EffectCircuit X Y} → c.numGates = 0 → IsExpansionBounded r S c
  | _, _, PartyCircuit.done _, _ => trivial
  | _, _, PartyCircuit.gate _ _ _, h => absurd h one_ne_zero
  | _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, PartyCircuit.comp _ _, h =>
    ⟨isExpansionBounded_of_numGates_eq_zero r S (Nat.add_eq_zero_iff.mp h).1,
      isExpansionBounded_of_numGates_eq_zero r S (Nat.add_eq_zero_iff.mp h).2⟩

/-- A circuit without gates satisfies every monomial bound. -/
theorem isMonomialBounded_of_numGates_eq_zero (K : ℕ) :
    {X Y : P → Type} → {c : EffectCircuit X Y} → c.numGates = 0 → IsMonomialBounded K c
  | _, _, PartyCircuit.done _, _ => trivial
  | _, _, PartyCircuit.gate _ _ _, h => absurd h one_ne_zero
  | _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, PartyCircuit.comp _ _, h =>
    ⟨isMonomialBounded_of_numGates_eq_zero K (Nat.add_eq_zero_iff.mp h).1,
      isMonomialBounded_of_numGates_eq_zero K (Nat.add_eq_zero_iff.mp h).2⟩

/-- A circuit without gates satisfies every pair-source bound. -/
theorem isSourceBounded_of_numGates_eq_zero (r : ℕ) :
    {X Y : P → Type} → {c : EffectCircuit X Y} → c.numGates = 0 → IsSourceBounded r c
  | _, _, PartyCircuit.done _, _ => trivial
  | _, _, PartyCircuit.gate _ _ _, h => absurd h one_ne_zero
  | _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, PartyCircuit.comp _ _, h =>
    ⟨isSourceBounded_of_numGates_eq_zero r (Nat.add_eq_zero_iff.mp h).1,
      isSourceBounded_of_numGates_eq_zero r (Nat.add_eq_zero_iff.mp h).2⟩

/-- The monomial bound bounds the number of monomials at every occurrence. -/
theorem monomialCount_le_of_isMonomialBounded {K : ℕ} : {X Y : P → Type} →
    {c : EffectCircuit X Y} → IsMonomialBounded K c → ∀ g, monomialCount c g ≤ K
  | _, _, PartyCircuit.done _, _, g => g.elim
  | _, _, PartyCircuit.gate _ _ _, h, _ => h
  | _, _, PartyCircuit.localOp _ _ _, _, g => g.elim
  | _, _, PartyCircuit.localOps _, _, g => g.elim
  | _, _, PartyCircuit.comp _ _, h, g => by
    rcases g with g | g
    exacts [monomialCount_le_of_isMonomialBounded h.1 g,
      monomialCount_le_of_isMonomialBounded h.2 g]

end EffectCircuit

/-! ### Original circuits -/

namespace OriginalCircuit

variable {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-! #### Gate occurrences and counts -/

/-- The number of nonprivate gates: the gate count of the circuit, every gate (the empty cell
included) costing `1`; private maps cost nothing. Source: `04-compression.tex`, lines 199–202. -/
def nonprivateCount (w : OriginalCircuit X Y) : ℕ :=
  w.toPartyCircuit.gateCount

/-- The nonprivate gate occurrences, kept distinct even when their operators coincide. Source:
`04-compression.tex`, lines 199–229. -/
abbrev nonprivateLocations (w : OriginalCircuit X Y) : Type :=
  w.toPartyCircuit.gateLocations

/-- The participants of a nonprivate gate occurrence: its cell. Source: `04-compression.tex`, lines
25–27. -/
def participants (w : OriginalCircuit X Y) (g : w.nonprivateLocations) : Finset P :=
  w.toPartyCircuit.participants g

/-- The participation of a party: the number of nonprivate gates containing it. Source:
`04-compression.tex`, lines 140–142. -/
def participation (w : OriginalCircuit X Y) (p : P) : ℕ :=
  w.toPartyCircuit.participation p

/-- Every gate is counted: the number of nonprivate gates is the number of gates. -/
theorem nonprivateCount_eq_numGates (w : OriginalCircuit X Y) :
    w.nonprivateCount = w.toPartyCircuit.numGates :=
  PartyCircuit.gateCount_eq_numGates _ w.forallGate_card_ne_one

/-- The effect circuit has exactly one gate for each nonprivate gate. Source: `04-compression.tex`,
lines 199–217. -/
theorem numGates_toEffectCircuit (w : OriginalCircuit X Y) :
    w.toEffectCircuit.numGates = w.nonprivateCount :=
  (PartyCircuit.numGates_mapGates _ _).trans w.nonprivateCount_eq_numGates.symm

/-- The effect circuit has the gate count of the original circuit. -/
theorem gateCount_toEffectCircuit (w : OriginalCircuit X Y) :
    w.toEffectCircuit.gateCount = w.nonprivateCount :=
  PartyCircuit.gateCount_mapGates _ _

/-- The effect circuit neither merges nor creates gate occurrences. Source: `04-compression.tex`,
lines 199–229. -/
def toEffectCircuitLocationsEquiv (w : OriginalCircuit X Y) :
    w.nonprivateLocations ≃ w.toEffectCircuit.gateLocations :=
  PartyCircuit.mapGatesLocationsEquiv _ w.toPartyCircuit

/-- The occurrence correspondence keeps the cells. Source: `04-compression.tex`, line 229. -/
theorem participants_toEffectCircuitLocationsEquiv (w : OriginalCircuit X Y)
    (g : w.nonprivateLocations) :
    w.toEffectCircuit.participants (w.toEffectCircuitLocationsEquiv g) = w.participants g :=
  PartyCircuit.participants_mapGatesLocationsEquiv _ _ g

/-- **No nonprivate occurrence has exactly one participant.** Empty cells are permitted, as in the
manuscript. Source: `04-compression.tex`, lines 25–27. -/
theorem card_participants_ne_one (w : OriginalCircuit X Y) (g : w.nonprivateLocations) :
    (w.participants g).card ≠ 1 :=
  PartyCircuit.forall_participants_of_forallGate w.forallGate_card_ne_one g

/-- The finite set of nonprivate occurrences has the gate count. Source: `04-compression.tex`, lines
199–229. -/
theorem natCard_nonprivateLocations (w : OriginalCircuit X Y) :
    Nat.card w.nonprivateLocations = w.nonprivateCount :=
  Nat.card_eq_fintype_card.trans
    ((PartyCircuit.card_gateLocations _).trans w.nonprivateCount_eq_numGates.symm)

/-- The finite enumeration of the nonprivate occurrences has the gate count. -/
theorem card_nonprivateLocations (w : OriginalCircuit X Y) :
    Fintype.card w.nonprivateLocations = w.nonprivateCount :=
  (PartyCircuit.card_gateLocations _).trans w.nonprivateCount_eq_numGates.symm

/-- A circuit without nonprivate gates has no nonprivate gate occurrence. -/
theorem isEmpty_nonprivateLocations_of_nonprivateCount_eq_zero {w : OriginalCircuit X Y}
    (h : w.nonprivateCount = 0) : IsEmpty w.nonprivateLocations :=
  Fintype.card_eq_zero_iff.mp (w.card_nonprivateLocations.trans h)

/-- Every condition on the participants of the nonprivate gates holds for a circuit without
nonprivate gates. -/
theorem forall_participants_of_nonprivateCount_eq_zero {Q : Finset P → Prop}
    {w : OriginalCircuit X Y} (h : w.nonprivateCount = 0) (g : w.nonprivateLocations) :
    Q (w.participants g) :=
  ((isEmpty_nonprivateLocations_of_nonprivateCount_eq_zero h).false g).elim

/-- The participation of a party is the number of gates containing it (no gate is private). -/
theorem participation_eq_participationCount (w : OriginalCircuit X Y) (p : P) :
    w.participation p = w.toPartyCircuit.participationCount p :=
  PartyCircuit.participation_eq_participationCount p _ w.forallGate_card_ne_one

/-- The participation of a party is the number of nonprivate occurrences containing it. Source:
`04-compression.tex`, lines 140–142. -/
theorem natCard_participants_mem (w : OriginalCircuit X Y) (p : P) :
    Nat.card {g : w.nonprivateLocations // p ∈ w.participants g} = w.participation p :=
  (PartyCircuit.natCard_participants_mem p _).trans (w.participation_eq_participationCount p).symm

/-- The effect circuit has the participations of the original circuit. -/
theorem participation_toEffectCircuit (w : OriginalCircuit X Y) (p : P) :
    w.toEffectCircuit.participation p = w.participation p :=
  PartyCircuit.participation_mapGates _ p _

/-- Every occurrence containing a party belongs to exactly one of two successive circuits. Source:
`04-compression.tex`, lines 140–142. -/
theorem participation_comp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (w : OriginalCircuit X Y) (w' : OriginalCircuit Y Z) (p : P) :
    (w.comp w').participation p = w.participation p + w'.participation p :=
  rfl

/-- The number of nonprivate gates of a composition. -/
theorem nonprivateCount_comp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (w : OriginalCircuit X Y) (w' : OriginalCircuit Y Z) :
    (w.comp w').nonprivateCount = w.nonprivateCount + w'.nonprivateCount :=
  rfl

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- The empty circuit has no nonprivate gate. -/
@[simp] theorem nonprivateCount_done (X : P → Type) [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] : (done X).nonprivateCount = 0 :=
  rfl

/-- One original gate is one nonprivate gate (an empty cell included). -/
@[simp] theorem nonprivateCount_gate [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : OriginalGate D X Y) :
    (gate D hY g).nonprivateCount = 1 :=
  ite_eq_right g.card_ne_one

/-- A private contraction is not counted. -/
@[simp] theorem nonprivateCount_localOp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (p : P)
    (hY : ∀ s ≠ p, Y s = X s) (U : Matrix (Y p) (X p) ℂ) (hU : ‖U‖ ≤ 1) :
    (localOp p hY U hU).nonprivateCount = 0 :=
  rfl

/-- Contractions at every party are not counted. -/
@[simp] theorem nonprivateCount_localOps [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (U : ∀ p, Matrix (Y p) (X p) ℂ) (hU : ∀ p, ‖U p‖ ≤ 1) :
    (localOps U hU).nonprivateCount = 0 :=
  rfl

/-! #### Expansion bounds -/

/-- Original pair-effect and coefficient-sum bounds, before the insertion averages are expanded.
Source: `04-compression.tex`, lines 199–208. -/
def IsExpansionBounded (r : ℕ) (S : ℝ) (w : OriginalCircuit X Y) : Prop :=
  w.toEffectCircuit.IsExpansionBounded r S

/-- The original monomial count is bounded. Source: `04-compression.tex`, lines 199–208. -/
def IsMonomialBounded (K : ℕ) (w : OriginalCircuit X Y) : Prop :=
  w.toEffectCircuit.IsMonomialBounded K

/-- Every monomial of every gate expansion has at most `r` pair sources. Source: Theorem 5.2, item
3, `04-compression.tex`, lines 143–147. -/
def IsSourceBounded (r : ℕ) (w : OriginalCircuit X Y) : Prop :=
  w.toEffectCircuit.IsSourceBounded r

/-- The effect circuit has exactly the original expansion bounds. Source: `04-compression.tex`,
lines 199–208. -/
theorem isExpansionBounded_toEffectCircuit_iff (w : OriginalCircuit X Y) (r : ℕ) (S : ℝ) :
    w.toEffectCircuit.IsExpansionBounded r S ↔ w.IsExpansionBounded r S :=
  Iff.rfl

section Rules

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- A composition satisfies an expansion bound when both parts do. -/
@[simp] theorem isExpansionBounded_comp (r : ℕ) (S : ℝ) (w : OriginalCircuit X Y)
    (w' : OriginalCircuit Y Z) :
    (w.comp w').IsExpansionBounded r S ↔ w.IsExpansionBounded r S ∧ w'.IsExpansionBounded r S :=
  Iff.rfl

/-- The expansion bound of one gate: few pair effects per monomial and a bounded coefficient sum. -/
@[simp] theorem isExpansionBounded_gate (r : ℕ) (S : ℝ) (D : Finset P)
    (hY : ∀ s ∉ D, Y s = X s) (g : OriginalGate D X Y) :
    (gate D hY g).IsExpansionBounded r S ↔
      (∀ t ∈ g.toWeightedGate.terms, t.2.effectCount ≤ r) ∧
        (g.toWeightedGate.terms.map fun t ↦ ‖t.1‖).sum ≤ S :=
  Iff.rfl

/-- A composition satisfies a monomial bound when both parts do. -/
@[simp] theorem isMonomialBounded_comp (K : ℕ) (w : OriginalCircuit X Y)
    (w' : OriginalCircuit Y Z) :
    (w.comp w').IsMonomialBounded K ↔ w.IsMonomialBounded K ∧ w'.IsMonomialBounded K :=
  Iff.rfl

/-- The monomial bound of one gate: few monomials in its expansion. -/
@[simp] theorem isMonomialBounded_gate (K : ℕ) (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : OriginalGate D X Y) :
    (gate D hY g).IsMonomialBounded K ↔ g.toWeightedGate.terms.length ≤ K :=
  Iff.rfl

/-- A composition satisfies a pair-source bound when both parts do. -/
@[simp] theorem isSourceBounded_comp (r : ℕ) (w : OriginalCircuit X Y)
    (w' : OriginalCircuit Y Z) :
    (w.comp w').IsSourceBounded r ↔ w.IsSourceBounded r ∧ w'.IsSourceBounded r :=
  Iff.rfl

/-- The pair-source bound of one gate: few pair sources in every monomial. -/
@[simp] theorem isSourceBounded_gate (r : ℕ) (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : OriginalGate D X Y) :
    (gate D hY g).IsSourceBounded r ↔ ∀ t ∈ g.toWeightedGate.terms, t.2.sourceCount ≤ r :=
  Iff.rfl

end Rules

/-- Larger constants preserve the original expansion condition. Source: `04-compression.tex`, lines
199–208. -/
theorem isExpansionBounded_mono (w : OriginalCircuit X Y) {r r' : ℕ} {S S' : ℝ}
    (h : w.IsExpansionBounded r S) (hr : r ≤ r') (hS : S ≤ S') : w.IsExpansionBounded r' S' :=
  EffectCircuit.IsExpansionBounded.mono hr hS h

/-- A larger monomial bound preserves the original condition. Source: `04-compression.tex`, lines
137–151. -/
theorem isMonomialBounded_mono (w : OriginalCircuit X Y) {K K' : ℕ}
    (h : w.IsMonomialBounded K) (hK : K ≤ K') : w.IsMonomialBounded K' :=
  EffectCircuit.IsMonomialBounded.mono hK h

/-- A larger constant bounds the pair sources as well. -/
theorem IsSourceBounded.mono {w : OriginalCircuit X Y} {r r' : ℕ} (h : w.IsSourceBounded r)
    (hr : r ≤ r') : w.IsSourceBounded r' :=
  EffectCircuit.IsSourceBounded.mono hr h

/-- A circuit without nonprivate gates satisfies the pair-source bound with every constant. -/
theorem isSourceBounded_of_nonprivateCount_eq_zero {w : OriginalCircuit X Y}
    (h0 : w.nonprivateCount = 0) (r : ℕ) : w.IsSourceBounded r :=
  EffectCircuit.isSourceBounded_of_numGates_eq_zero r (w.numGates_toEffectCircuit.trans h0)

/-- A circuit without nonprivate gates satisfies every expansion bound. -/
theorem isExpansionBounded_of_nonprivateCount_eq_zero {w : OriginalCircuit X Y}
    (h0 : w.nonprivateCount = 0) (r : ℕ) (S : ℝ) : w.IsExpansionBounded r S :=
  EffectCircuit.isExpansionBounded_of_numGates_eq_zero r S (w.numGates_toEffectCircuit.trans h0)

/-- A circuit without nonprivate gates satisfies every monomial bound. -/
theorem isMonomialBounded_of_nonprivateCount_eq_zero {w : OriginalCircuit X Y}
    (h0 : w.nonprivateCount = 0) (K : ℕ) : w.IsMonomialBounded K :=
  EffectCircuit.isMonomialBounded_of_numGates_eq_zero K (w.numGates_toEffectCircuit.trans h0)

/-- **Every gate of the effect circuit keeps its original monomial bound**. Source: Theorem 5.2,
`04-compression.tex`, lines 143–149 and 199–208. -/
theorem monomialCount_toEffectCircuit_le_of_isMonomialBounded (w : OriginalCircuit X Y)
    {K : ℕ} (h : w.IsMonomialBounded K) (g : w.toEffectCircuit.gateLocations) :
    w.toEffectCircuit.monomialCount g ≤ K :=
  EffectCircuit.monomialCount_le_of_isMonomialBounded h g

end OriginalCircuit

end QuantumCircuit.Party
