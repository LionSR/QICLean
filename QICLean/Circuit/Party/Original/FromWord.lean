/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Original.PairGate

/-!
# Allowed monomials as original circuits

An allowed monomial of Theorem 5.2 is a composition of local contractions, normalized pair
sources and normalized pair effects. Read operation by operation it is an original circuit:
every local contraction is a private map of its party, and every pair source and every pair
effect is a nonprivate gate on the cell of its two endpoints, whose gate expansion is the one
monomial "this gate" with coefficient one (`WeightedGate.single`, `ChainGate.toMonomial`).

This is how changes given as monomials enter a protocol: each change is a fixed number of
nonprivate gates whose participants are parties named by the change (Proposition 7.1 of the
source, `06-geometry.tex`, lines 574–583).

## Main definitions

* `QuantumCircuit.Party.Word.toOriginalCircuit`, `QuantumCircuit.Party.Monomial.toOriginalCircuit`
  (the gates are those of `Original/PairGate`).

## Main results

* `QuantumCircuit.Party.Word.op_toOriginalCircuit`,
  `QuantumCircuit.Party.Monomial.op_toOriginalCircuit`.
* `nonprivateCount_toOriginalCircuit`: one nonprivate gate per pair source and pair effect.
* `participants_toOriginalCircuit_subset`, `isExpansionBounded_toOriginalCircuit`,
  `isMonomialBounded_toOriginalCircuit`, `isSourceBounded_toOriginalCircuit` and their forms
  `_of_one_le` and `_of_sourceCount_eq_zero`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 21–43
  (allowed monomials), 143–147 (pair-source bound) and 199–208 (original circuits);
  `06-geometry.tex`, lines 574–583.
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Source-only words -/

namespace Word

/-- A source-only word as an original circuit: a local contraction is a private map of its party, a
normalized pair source a two-party nonprivate gate. Source: `04-compression.tex`, lines 21–43. -/
noncomputable def toOriginalCircuit : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → w.IsAllowed → OriginalCircuit X Y
  | _, _, _, _, PartyCircuit.done X, _ => OriginalCircuit.done X
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g, h =>
    OriginalCircuit.gate D hY (OriginalGate.ofChainGate (.inl g) h.2)
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY U, h => OriginalCircuit.localOp p hY U h
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ U, h => OriginalCircuit.localOps U h
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', h =>
    (toOriginalCircuit c h.1).comp (toOriginalCircuit c' h.2)

variable {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- The empty word is the empty original circuit. -/
@[simp] theorem toOriginalCircuit_done (h : Word.IsAllowed (PartyCircuit.done X : Word X X)) :
    toOriginalCircuit (PartyCircuit.done X) h = OriginalCircuit.done X :=
  rfl

/-- The original circuit of a composition of words is the composition. -/
@[simp] theorem toOriginalCircuit_comp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (w : Word X Y) (w' : Word Y Z) (h : Word.IsAllowed (PartyCircuit.comp w w')) :
    toOriginalCircuit (PartyCircuit.comp w w') h =
      (toOriginalCircuit w h.1).comp (toOriginalCircuit w' h.2) :=
  rfl

/-- The original circuit of a word has the gates of the word. -/
theorem numGates_toOriginalCircuit : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → (hw : w.IsAllowed) →
      (w.toOriginalCircuit hw).toPartyCircuit.numGates = w.numGates
  | _, _, _, _, PartyCircuit.done _, _ => rfl
  | _, _, _, _, PartyCircuit.gate _ _ _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, _ => rfl
  | _, _, _, _, PartyCircuit.localOps _, _ => rfl
  | _, _, _, _, PartyCircuit.comp c c', h =>
    congrArg₂ (· + ·) (numGates_toOriginalCircuit c h.1) (numGates_toOriginalCircuit c' h.2)

/-- The original circuit of a word has the operator of the word. -/
theorem op_toOriginalCircuit [Fintype P] : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → (hw : w.IsAllowed) →
      (w.toOriginalCircuit hw).op = w.op
  | _, _, _, _, PartyCircuit.done _, _ => rfl
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ g, hw =>
    (OriginalCircuit.op_sourceCircuit g hw.2).trans (Word.op_source g).symm
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY U, hw =>
    (OriginalCircuit.op_localOp p hY U hw).trans (PartyCircuit.op_localOp _ p hY U).symm
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ U, hw =>
    (OriginalCircuit.op_localOps U hw).trans (PartyCircuit.op_localOps _ U).symm
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', hw =>
    (OriginalCircuit.op_comp (toOriginalCircuit c hw.1) (toOriginalCircuit c' hw.2)).trans
      ((congrArg₂ (· * ·) (op_toOriginalCircuit c' hw.2) (op_toOriginalCircuit c hw.1)).trans
        (Word.op_comp c c').symm)

/-- One nonprivate gate for each pair source of the word. -/
theorem nonprivateCount_toOriginalCircuit (w : Word X Y) (hw : w.IsAllowed) :
    (w.toOriginalCircuit hw).nonprivateCount = w.sourceCount := by
  rw [OriginalCircuit.nonprivateCount_eq_numGates, numGates_toOriginalCircuit,
    Word.numGates_eq_sourceCount]

/-- A word without pair sources gives an original circuit without nonprivate gates. -/
theorem nonprivateCount_toOriginalCircuit_of_sourceCount_eq_zero (w : Word X Y)
    (hw : w.IsAllowed) (h0 : w.sourceCount = 0) : (w.toOriginalCircuit hw).nonprivateCount = 0 :=
  (nonprivateCount_toOriginalCircuit w hw).trans h0

/-- Every participant of a nonprivate gate of the circuit is a party used by the word. -/
theorem participants_toOriginalCircuit_subset {S : Set P} : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → (w : Word X Y) → (hw : w.IsAllowed) →
      w.UsesOnly S → (g : (w.toOriginalCircuit hw).nonprivateLocations) →
        (↑((w.toOriginalCircuit hw).participants g) : Set P) ⊆ S
  | _, _, _, _, PartyCircuit.done _, _, _, g => g.elim
  | _, _, _, _, PartyCircuit.gate _ _ _, _, hS, _ => hS
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, g => g.elim
  | _, _, _, _, PartyCircuit.localOps _, _, _, g => g.elim
  | _, _, _, _, PartyCircuit.comp c c', hw, hS, g => by
    rcases g with g | g
    exacts [participants_toOriginalCircuit_subset c hw.1 hS.1 g,
      participants_toOriginalCircuit_subset c' hw.2 hS.2 g]

/-- Each gate of the circuit is a single monomial with coefficient one and no pair effect. -/
theorem isExpansionBounded_toOriginalCircuit : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → (hw : w.IsAllowed) → (r : ℕ) → {s : ℝ} →
      1 ≤ s → (w.toOriginalCircuit hw).IsExpansionBounded r s
  | _, _, _, _, PartyCircuit.done _, _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, _, r, _, hs =>
    ⟨fun t ht ↦ by
      rw [List.mem_singleton.mp ht]
      exact Nat.zero_le r, by
      simpa [OriginalGate.toWeightedGateMorphism, OriginalGate.ofChainGate,
        OriginalGate.ofWeightedGate, WeightedGate.single] using hs⟩
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.comp c c', hw, r, _, hs =>
    ⟨isExpansionBounded_toOriginalCircuit c hw.1 r hs,
      isExpansionBounded_toOriginalCircuit c' hw.2 r hs⟩

/-- Each gate of the circuit has one monomial. -/
theorem isMonomialBounded_toOriginalCircuit : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → (hw : w.IsAllowed) → {K : ℕ} → 1 ≤ K →
      (w.toOriginalCircuit hw).IsMonomialBounded K
  | _, _, _, _, PartyCircuit.done _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _, hK => hK
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.comp c c', hw, _, hK =>
    ⟨isMonomialBounded_toOriginalCircuit c hw.1 hK, isMonomialBounded_toOriginalCircuit c' hw.2 hK⟩

/-- Each gate of the circuit is a single pair source. Source: `04-compression.tex`, lines 21–43 and
143–147. -/
theorem isSourceBounded_toOriginalCircuit : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → (hw : w.IsAllowed) →
      (w.toOriginalCircuit hw).IsSourceBounded 1
  | _, _, _, _, PartyCircuit.done _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, _ => fun t ht ↦ by
    rw [List.mem_singleton.mp ht]
    exact le_rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, _, _, PartyCircuit.comp c c', hw =>
    ⟨isSourceBounded_toOriginalCircuit c hw.1, isSourceBounded_toOriginalCircuit c' hw.2⟩

/-- The pair-source bound with every positive constant, as for the bulk births of Proposition 7.1.
Source: `04-compression.tex`, lines 143–147. -/
theorem isSourceBounded_toOriginalCircuit_of_one_le (w : Word X Y) (hw : w.IsAllowed) {r : ℕ}
    (hr : 1 ≤ r) : (w.toOriginalCircuit hw).IsSourceBounded r :=
  (isSourceBounded_toOriginalCircuit w hw).mono hr

/-- A word without pair sources gives original circuits with arbitrary expansion bounds. -/
theorem isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero (w : Word X Y)
    (hw : w.IsAllowed) (h0 : w.sourceCount = 0) (r : ℕ) (s : ℝ) :
    (w.toOriginalCircuit hw).IsExpansionBounded r s :=
  OriginalCircuit.isExpansionBounded_of_nonprivateCount_eq_zero
    (nonprivateCount_toOriginalCircuit_of_sourceCount_eq_zero w hw h0) r s

/-- A word without pair sources gives original circuits with arbitrary monomial bounds. -/
theorem isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero (w : Word X Y)
    (hw : w.IsAllowed) (h0 : w.sourceCount = 0) (K : ℕ) :
    (w.toOriginalCircuit hw).IsMonomialBounded K :=
  OriginalCircuit.isMonomialBounded_of_nonprivateCount_eq_zero
    (nonprivateCount_toOriginalCircuit_of_sourceCount_eq_zero w hw h0) K

end Word

/-! ### Allowed monomials -/

namespace Monomial

/-- An allowed circuit of pair sources, pair effects and local contractions as an original circuit:
every pair source and every pair effect a two-party nonprivate gate. It applies to a monomial `M :
Monomial D X Y`, giving an original circuit on the parties of `D`. Source: `04-compression.tex`,
lines 32–35. -/
noncomputable def toOriginalCircuit : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (M : PartyCircuit (ChainGate (P := P)) X Y) →
      M.IsAllowed chainEv ChainGate.IsAllowed → OriginalCircuit X Y
  | _, _, _, _, PartyCircuit.done X, _ => OriginalCircuit.done X
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g, h =>
    OriginalCircuit.gate D hY (OriginalGate.ofChainGate g (by rcases g with g | g <;> exact h.2))
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY U, h => OriginalCircuit.localOp p hY U h
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ U, h => OriginalCircuit.localOps U h
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', h =>
    (toOriginalCircuit c h.1).comp (toOriginalCircuit c' h.2)

variable {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- The empty circuit is the empty original circuit. -/
@[simp] theorem toOriginalCircuit_done
    (h : (PartyCircuit.done X : PartyCircuit (ChainGate (P := P)) X X).IsAllowed chainEv
      ChainGate.IsAllowed) :
    toOriginalCircuit (PartyCircuit.done X) h = OriginalCircuit.done X :=
  rfl

/-- The original circuit of a composition is the composition. -/
@[simp] theorem toOriginalCircuit_comp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (M : PartyCircuit (ChainGate (P := P)) X Y) (M' : PartyCircuit (ChainGate (P := P)) Y Z)
    (h : (PartyCircuit.comp M M').IsAllowed chainEv ChainGate.IsAllowed) :
    toOriginalCircuit (PartyCircuit.comp M M') h =
      (toOriginalCircuit M h.1).comp (toOriginalCircuit M' h.2) :=
  rfl

/-- The original circuit has the gates of the circuit. -/
theorem numGates_toOriginalCircuit : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (M : PartyCircuit (ChainGate (P := P)) X Y) →
      (hM : M.IsAllowed chainEv ChainGate.IsAllowed) →
        (toOriginalCircuit M hM).toPartyCircuit.numGates = M.numGates
  | _, _, _, _, PartyCircuit.done _, _ => rfl
  | _, _, _, _, PartyCircuit.gate _ _ _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, _ => rfl
  | _, _, _, _, PartyCircuit.localOps _, _ => rfl
  | _, _, _, _, PartyCircuit.comp c c', h =>
    congrArg₂ (· + ·) (numGates_toOriginalCircuit c h.1) (numGates_toOriginalCircuit c' h.2)

/-- The original circuit of a monomial has the operator of the monomial. -/
theorem op_toOriginalCircuit [Fintype P] : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (M : PartyCircuit (ChainGate (P := P)) X Y) →
      (hM : M.IsAllowed chainEv ChainGate.IsAllowed) → (toOriginalCircuit M hM).op = M.op chainEv
  | _, _, _, _, PartyCircuit.done _, _ => rfl
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D _ g, hM => by
    rcases g with g | g
    · exact (OriginalCircuit.op_sourceCircuit g hM.2).trans (ChainGate.op_gate_inl g).symm
    · exact (OriginalCircuit.op_effectCircuit g hM.2).trans (ChainGate.op_gate_inr g).symm
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY U, hM =>
    (OriginalCircuit.op_localOp p hY U hM).trans (PartyCircuit.op_localOp _ p hY U).symm
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ U, hM =>
    (OriginalCircuit.op_localOps U hM).trans (PartyCircuit.op_localOps _ U).symm
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', hM =>
    (OriginalCircuit.op_comp (toOriginalCircuit c hM.1) (toOriginalCircuit c' hM.2)).trans
      ((congrArg₂ (· * ·) (op_toOriginalCircuit c' hM.2) (op_toOriginalCircuit c hM.1)).trans
        (PartyCircuit.op_comp (P := P) (G := ChainGate) chainEv c c').symm)

/-- One nonprivate gate for each gate of the circuit. -/
theorem nonprivateCount_toOriginalCircuit_eq_numGates
    (M : PartyCircuit (ChainGate (P := P)) X Y) (hM : M.IsAllowed chainEv ChainGate.IsAllowed) :
    (toOriginalCircuit M hM).nonprivateCount = M.numGates := by
  rw [OriginalCircuit.nonprivateCount_eq_numGates, numGates_toOriginalCircuit]

/-- One nonprivate gate for each pair source and each pair effect of the monomial. -/
theorem nonprivateCount_toOriginalCircuit {D : Finset P} {A B : ↥D → Type}
    [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] (M : Monomial D A B)
    (hM : M.IsAllowed chainEv ChainGate.IsAllowed) :
    (toOriginalCircuit M hM).nonprivateCount = M.sourceCount + M.effectCount := by
  rw [nonprivateCount_toOriginalCircuit_eq_numGates, ← M.effectCount_add_sourceCount,
    Nat.add_comm]

/-- Every participant of a nonprivate gate of the circuit lies in `S` when every cell does. -/
theorem participants_toOriginalCircuit_subset {S : Set P} : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
      (M : PartyCircuit (ChainGate (P := P)) X Y) →
      (hM : M.IsAllowed chainEv ChainGate.IsAllowed) →
      M.ForallGate (fun D _ _ _ ↦ (↑D : Set P) ⊆ S) →
      (g : (toOriginalCircuit M hM).nonprivateLocations) →
        (↑((toOriginalCircuit M hM).participants g) : Set P) ⊆ S
  | _, _, _, _, PartyCircuit.done _, _, _, g => g.elim
  | _, _, _, _, PartyCircuit.gate _ _ _, _, hS, _ => hS
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, g => g.elim
  | _, _, _, _, PartyCircuit.localOps _, _, _, g => g.elim
  | _, _, _, _, PartyCircuit.comp c c', hM, hS, g => by
    rcases g with g | g
    exacts [participants_toOriginalCircuit_subset c hM.1 hS.1 g,
      participants_toOriginalCircuit_subset c' hM.2 hS.2 g]

/-- Each gate of the circuit is a single monomial with coefficient one and at most one pair effect.
-/
theorem isExpansionBounded_toOriginalCircuit : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (M : PartyCircuit (ChainGate (P := P)) X Y) →
      (hM : M.IsAllowed chainEv ChainGate.IsAllowed) → {r : ℕ} → 1 ≤ r → {s : ℝ} → 1 ≤ s →
        (toOriginalCircuit M hM).IsExpansionBounded r s
  | _, _, _, _, PartyCircuit.done _, _, _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ g, _, _, hr, _, hs =>
    ⟨fun t ht ↦ by
      rw [List.mem_singleton.mp ht]
      exact g.effectCount_toMonomial_le_one.trans hr, by
      simpa [OriginalGate.toWeightedGateMorphism, OriginalGate.ofChainGate,
        OriginalGate.ofWeightedGate, WeightedGate.single] using hs⟩
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _, _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.comp c c', hM, _, hr, _, hs =>
    ⟨isExpansionBounded_toOriginalCircuit c hM.1 hr hs,
      isExpansionBounded_toOriginalCircuit c' hM.2 hr hs⟩

/-- Each gate of the circuit has one monomial. -/
theorem isMonomialBounded_toOriginalCircuit : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (M : PartyCircuit (ChainGate (P := P)) X Y) →
      (hM : M.IsAllowed chainEv ChainGate.IsAllowed) → {K : ℕ} → 1 ≤ K →
        (toOriginalCircuit M hM).IsMonomialBounded K
  | _, _, _, _, PartyCircuit.done _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _, hK => hK
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.comp c c', hM, _, hK =>
    ⟨isMonomialBounded_toOriginalCircuit c hM.1 hK, isMonomialBounded_toOriginalCircuit c' hM.2 hK⟩

/-- Each gate of the circuit is a single pair source or a single pair effect, so it has at most one
pair source. Source: `04-compression.tex`, lines 21–43 and 143–147. -/
theorem isSourceBounded_toOriginalCircuit : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (M : PartyCircuit (ChainGate (P := P)) X Y) →
      (hM : M.IsAllowed chainEv ChainGate.IsAllowed) →
        (toOriginalCircuit M hM).IsSourceBounded 1
  | _, _, _, _, PartyCircuit.done _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ g, _ => fun t ht ↦ by
    rw [List.mem_singleton.mp ht]
    exact g.sourceCount_toMonomial_le_one
  | _, _, _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, _, _, PartyCircuit.comp c c', hM =>
    ⟨isSourceBounded_toOriginalCircuit c hM.1, isSourceBounded_toOriginalCircuit c' hM.2⟩

/-- The pair-source bound with every positive constant, as for the bulk deaths of Proposition 7.1.
Source: `04-compression.tex`, lines 143–147. -/
theorem isSourceBounded_toOriginalCircuit_of_one_le (M : PartyCircuit (ChainGate (P := P)) X Y)
    (hM : M.IsAllowed chainEv ChainGate.IsAllowed) {r : ℕ} (hr : 1 ≤ r) :
    (toOriginalCircuit M hM).IsSourceBounded r :=
  (isSourceBounded_toOriginalCircuit M hM).mono hr

end Monomial

end QuantumCircuit.Party
