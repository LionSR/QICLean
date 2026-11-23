/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Original.Basic
import QICLean.Circuit.Party.Syntax.Frame

/-!
# Original circuits beside spectator factors

`OriginalCircuit.frame W w` runs the original circuit `w` beside an untouched spectator factor
`W p` in front of the basis of every party `p`: every gate framed
(`OriginalGate.frame`), every private contraction `A` replaced by `1 ⊗ A`. Its effect circuit is
the framed effect circuit, its operator `1 ⊗ op`, and its gates, cells, counts and expansion
bounds are those of `w`. Framing a monomial keeps its pair sources and pair effects
(`Monomial.sources_frame`, `Monomial.effects_frame`).

## Main definitions

* `QuantumCircuit.Party.OriginalGate.frame`, `QuantumCircuit.Party.OriginalCircuit.frame`.
* `QuantumCircuit.Party.PartyCircuit.frameLocationsEquiv`.

## Main results

* `QuantumCircuit.Party.OriginalCircuit.op_frame`, `nonprivateCount_frame`, `participation_frame`,
  `isExpansionBounded_frame`, `isMonomialBounded_frame`, `isSourceBounded_frame`.
* `QuantumCircuit.Party.Monomial.sources_frame`, `effects_frame`, `effectCount_frame`,
  `sourceCount_frame`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 21–43; Proposition
  7.1, `06-geometry.tex`, lines 658–667 (untouched factors are spectators).
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Original gates beside spectator factors -/

namespace OriginalGate

variable {D : Finset P} {X Y : P → Type} (W : P → Type) [∀ p, Fintype (W p)]
  [∀ p, DecidableEq (W p)] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)]

/-- An original gate beside the spectator factors `W`: the framed gate expansion. Its conditions are
proved with the finiteness instances of `X` and `Y` at hand (a framed gate of a system without them
may fail them, so this is not a `GateFrame` instance of weighted gates). -/
def frame (g : OriginalGate D X Y) : OriginalGate D (fun p ↦ W p × X p) (fun p ↦ W p × Y p) :=
  ofWeightedGate (GateFrame.frame W g.toWeightedGate) g.card_ne_one
    (WeightedGate.isAllowed_frame g.monomials_allowed)
    ((congrArg norm (WeightedGate.isCompatible_frame g.toWeightedGate ())).trans_le
      ((l2_opNorm_reindex_le _ _ _).trans
        ((l2_opNorm_one_kronecker_le _).trans g.norm_ev_le_one)))

/-- The gate expansion of a framed original gate is the framed gate expansion. -/
@[simp] theorem toWeightedGate_frame (g : OriginalGate D X Y) :
    (g.frame W).toWeightedGate = GateFrame.frame W g.toWeightedGate :=
  rfl

end OriginalGate

/-- Original gates run beside spectator factors (the conditions of the framed gate are proved with
the instances of the systems of the gate, which `GateFrame.frame` receives). -/
instance : GateFrame (OriginalGate (P := P)) where
  frame _ _ _ W _ _ _ _ _ _ g := g.frame W
  outcomeEquiv _ _ _ _ _ _ _ _ _ _ _ := Equiv.refl Unit

/-- The interpretation of original gates is compatible with framing. -/
theorem OriginalGate.isCompatible_frame :
    GateFrame.IsCompatible (OriginalGate (P := P)) OriginalGate.ev :=
  fun _ _ _ _ _ _ _ _ _ _ g o ↦ WeightedGate.isCompatible_frame g.toWeightedGate o

/-! ### Bounds of framed effect circuits -/

namespace EffectCircuit

variable (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

/-- Framing keeps the expansion bounds. -/
theorem isExpansionBounded_frame {r : ℕ} {S : ℝ} : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → {c : EffectCircuit X Y} → IsExpansionBounded r S c →
      IsExpansionBounded r S (c.frame W)
  | _, _, _, _, PartyCircuit.done _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ g, h => by
    refine ⟨fun t ht ↦ ?_, ?_⟩
    · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
      exact (Monomial.effectCount_frame _ t'.2).trans_le (h.1 t' ht')
    · change ((g.terms.map _).map _).sum ≤ S
      simpa only [List.map_map, Function.comp_def] using h.2
  | _, _, _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, _, _, PartyCircuit.comp _ _, h =>
    ⟨isExpansionBounded_frame h.1, isExpansionBounded_frame h.2⟩

/-- Framing keeps the monomial bounds. -/
theorem isMonomialBounded_frame {K : ℕ} : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → {c : EffectCircuit X Y} →
    IsMonomialBounded K c → IsMonomialBounded K (c.frame W)
  | _, _, _, _, PartyCircuit.done _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, h => (List.length_map _).trans_le h
  | _, _, _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, _, _, PartyCircuit.comp _ _, h =>
    ⟨isMonomialBounded_frame h.1, isMonomialBounded_frame h.2⟩

/-- Framing keeps the pair-source bounds. -/
theorem isSourceBounded_frame {r : ℕ} : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → {c : EffectCircuit X Y} →
    IsSourceBounded r c → IsSourceBounded r (c.frame W)
  | _, _, _, _, PartyCircuit.done _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, h => fun t ht ↦ by
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact (Monomial.sourceCount_frame _ t'.2).trans_le (h t' ht')
  | _, _, _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, _, _, PartyCircuit.comp _ _, h =>
    ⟨isSourceBounded_frame h.1, isSourceBounded_frame h.2⟩

end EffectCircuit

namespace OriginalCircuit

section Frame

variable {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

/-- An original circuit beside the spectator factors `W`, the factor `W p` in front of the basis of
every party `p`. Source: `06-geometry.tex`, lines 658–667 (untouched factors are spectators). -/
def frame (w : OriginalCircuit X Y) : OriginalCircuit (fun p ↦ W p × X p) (fun p ↦ W p × Y p) :=
  ⟨w.toPartyCircuit.frame W, w.localAllowed.frame W⟩

/-- The effect circuit of a framed circuit is the framed effect circuit. -/
theorem toEffectCircuit_frame (w : OriginalCircuit X Y) :
    (w.frame W).toEffectCircuit = w.toEffectCircuit.frame W :=
  PartyCircuit.mapGates_frame W _ (fun _ _ _ _ _ _ _ _ ↦ rfl) _

/-- **A framed circuit acts as `1 ⊗ op`**, read along the pairing of configurations. -/
theorem op_frame [Fintype P] (w : OriginalCircuit X Y) :
    (w.frame W).op =
      reindex (Equiv.arrowProdEquivProdArrow P W Y).symm
        (Equiv.arrowProdEquivProdArrow P W X).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ w.op) :=
  PartyCircuit.op_frame W _ OriginalGate.isCompatible_frame _

/-- Framing keeps the number of nonprivate gates. -/
@[simp] theorem nonprivateCount_frame (w : OriginalCircuit X Y) :
    (w.frame W).nonprivateCount = w.nonprivateCount :=
  PartyCircuit.gateCount_frame W _

/-- Framing keeps the participations. -/
@[simp] theorem participation_frame (w : OriginalCircuit X Y) (p : P) :
    (w.frame W).participation p = w.participation p :=
  PartyCircuit.participation_frame W p _

/-- Framing keeps the gate occurrences. -/
def frameLocationsEquiv (w : OriginalCircuit X Y) :
    w.nonprivateLocations ≃ (w.frame W).nonprivateLocations :=
  PartyCircuit.frameLocationsEquiv W _

/-- Framing keeps the cell of every occurrence. -/
theorem participants_frameLocationsEquiv (w : OriginalCircuit X Y) (g : w.nonprivateLocations) :
    (w.frame W).participants (w.frameLocationsEquiv W g) = w.participants g :=
  PartyCircuit.participants_frameLocationsEquiv W _ g

/-- A condition on the participants of every occurrence passes to the framed circuit. -/
theorem forall_participants_frame {Q : Finset P → Prop} (w : OriginalCircuit X Y)
    (h : ∀ g, Q (w.participants g)) : ∀ g, Q ((w.frame W).participants g) := fun g ↦ by
  obtain ⟨g, rfl⟩ := (w.frameLocationsEquiv W).surjective g
  rw [participants_frameLocationsEquiv]
  exact h g

/-- Framing keeps the expansion bounds. -/
theorem isExpansionBounded_frame (w : OriginalCircuit X Y) {r : ℕ} {S : ℝ}
    (h : w.IsExpansionBounded r S) : (w.frame W).IsExpansionBounded r S := by
  rw [IsExpansionBounded, toEffectCircuit_frame]
  exact EffectCircuit.isExpansionBounded_frame W h

/-- Framing keeps the monomial bounds. -/
theorem isMonomialBounded_frame (w : OriginalCircuit X Y) {K : ℕ}
    (h : w.IsMonomialBounded K) : (w.frame W).IsMonomialBounded K := by
  rw [IsMonomialBounded, toEffectCircuit_frame]
  exact EffectCircuit.isMonomialBounded_frame W h

/-- Framing keeps the pair-source bounds. -/
theorem isSourceBounded_frame (w : OriginalCircuit X Y) {r : ℕ}
    (h : w.IsSourceBounded r) : (w.frame W).IsSourceBounded r := by
  rw [IsSourceBounded, toEffectCircuit_frame]
  exact EffectCircuit.isSourceBounded_frame W h

end Frame

end OriginalCircuit

end QuantumCircuit.Party
