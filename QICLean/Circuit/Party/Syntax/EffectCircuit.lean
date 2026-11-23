/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Gates

/-!
# Weighted gates, effect circuits and original circuits

A gate of the party calculus on a cell `D` is given by a gate expansion: a weighted list of
monomials on the parties of `D` (`WeightedGate`), whose matrix is the weighted sum of the
operators of the monomials. An *effect circuit* is a party circuit of such gates; an *original
circuit* is an effect circuit whose local operations and gates are contractions, whose
monomials are allowed, and none of whose gates is private, so that its theorems need no side
hypothesis.

## Main definitions

* `QuantumCircuit.Party.WeightedGate`, `QuantumCircuit.Party.WeightedGate.ev`,
  `QuantumCircuit.Party.WeightedGate.IsAllowed`.
* `QuantumCircuit.Party.EffectCircuit`, `QuantumCircuit.Party.OriginalCircuit`.

## Main results

* `QuantumCircuit.Party.OriginalCircuit.norm_op_le_one` — an original circuit is a contraction.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 21–36 (gates),
  53–57 (gate expansions), 199–216 (nonprivate gates).
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

/-- An original circuit: an effect circuit whose local operations and gates are contractions,
whose monomials are allowed, and no gate of which is private, that is, acts on exactly one
party. Its theorems need no side hypothesis. Source: `04-compression.tex`, lines 21–36
and 199–216. -/
structure OriginalCircuit [Fintype P] (X Y : P → Type) [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] : Type 1 where
  /-- The underlying effect circuit. -/
  toEffectCircuit : EffectCircuit X Y
  /-- Contractive local operations and gates, and allowed monomials. -/
  allowed : toEffectCircuit.IsAllowed WeightedGate.ev WeightedGate.IsAllowed
  /-- No gate acts on exactly one party. -/
  nonprivate : toEffectCircuit.ForallGate fun D _ _ _ ↦ D.card ≠ 1

namespace OriginalCircuit

variable [Fintype P] {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- The operator of an original circuit. -/
noncomputable def op (w : OriginalCircuit X Y) : Matrix (Config Y) (Config X) ℂ :=
  w.toEffectCircuit.op WeightedGate.ev

/-- **An original circuit is a contraction.** Source: `04-compression.tex`, line 28 and
lines 215–216. -/
theorem norm_op_le_one [∀ p, Fintype (Y p)] (w : OriginalCircuit X Y) : ‖w.op‖ ≤ 1 :=
  PartyCircuit.norm_op_le_one _ w.allowed

end OriginalCircuit

end QuantumCircuit.Party
