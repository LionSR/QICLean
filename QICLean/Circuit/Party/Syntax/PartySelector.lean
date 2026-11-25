/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Option.Basic

/-!
# Selecting a single party

The selector of a party is the set of parties, given by its indicator, that contains exactly
that party. The selector of the exterior party of a type of optional parties is the test for the
exterior party.

## Main definitions

* `QuantumCircuit.Party.partySelector`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 233–251, 351–381 and 409–417.
-/

namespace QuantumCircuit.Party

variable {P : Type}

/-- The indicator of one party. Source: `04-compression.tex`, lines 233–251 and 351–381. -/
def partySelector [DecidableEq P] (p : P) : P → Bool :=
  fun q ↦ decide (q = p)

/-- The selector of a party contains exactly that party. -/
@[simp] theorem partySelector_eq_true_iff [DecidableEq P] {p q : P} :
    partySelector p q = true ↔ q = p :=
  decide_eq_true_iff

/-- The selector of the exterior party tests for the exterior party. Source: Theorem 5.2,
`04-compression.tex`, lines 409–417. -/
theorem partySelector_none [DecidableEq P] : partySelector (none : Option P) = Option.isNone := by
  funext q
  cases q <;> simp [partySelector]

end QuantumCircuit.Party
