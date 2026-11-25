/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Sym.Card
import QICLean.Circuit.Party.Syntax.Gates

/-!
# Source slots indexed by unordered pairs of parties

A source inventory with distinct pair labels that covers every pair of distinct parties indexes
the unordered pairs of distinct parties exactly once. On a finite type of parties its length is
therefore the number of ways of choosing two parties. The identification keeps the pair of each
source; the bases and the vector of the source do not enter.

## Main definitions

* `QuantumCircuit.Party.SourceInventory.pairIndexEquiv` — slots as unordered pairs of distinct
  parties.

## Main results

* `QuantumCircuit.Party.SourceInventory.length_eq_choose`,
  `QuantumCircuit.Party.SourceInventory.length_le_card_sq`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`, pair slots
  at lines 233–245 and sample positions at lines 565–585.
-/

namespace QuantumCircuit.Party.SourceInventory

variable {P : Type}

/-- The slots of a complete source inventory are the unordered pairs of distinct parties.
Source: Theorem 5.2, `04-compression.tex`, lines 233–245 and 565–585. -/
def pairIndexEquiv [DecidableEq P] (R : SourceInventory P)
    (hN : (R.map PairSource.partyPair).Nodup)
    (hK : ∀ k, k ∈ R.map PairSource.partyPair ↔ ¬k.IsDiag) :
    Fin R.length ≃ {k : Sym2 P // ¬k.IsDiag} :=
  (finCongr (by simp : R.length = (R.map PairSource.partyPair).length)).trans
    ((List.Nodup.getEquiv _ hN).trans (Equiv.subtypeEquivRight hK))

/-- The identification sends each slot to the pair of its source. Source: Theorem 5.2,
`04-compression.tex`, lines 233–245. -/
@[simp] theorem pairIndexEquiv_apply [DecidableEq P] (R : SourceInventory P)
    (hN : (R.map PairSource.partyPair).Nodup)
    (hK : ∀ k, k ∈ R.map PairSource.partyPair ↔ ¬k.IsDiag) (i : Fin R.length) :
    (pairIndexEquiv R hN hK i).val = (R.get i).partyPair := by
  simp [pairIndexEquiv, List.Nodup.getEquiv]

/-- A complete source inventory has exactly one slot for each choice of two distinct parties.
Source: Theorem 5.2, `04-compression.tex`, lines 233–245 and 581–585. -/
theorem length_eq_choose [Fintype P] (R : SourceInventory P)
    (hN : (R.map PairSource.partyPair).Nodup)
    (hK : ∀ k, k ∈ R.map PairSource.partyPair ↔ ¬k.IsDiag) :
    R.length = (Fintype.card P).choose 2 := by
  classical
  simpa only [Fintype.card_fin] using
    (Fintype.card_congr (pairIndexEquiv R hN hK)).trans (Sym2.card_subtype_not_diag (α := P))

/-- The number of pair-source slots is at most the square of the number of parties. Source:
Theorem 5.2, `04-compression.tex`, lines 581–585. -/
theorem length_le_card_sq [Fintype P] (R : SourceInventory P)
    (hN : (R.map PairSource.partyPair).Nodup)
    (hK : ∀ k, k ∈ R.map PairSource.partyPair ↔ ¬k.IsDiag) :
    R.length ≤ (Fintype.card P) ^ 2 := by
  rw [length_eq_choose R hN hK]
  exact Nat.choose_le_pow _ _

end QuantumCircuit.Party.SourceInventory
