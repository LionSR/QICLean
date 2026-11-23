/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.PartyMaps
import QICLean.Circuit.Party.Monomial.WeightedGate

/-!
# Pair-effect elimination with grouped sources

The pair-effect elimination of a gate expansion (`WeightedGate.partyPairEffectElimination`)
together with the grouping of the sources of every resulting word by party pair
(`Word.exists_grouped_source_preparation`): every resulting word is a preparation with at most
one normalized source on each unordered pair of parties, followed by an allowed word with no
sources.

It is kept apart from `Source/PartyMaps` so that the grouping of sources does not depend on the
monomials.

## Main results

* `QuantumCircuit.Party.WeightedGate.partyPairEffectElimination_with_grouped_sources`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 53–127.
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Pair-effect elimination with grouped sources -/

namespace WeightedGate

open GateExpansion

variable {D : Finset P} {A B : ↥D → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Fintype (B s)] [∀ s, DecidableEq (B s)]

/-- **Pair-effect elimination with grouped sources**: the conclusions of
`partyPairEffectElimination`, and every resulting word is a preparation with at most one normalized
source on each unordered pair of parties, the pairs of the word, followed by an allowed word with no
sources. Source: Lemma 5.1 `lem:effects`, `04-compression.tex`, lines 53–127. -/
theorem partyPairEffectElimination_with_grouped_sources {m r : ℕ} (hm : m ≠ 0)
    (L : List (ℂ × Monomial D A B))
    (hL : ∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed ∧ t.2.effectCount ≤ r) :
    (‖inventoryVector m (toGate L)‖ = 1 ∧
    (prepGate m L).op = reindex (gateEquiv m L).symm (Equiv.refl _)
      (prepMatrix (Equiv.prodComm (Config B) _) (inventoryVector m (toGate L))) ∧
    (prepGate m L).IsAllowed ∧
    ‖replaceGate m (toGate L) -
        prepMatrix (Equiv.prodComm (Config B) _) (inventoryVector m (toGate L)) *
          gate (toGate L)‖ ≤
      r / Real.sqrt m * (L.map fun t ↦ ‖t.1‖).sum ∧
    replaceGate m (toGate L) =
      ((wordList m L).map fun q ↦ q.1 • reindex (gateEquiv m L) (Equiv.refl _) q.2.op).sum ∧
    (∀ q ∈ wordList m L, q.2.IsAllowed) ∧
    (∀ q ∈ termList m (toGate L),
      IsSourceOnly (reindex (gateEquiv m L).symm (Equiv.refl _) q.2)) ∧
    (wordList m L).length ≤ L.length * m ^ r ∧
    ((wordList m L).map fun q ↦ ‖q.1‖).sum = (L.map fun t ↦ ‖t.1‖).sum ∧
    ∀ s : ↥D, (∀ t ∈ L, ∀ e ∈ t.2.effectParties, s ≠ e.1 ∧ s ≠ e.2) → gateOut m L s = B s) ∧
    ∀ q ∈ wordList m L, ∃ S : SourceInventory ↥D, S.IsNormalized ∧
      (S.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ S.map PairSource.partyPair ↔ k ∈ q.2.sources.map PairSource.partyPair) ∧
      ∃ v : Word (S.system A) (gateOut m L),
        v.IsAllowed ∧ v.sources = [] ∧ q.2.op = v.op * (S.prepare A).op := by
  have h := partyPairEffectElimination hm L hL
  exact ⟨h, fun q hq ↦ Word.exists_grouped_source_preparation q.2 (h.2.2.2.2.2.1 q hq)⟩

end WeightedGate

end QuantumCircuit.Party
