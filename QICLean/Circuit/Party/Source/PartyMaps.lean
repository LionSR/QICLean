/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.Common

/-!
# Words as prepared sources followed by local contractions

An allowed word is a preparation of normalized sources, at most one on each unordered pair of
parties, followed by one contraction at each party (`Word.exists_grouped_source_preparation`,
`Word.exists_prepared_localOps`). The sources can be completed to one on every pair
(`Word.exists_complete_source_preparation`, `Word.exists_complete_prepared_localOps`), and for a
finite family of words they can be prepared in common slot bases
(`Word.exists_common_source_preparation`, `Word.exists_common_prepared_localOps`). The tensor
product of the contractions at the parties is `Matrix.piKronecker` of the party matrices, the
configurations of a system being grouped by party.

## Main results

* `QuantumCircuit.Party.Word.exists_grouped_source_preparation`,
  `QuantumCircuit.Party.Word.exists_prepared_localOps` — grouped sources.
* `QuantumCircuit.Party.Word.exists_complete_source_preparation`,
  `QuantumCircuit.Party.Word.exists_complete_prepared_localOps` — a source on every pair.
* `QuantumCircuit.Party.Word.exists_common_source_preparation`,
  `QuantumCircuit.Party.Word.exists_common_prepared_localOps` — common slot bases for a finite
  family of words.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`,
  lines 68–70 and 125–127; equation `eq:compression-source-gate` and common private slot
  spaces, lines 233–267.
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)]

namespace Word

/-- An allowed word is a preparation with at most one normalized source on each unordered pair
of parties, followed by an allowed word with no sources; the pairs of the preparation are the
pairs of the word. Source: Lemma 5.1, `04-compression.tex`, lines 68–70 and 125–127. -/
theorem exists_grouped_source_preparation [∀ p, Finite (Y p)] (w : Word X Y) (hw : w.IsAllowed) :
    ∃ S : SourceInventory P, S.IsNormalized ∧ (S.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ S.map PairSource.partyPair ↔ k ∈ w.sources.map PairSource.partyPair) ∧
      ∃ v : Word (S.system X) Y,
        v.IsAllowed ∧ v.sources = [] ∧ w.op = v.op * (S.prepare X).op := by
  classical
  let := fun p ↦ Fintype.ofFinite (Y p)
  obtain ⟨S, hS, hN, hK, hE⟩ :=
    SourceInventory.exists_grouped w.sources (w.isNormalized_sources hw)
  obtain ⟨v, hv, hs, he⟩ := hE X
  refine ⟨S, hS, hN, hK, v.comp w.localPart, ⟨hv, w.isAllowed_localPart hw⟩, ?_, ?_⟩
  · rw [Word.sources_comp, Word.sources_localPart, hs, List.nil_append]
  · refine (w.op_localPart_mul_prepare).symm.trans ?_
    rw [Word.op_comp, Matrix.mul_assoc, he]

/-- An allowed word is a preparation of grouped normalized sources followed by one contraction
at each party. Source: `eq:compression-source-gate`,
`04-compression.tex`, lines 233–251. -/
theorem exists_prepared_localOps [∀ p, Fintype (Y p)] (w : Word X Y) (hw : w.IsAllowed) :
    ∃ S : SourceInventory P, S.IsNormalized ∧ (S.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ S.map PairSource.partyPair ↔ k ∈ w.sources.map PairSource.partyPair) ∧
      ∃ B : ∀ p, Matrix (Y p) (S.system X p) ℂ,
        (∀ p, ‖B p‖ ≤ 1) ∧ w.op = piKronecker B * (S.prepare X).op := by
  classical
  obtain ⟨S, hS, hN, hK, v, hv, hvs, he⟩ := w.exists_grouped_source_preparation hw
  obtain ⟨B, hB, hF⟩ := Word.exists_piKronecker_of_sources_eq_nil hv hvs
  exact ⟨S, hS, hN, hK, B, hB, he.trans (by rw [← hF])⟩

/-- An allowed word is a preparation of exactly one normalized source on every unordered pair
of distinct parties, with one-element bases on the pairs absent from the word, followed by an
allowed word with no sources. Source:
`eq:compression-source-gate`, `04-compression.tex`, lines 233–251. -/
theorem exists_complete_source_preparation [∀ p, Finite (Y p)] (w : Word X Y) (hw : w.IsAllowed) :
    ∃ S : SourceInventory P, S.IsNormalized ∧ (S.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ S.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      (∀ s ∈ S, s.partyPair ∉ w.sources.map PairSource.partyPair →
        Fintype.card s.leftBasis = 1 ∧ Fintype.card s.rightBasis = 1) ∧
      ∃ v : Word (S.system X) Y,
        v.IsAllowed ∧ v.sources = [] ∧ w.op = v.op * (S.prepare X).op := by
  classical
  let := fun p ↦ Fintype.ofFinite (Y p)
  obtain ⟨S, hS, hN, hK, v, hv, hvs, he⟩ := w.exists_grouped_source_preparation hw
  obtain ⟨U, hU, hT, hTN, hTK, hE⟩ := SourceInventory.exists_complete_extension S hS hN
  obtain ⟨d, hd, hds, hde⟩ := hE X
  refine ⟨U ++ S, hT, hTN, hTK, ?_, d.comp v, ⟨hd, hv⟩, ?_, ?_⟩
  · intro s hs hks
    rcases List.mem_append.mp hs with hs | hs
    · exact ⟨(hU s hs).1, (hU s hs).2.1⟩
    · exact (hks ((hK s.partyPair).mp (List.mem_map_of_mem hs))).elim
  · rw [Word.sources_comp, hds, hvs, List.nil_append]
  · rw [he, Word.op_comp, Matrix.mul_assoc]
    exact congrArg _ hde.symm

/-- The complete preparation followed by one contraction at each party. Source:
`eq:compression-source-gate`, `04-compression.tex`, lines 233–251. -/
theorem exists_complete_prepared_localOps [∀ p, Fintype (Y p)] (w : Word X Y) (hw : w.IsAllowed) :
    ∃ S : SourceInventory P, S.IsNormalized ∧ (S.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ S.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      (∀ s ∈ S, s.partyPair ∉ w.sources.map PairSource.partyPair →
        Fintype.card s.leftBasis = 1 ∧ Fintype.card s.rightBasis = 1) ∧
      ∃ B : ∀ p, Matrix (Y p) (S.system X p) ℂ,
        (∀ p, ‖B p‖ ≤ 1) ∧ w.op = piKronecker B * (S.prepare X).op := by
  classical
  obtain ⟨S, hS, hN, hK, hD, v, hv, hvs, he⟩ := w.exists_complete_source_preparation hw
  obtain ⟨B, hB, hF⟩ := Word.exists_piKronecker_of_sources_eq_nil hv hvs
  exact ⟨S, hS, hN, hK, hD, B, hB, he.trans (by rw [← hF])⟩

/-- Prepare the sources of every word of a finite family in fixed slot bases, followed by allowed
words with no sources; the common bases are built from the words. Source: `04-compression.tex`,
lines 233–267. -/
theorem exists_common_source_preparation [∀ p, Finite (Y p)] {ι : Type} [Finite ι]
    (w : ι → Word X Y)
    (hw : ∀ ξ, (w ξ).IsAllowed) :
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ (B : SourceInventory.SlotBases R.length)
        (η : ι → ∀ i, EuclideanSpace ℂ (B.left i × B.right i)),
        (∀ ξ i, ‖η ξ i‖ = 1) ∧
        ∃ v : ι → Word (SourceInventory.slotSystem R B X) Y,
          (∀ ξ, (v ξ).IsAllowed) ∧ (∀ ξ, (v ξ).sources = []) ∧
          ∀ ξ, (w ξ).op = (v ξ).op * (SourceInventory.prepareSlots R B (η ξ) X).op := by
  classical
  let := fun p ↦ Fintype.ofFinite (Y p)
  let := Fintype.ofFinite ι
  obtain ⟨R, _, hR, hRK, _⟩ := SourceInventory.exists_complete ([] : SourceInventory P)
    (by simp [SourceInventory.IsNormalized]) (by simp)
  choose S hS hN hK hD v hv hvs he using fun ξ ↦
    (w ξ).exists_complete_source_preparation (hw ξ)
  obtain ⟨B, η, hη, hE⟩ := SourceInventory.exists_common_expansions R S hR hS hN
    (fun ξ k ↦ (hRK k).trans (hK ξ k).symm)
  choose d hd hds hde using fun ξ ↦
    SourceInventory.exists_prepareSlots_recovery R (S ξ) B (η ξ) (hE ξ) X
  refine ⟨R, hR, hRK, B, η, hη, fun ξ ↦ (d ξ).comp (v ξ),
    fun ξ ↦ ⟨hd ξ, hv ξ⟩, ?_, ?_⟩
  · intro ξ
    rw [Word.sources_comp, hds, hvs, List.nil_append]
  · intro ξ
    rw [he ξ, Word.op_comp, Matrix.mul_assoc]
    exact congrArg _ (hde ξ).symm

/-- Every word of a finite family is a preparation in common slot bases, with normalized vectors on
every pair of distinct parties, followed by one contraction at each party. Source:
`eq:compression-source-gate` and common private slot spaces, `04-compression.tex`, lines 233–267. -/
theorem exists_common_prepared_localOps [∀ p, Fintype (Y p)] {ι : Type} [Finite ι]
    (w : ι → Word X Y)
    (hw : ∀ ξ, (w ξ).IsAllowed) :
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ (B : SourceInventory.SlotBases R.length)
        (η : ι → ∀ i, EuclideanSpace ℂ (B.left i × B.right i)),
        (∀ ξ i, ‖η ξ i‖ = 1) ∧
        ∃ A : ι → ∀ p, Matrix (Y p) (SourceInventory.slotSystem R B X p) ℂ,
          (∀ ξ p, ‖A ξ p‖ ≤ 1) ∧
          ∀ ξ, (w ξ).op = piKronecker (A ξ) * (SourceInventory.prepareSlots R B (η ξ) X).op := by
  classical
  obtain ⟨R, hR, hRK, B, η, hη, v, hv, hvs, he⟩ := exists_common_source_preparation w hw
  choose A hA hF using fun ξ ↦ Word.exists_piKronecker_of_sources_eq_nil (hv ξ) (hvs ξ)
  exact ⟨R, hR, hRK, B, η, hη, A, hA, fun ξ ↦ (he ξ).trans (by rw [← hF ξ])⟩

end Word

end QuantumCircuit.Party
