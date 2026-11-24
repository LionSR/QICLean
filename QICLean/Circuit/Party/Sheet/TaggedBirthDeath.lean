/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Sheet.BoundedChanges

/-!
# Birth and death beside tag registers

If the handed-over region avoids the hole footprints, one can leave every tag
at its original party. In the tag and site coordinates the circuit is the
identity on the tags tensored with the canonical birth operator. The tags
can be entangled with the sites.

Source: polynomial-PEPS, Lemma 6.5, `05-frames.tex`, lines 396–446.
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit.Party.Sheet

variable {ι P : Type} [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P]
  {q : ℕ} (S : Sheet ι P) {T E : Finset ι} {P₀ Q : P}
  (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

local notation "S'" => S.changeOwner T Q
local notation "X" => fun p ↦ W p × S.system q p
local notation "Y" => fun p ↦ W p × system q (S') p

/-- A birth in the site bases extended by untouched tag factors. Source: polynomial-PEPS,
Lemma 6.5, `05-frames.tex`, lines 396–437. -/
theorem exists_taggedBirthWord_of_environment (hTE : Disjoint T E)
    (hTP : ∀ x ∈ T, S.owner x = P₀) (hU : ∀ x ∉ T ∪ E, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    ∃ w : Word X Y,
      w.IsAllowed ∧ w.UsesOnly {P₀, Q} ∧ w.sourceCount ≤ 1 ∧
      w.op = reindex
        ((Equiv.arrowProdEquivProdArrow P W ((S').system q)).trans
          ((Equiv.refl _).prodCongr (blockConfigEquiv (S').owner (fun _ ↦ Fin q)))).symm
        ((Equiv.arrowProdEquivProdArrow P W (S.system q)).trans
          ((Equiv.refl _).prodCongr (blockConfigEquiv S.owner (fun _ ↦ Fin q)))).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ configBirthOp Finset.subset_union_left σ) := by
  obtain ⟨w, hA, hR, hn, hop, -⟩ := S.exists_birthWord_of_environment (Q := Q) hTE hTP hU σ 0
  refine ⟨w.frame W, Word.isAllowed_frame W hA, PartyCircuit.UsesOnly.frame W hR, ?_, ?_⟩
  · simpa only [Word.sourceCount, Word.sources_frame] using hn
  · rw [Word.op_frame, hop]
    rfl

/-- A death in the site bases extended by untouched tag factors. Source: polynomial-PEPS,
Lemma 6.5, `05-frames.tex`, lines 439–446. -/
theorem exists_taggedDeathChain_of_environment (hTE : Disjoint T E)
    (hTP : ∀ x ∈ T, S.owner x = P₀) (hU : ∀ x ∉ T ∪ E, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    ∃ M : PartyCircuit (ChainGate (P := P)) Y X,
      M.IsAllowed chainEv ChainGate.IsAllowed ∧ M.UsesOnly {P₀, Q} ∧
      M.ForallGate (fun _ _ _ g ↦ Sum.isRight g) ∧ M.numGates ≤ 1 ∧
      M.op chainEv = reindex
        ((Equiv.arrowProdEquivProdArrow P W (S.system q)).trans
          ((Equiv.refl _).prodCongr (blockConfigEquiv S.owner (fun _ ↦ Fin q)))).symm
        ((Equiv.arrowProdEquivProdArrow P W ((S').system q)).trans
          ((Equiv.refl _).prodCongr (blockConfigEquiv (S').owner (fun _ ↦ Fin q)))).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ configBirthOp Finset.subset_union_left σ) := by
  obtain ⟨M, hA, hR, hG, hn, hop, -⟩ := S.exists_deathChain_of_environment (Q := Q) hTE hTP hU σ 0
  refine ⟨M.frame W, PartyCircuit.isAllowed_frame W _ chainEv_isCompatible_frame
    (fun _ _ _ _ _ _ _ _ hg ↦ ChainGate.isAllowed_frame hg) hA,
    PartyCircuit.UsesOnly.frame W hR, PartyCircuit.forallGate_isRight_frame W M hG, ?_, ?_⟩
  · simpa only [PartyCircuit.numGates_frame] using hn
  · rw [PartyCircuit.op_frame W _ chainEv_isCompatible_frame, hop]
    rfl

end QuantumCircuit.Party.Sheet
