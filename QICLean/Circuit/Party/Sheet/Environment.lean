/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Sheet.Placement
import Mathlib.Logic.Equiv.Set

/-!
# Bases of a sheet with a prescribed environment

For a birth or death at the central party, an environment can contain sites
of that party. The central basis before the birth splits into the central
sites in the environment, the region handed to the recipient, and the
remaining sites. The environmental factor stays at the central party.

Source: polynomial-PEPS, Lemma 6.5, `05-frames.tex`, lines 396–410.
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.Sheet

variable {ι P : Type} [Fintype ι] [DecidableEq ι] [DecidableEq P]
  {q : ℕ} {S : Sheet ι P} {T E : Finset ι} {P₀ Q : P}

omit [Fintype ι] [DecidableEq P] in
private theorem owner_eq_iff_environment (hTP : ∀ x ∈ T, S.owner x = P₀)
    (hU : ∀ x ∉ T ∪ E, S.owner x = P₀) (x : ι) :
    S.owner x = P₀ ↔ (x ∈ E ∧ S.owner x = P₀) ∨ (x ∈ T ∨ x ∉ T ∪ E) :=
  ⟨fun h ↦ if hE : x ∈ E then Or.inl ⟨hE, h⟩
    else if hT : x ∈ T then Or.inr (Or.inl hT)
    else Or.inr (Or.inr (fun hx ↦ (Finset.mem_union.mp hx).elim hT hE)),
    fun h ↦ h.elim And.right (fun h' ↦ h'.elim (hTP x) (hU x))⟩

/-- The central basis before a birth consists of its environmental sites, the sites of
`T`, and the sites outside `T ∪ E`. -/
def birthEnvironmentEquiv (hTE : Disjoint T E) (hTP : ∀ x ∈ T, S.owner x = P₀)
    (hU : ∀ x ∉ T ∪ E, S.owner x = P₀) :
    S.system q P₀ ≃ ({x // x ∈ E ∧ S.owner x = P₀} → Fin q) ×
      (RegionConfig (fun _ : ι ↦ Fin q) T × ComplConfig (fun _ : ι ↦ Fin q) (T ∪ E)) := by
  have hdis : Disjoint (↑T : Set ι) {x | x ∉ T ∪ E} :=
    Set.disjoint_left.mpr fun x hT hU' ↦ hU' (Finset.mem_union_left E hT)
  let e := (Equiv.Set.union hdis).arrowCongr (Equiv.refl (Fin q))
  exact (S.splitEquiv q P₀ (fun x ↦ x ∈ E ∧ S.owner x = P₀)
    (fun x ↦ x ∈ T ∨ x ∉ T ∪ E) (owner_eq_iff_environment hTP hU)
    (fun x hx hb ↦ hb.elim (fun hT ↦ Finset.disjoint_left.mp hTE hT hx.1)
      (fun hU' ↦ hU' (Finset.mem_union_right T hx.1)))).trans
    ((Equiv.refl _).prodCongr (e.trans (Equiv.sumArrowEquivProdArrow _ _ _)))

/-- After a birth to a different party, the central basis retains the same environmental
factor and the sites outside `T ∪ E`. -/
def birthEnvironmentEquivAfter (hTE : Disjoint T E) (hQP : Q ≠ P₀)
    (hU : ∀ x ∉ T ∪ E, S.owner x = P₀) :
    (S.changeOwner T Q).system q P₀ ≃ ({x // x ∈ E ∧ S.owner x = P₀} → Fin q) ×
      ComplConfig (fun _ : ι ↦ Fin q) (T ∪ E) :=
  (S.changeOwner T Q).splitEquiv q P₀ (fun x ↦ x ∈ E ∧ S.owner x = P₀)
    (· ∉ T ∪ E) (fun x ↦ by
      by_cases hT : x ∈ T
      · have hE : x ∉ E := Finset.disjoint_left.mp hTE hT
        simp [changeOwner, hT, hE, hQP]
      · by_cases hE : x ∈ E
        · simp [changeOwner, hT, hE]
        · simpa [changeOwner, hT, hE] using hU x (by simp [hT, hE]))
    fun _ hE hU' ↦ hU' (Finset.mem_union_right T hE.1)

private theorem exists_privateBirthMatrix_of_environment [Fintype P]
    (hTP : ∀ x ∈ T, S.owner x = P₀) (hU : ∀ x ∉ T ∪ E, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    ∃ L : Matrix (S.system q P₀) (S.system q P₀) ℂ, ‖L‖ ≤ 1 ∧
      (PartyCircuit.localOp (G := SourceGate) P₀ (fun _ _ ↦ rfl) L).op SourceGate.ev =
        reindex (blockConfigEquiv S.owner (fun _ ↦ Fin q)).symm
          (blockConfigEquiv S.owner (fun _ ↦ Fin q)).symm
          (configBirthOp Finset.subset_union_left σ) := by
  classical
  let X : ι → Type := fun _ ↦ Fin q
  let D := blockPreimage S.owner {P₀}
  have hsub : ((T ∪ E) \ T)ᶜ ⊆ D := by
    intro x hx
    apply (mem_blockPreimage_singleton S.owner).mpr
    by_cases hT : x ∈ T
    · exact hTP x hT
    · exact hU x fun hTE' ↦ (Finset.mem_compl.mp hx) (Finset.mem_sdiff.mpr ⟨hTE', hT⟩)
  have hsup := (isSupportedOn_configBirthOp Finset.subset_union_left σ).mono hsub
  let e := blockConfigEquiv S.owner X
  rcases isEmpty_or_nonempty (Config X) with he | hx
  · let : IsEmpty (Config (S.system q)) := ⟨fun z ↦ he.false (e z)⟩
    let L : Matrix (S.system q P₀) (S.system q P₀) ℂ := 0
    refine ⟨L, ?_, Subsingleton.elim _ _⟩
    simp [L]
  · let x := Classical.choice hx
    have hsites : ∀ _ : ι, Nonempty (Fin q) := fun v ↦ ⟨x v⟩
    obtain ⟨K, hK⟩ := exists_eq_place_of_mem_supportedOperators hsup
    have hn : ‖K‖ ≤ 1 := by
      rw [← @norm_place ι _ _ (fun _ ↦ Fin q) _ D _ hsites K, ← hK]
      exact norm_configBirthOp_le_one Finset.subset_union_left σ
    let ε := blockRegionConfigEquiv S.owner X {P₀}
    let M := reindex ε.symm ε.symm K
    let a := siteEquiv (S.system q) P₀
    let L := reindex a a M
    have hL : ‖L‖ ≤ 1 :=
      (l2_opNorm_reindex_le _ _ _).trans ((l2_opNorm_reindex_le _ _ _).trans hn)
    let w : Word (S.system q) (S.system q) := PartyCircuit.localOp P₀ (fun _ _ ↦ rfl) L
    refine ⟨L, hL, ?_⟩
    change w.op = _
    have hop : w.op = place {P₀} M := by
      dsimp only [w]
      rw [Word.op, PartyCircuit.op_localOp, placeBetween_eq_place]
      congr 1
      ext y z
      change M (a.symm (a y)) (a.symm (a z)) = M y z
      simp
    rw [hop, hK]
    apply (reindex e e).injective
    change reindex (blockConfigEquiv S.owner X) (blockConfigEquiv S.owner X) (place {P₀} M) =
      reindex e e (reindex e.symm e.symm (place D K))
    refine (reindex_blockConfigEquiv_place S.owner (X := X) {P₀} M).trans ?_
    calc
      place D (reindex ε ε M) = place D K :=
        congrArg (place D) ((reindex ε ε).apply_symm_apply K)
      _ = reindex e e (reindex e.symm e.symm (place D K)) :=
        ((reindex e e).apply_symm_apply (place D K)).symm

/-- If the recipient is the central party itself, the canonical birth operator is one
allowed local contraction. The environment may contain sites of the central party.
The contraction leaves the environment fixed. Source: polynomial-PEPS, Lemma 6.5,
`05-frames.tex`, lines 434–446. -/
theorem exists_privateBirthWord_of_environment [Fintype P]
    (hTP : ∀ x ∈ T, S.owner x = P₀) (hU : ∀ x ∉ T ∪ E, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    ∃ w : Word (S.system q) (S.system q),
      w.IsAllowed ∧ w.UsesOnly {P₀} ∧ w.sourceCount = 0 ∧
      w.op = reindex (blockConfigEquiv S.owner (fun _ ↦ Fin q)).symm
        (blockConfigEquiv S.owner (fun _ ↦ Fin q)).symm
        (configBirthOp Finset.subset_union_left σ) := by
  obtain ⟨L, hn, hop⟩ := exists_privateBirthMatrix_of_environment hTP hU σ
  exact ⟨PartyCircuit.localOp P₀ (fun _ _ ↦ rfl) L, Word.isAllowed_localOp _ _ _ hn,
    Set.mem_singleton P₀, rfl, hop⟩

/-- A private death with a prescribed environment is the same allowed local contraction
as the private birth. Its chain has no pair effects. Source: polynomial-PEPS, Lemma 6.5,
`05-frames.tex`, lines 445–446. -/
theorem exists_privateDeathChain_of_environment [Fintype P]
    (hTP : ∀ x ∈ T, S.owner x = P₀) (hU : ∀ x ∉ T ∪ E, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    ∃ M : PartyCircuit (ChainGate (P := P)) (S.system q) (S.system q),
      M.IsAllowed chainEv ChainGate.IsAllowed ∧ M.UsesOnly {P₀} ∧
      M.ForallGate (fun _ _ _ g ↦ Sum.isRight g) ∧ M.numGates = 0 ∧
      M.op chainEv = reindex (blockConfigEquiv S.owner (fun _ ↦ Fin q)).symm
        (blockConfigEquiv S.owner (fun _ ↦ Fin q)).symm
        (configBirthOp Finset.subset_union_left σ) := by
  obtain ⟨L, hn, hop⟩ := exists_privateBirthMatrix_of_environment hTP hU σ
  refine ⟨PartyCircuit.localOp P₀ (fun _ _ ↦ rfl) L, hn, Set.mem_singleton P₀, trivial, rfl, ?_⟩
  simpa only [PartyCircuit.op_localOp] using hop

end QuantumCircuit.Party.Sheet
