/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Matrix.ReindexSandwich
import QICLean.Circuit.Party.Compression.SourceReplacement.CorrectedTerm
import QICLean.Circuit.Party.Compression.SourceReplacement.Contraction
import QICLean.Circuit.Party.Compression.PartialExpansion.SubstitutionResidual

/-!
# Corrected source terms as source contractions

In a partial expansion, a label-selective basis substitution vanishes unless its labels are the
labels the branch chooses at the gates of the selected positions
(`SourceCircuit.partialSourceBasisMatrix_eq_ite`). Summing the labels therefore leaves the
corrected source operators at the ket and bra choices of the branches
(`SourceCircuit.correctedSourceTerm_eq_sum_coordinates`). The remaining operators are the
residuals of the branches applied after prepared slots, whatever vectors the selected slots
carry (`SourceCircuit.partialCoordinateBasisMatrix_eq_preparedMatrix`), so the corrected term of
a set of positions is a weighted sum over pairs of branches of source contractions of the
residuals (`SourceCircuit.correctedSourceTerm_eq_sourceContraction`): the selected slots carry
the corrected operators at the labels of the gates, all other slots their exact rank-one
operators.

## Main results

* `QuantumCircuit.Party.SourceCircuit.partialSourceBasisMatrix_eq_ite`,
  `QuantumCircuit.Party.SourceCircuit.correctedSourceTerm_eq_sum_coordinates`.
* `QuantumCircuit.Party.SourceCircuit.partialCoordinateBasisMatrix_eq_preparedMatrix`,
  `QuantumCircuit.Party.SourceCircuit.partialCoordinateBasisMatrix_reindex`.
* `QuantumCircuit.Party.SourceCircuit.correctedSourceTerm_eq_sourceContraction`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 338–434 (equation `eq:compression-subset-expansion`).

Adapted from TNLean, `TNLean/Lattice/Compression/SourceCorrectedContraction.lean`,
`TNLean/Lattice/Compression/SourceCorrectedSlots.lean` and
`TNLean/Lattice/Compression/SourceCorrectedContractionIdentity.lean` (Apache-2.0). Changes: the
input and output coordinates are configurations; the input density of a branch is read on the
blocks along `ManyBody.blockConfigEquiv`.
-/

open Matrix ManyBody
open scoped ComplexConjugate

namespace QuantumCircuit.Party

/-- Summing label-selective coefficients leaves the labels `l`, `l'`. The decidability instances
are arbitrary, so that the identity applies to the instances of its users. -/
private theorem sum_labelBasis_density {I m n : Type} [Fintype I] [DecidableEq I] [Fintype n]
    {L C : I → Type} [∀ i, Fintype (L i)] [∀ i, Fintype (C i)]
    (l l' : ∀ i, L i) [dl : ∀ u : (∀ i, L i), Decidable (u = l)]
    [dl' : ∀ u : (∀ i, L i), Decidable (u = l')] (E : ∀ i, L i → L i → C i → C i → ℂ)
    (K K' : (∀ i, C i) → Matrix m n ℂ) (ρ : Matrix n n ℂ) :
    (∑ u : ∀ i, L i × C i, ∑ v : ∀ i, L i × C i,
      (∏ i, E i (u i).1 (v i).1 (u i).2 (v i).2) •
        ((if (fun i ↦ (u i).1) = l then K (fun i ↦ (u i).2) else 0) * ρ *
          (if (fun i ↦ (v i).1) = l' then K' (fun i ↦ (v i).2) else 0)ᴴ)) =
      ∑ a, ∑ b, (∏ i, E i (l i) (l' i) (a i) (b i)) • (K a * ρ * (K' b)ᴴ) := by
  let : DecidableEq (∀ i, L i) := Classical.decEq _
  obtain rfl : dl = fun u ↦ this u l := Subsingleton.elim _ _
  obtain rfl : dl' = fun u ↦ this u l' := Subsingleton.elim _ _
  let e := Equiv.arrowProdEquivProdArrow I L C
  calc
    _ = ∑ u : (∀ i, L i) × (∀ i, C i), ∑ v : (∀ i, L i) × (∀ i, C i),
      (∏ i, E i (u.1 i) (v.1 i) (u.2 i) (v.2 i)) •
        ((if u.1 = l then K u.2 else 0) * ρ * (if v.1 = l' then K' v.2 else 0)ᴴ) :=
      Fintype.sum_equiv e _ _ fun u ↦ Fintype.sum_equiv e _ _ fun v ↦ rfl
    _ = _ := by
      have h (p q : Prop) [Decidable p] [Decidable q] (M N : Matrix m n ℂ) :
          (if p then M else 0) * ρ * (if q then N else 0)ᴴ =
            if p then if q then M * ρ * Nᴴ else 0 else 0 := by
        split_ifs <;> simp
      simp only [Fintype.sum_prod_type, h, smul_ite, smul_zero]
      simp

variable {P : Type} [DecidableEq P] [Fintype P]

namespace SourceInventory

/-- A zero slot vector prepares nothing. -/
private theorem op_prepareSlots_eq_zero (R : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type) [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] (i : Fin R.length) (hi : η i = 0) :
    (prepareSlots R B η X).op = 0 := by
  rw [op_prepareSlots]
  ext y x
  simp only [prepMatrix_apply, slotVector_apply, Matrix.zero_apply]
  split_ifs
  · exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; rfl)
  · rfl

end SourceInventory

namespace SourceCircuit

variable (A : P → Bool) {X Y : P → Type}

omit [Fintype P] in
/-- A substitution at positions with an affected endpoint changes no position with two exterior
endpoints. -/
private theorem selectedSourceVectors_exterior (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (η : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e))
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true) :
    ∀ e ξ, A (w.endpoints e).1 = false → A (w.endpoints e).2 = false →
      selectedSourceVectors w S η e ξ = w.sourceVectorAt e ξ := by
  intro e ξ hl hr
  have he : e ∉ S := fun h ↦ by simpa [hl, hr] using hS e h
  simp only [selectedSourceVectors, he, ite_false]

/-- A substituted branch reads only the vectors at the labels it chooses at the touched gates. -/
private theorem partialWithSources_congr : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (η θ : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e)) → (ξ : Choices A w) →
    (∀ e (h : IsTouched A w e.1), η e (choiceAt A w ξ e.1 h) = θ e (choiceAt A w ξ e.1 h)) →
      partialWithSources A w η ξ = partialWithSources A w θ ξ
  | _, _, _, _, PartyCircuit.done _, _, _, _, _ => rfl
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g, η, θ, ξ, h => by
    by_cases hD : PreparedGate.IsTouched A D
    · change dite _ _ _ = dite _ _ _
      rw [dite_eq_left hD, dite_eq_left hD]
      congr 3
      funext i
      exact h ⟨(), i⟩ hD
    · change dite _ _ _ = dite _ _ _
      rw [dite_eq_right hD, dite_eq_right hD]
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, _, _ => rfl
  | _, _, _, _, PartyCircuit.localOps _, _, _, _, _ => rfl
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', _, _, ξ, h =>
    congrArg₂ PartyCircuit.comp
      (partialWithSources_congr c _ _ ξ.1 fun e he ↦ h ⟨Sum.inl e.1, e.2⟩ he)
      (partialWithSources_congr c' _ _ ξ.2 fun e he ↦ h ⟨Sum.inr e.1, e.2⟩ he)

/-- A substituted branch with the zero vector at a chosen label of a touched gate vanishes. -/
private theorem op_partialWithSources_eq_zero : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (η : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e)) → (ξ : Choices A w) →
    (e : w.sourceLocations) → (h : IsTouched A w e.1) → η e (choiceAt A w ξ e.1 h) = 0 →
      Word.op (partialWithSources A w η ξ) = 0
  | _, _, _, _, PartyCircuit.done _, _, _, e, _, _ => Empty.elim e.1
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g, η, ξ, e, h, hz => by
    change Word.op (dite _ _ _) = 0
    rw [dite_eq_left (show PreparedGate.IsTouched A D from h), Word.op_coarsen, Word.op_onCell]
    have hb : Word.op (g.gate.branchWithSources (choiceLabel A hY g h ξ)
        fun i ↦ η ⟨(), i⟩ (choiceLabel A hY g h ξ)) = 0 := by
      refine (Word.op_comp _ _).trans ?_
      rw [SourceInventory.op_prepareSlots_eq_zero g.gate.slots g.gate.bases
        (fun i ↦ η ⟨(), i⟩ (choiceLabel A hY g h ξ)) _ e.2 hz, Matrix.mul_zero]
    rw [hb, placeBetween_zero]
    ext
    rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, e, _, _ => Empty.elim e.1
  | _, _, _, _, PartyCircuit.localOps _, _, _, e, _, _ => Empty.elim e.1
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', η, ξ, e, h, hz => by
    rw [partialWithSources_comp, Word.op_comp]
    match e, h, hz with
    | ⟨Sum.inl g, i⟩, h, hz =>
      rw [op_partialWithSources_eq_zero c (fun e ↦ η ⟨Sum.inl e.1, e.2⟩) ξ.1 ⟨g, i⟩ h hz,
        Matrix.mul_zero]
    | ⟨Sum.inr g, i⟩, h, hz =>
      rw [op_partialWithSources_eq_zero c' (fun e ↦ η ⟨Sum.inr e.1, e.2⟩) ξ.2 ⟨g, i⟩ h hz,
        Matrix.zero_mul]

variable [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

open Classical in
/-- **A label-selective partial matrix vanishes unless its labels are the choices of the
branch**; otherwise only basis vectors are inserted. Source: Theorem 5.2, `04-compression.tex`,
lines 351–417. -/
theorem partialSourceBasisMatrix_eq_ite (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (u : SourceBasisChoice w S) (ξ : Choices A w) :
    partialSourceBasisMatrix A w S u ξ =
      if (fun e : S ↦ (u e).1) =
          fun e : S ↦ choiceAt A w ξ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2))
      then partialCoordinateBasisMatrix A w S (fun e ↦ (u e).2) ξ else 0 := by
  split_ifs with hu
  · unfold partialSourceBasisMatrix partialCoordinateBasisMatrix
    rw [partialWithSources_congr A w _ _ ξ fun e h ↦ ?_]
    by_cases he : e ∈ S
    · have hc : choiceAt A w ξ e.1 h = (u ⟨e, he⟩).1 := (congrFun hu ⟨e, he⟩).symm
      simp only [selectedSourceVectors, he, ite_true, labelBasisVectors, coordinateBasisVectors,
        dite_true, hc, ite_true]
    · simp only [selectedSourceVectors, he, ite_false]
  · obtain ⟨e, he⟩ := Function.ne_iff.mp hu
    unfold partialSourceBasisMatrix
    rw [op_partialWithSources_eq_zero A w _ ξ e.1
      (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2))]
    · ext
      rfl
    · simp only [selectedSourceVectors, e.2, ite_true, labelBasisVectors, dite_true,
        ite_eq_right_iff]
      exact fun h ↦ absurd h.symm he

/-- **Each corrected source operator is read at the labels the branches choose**: different
corrected slots of one gate share its label, and its coefficient occurs once. Source:
Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem correctedSourceTerm_eq_sum_coordinates (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    correctedSourceTerm w S E ρ =
      ∑ ξ, ∑ ζ, (coefficient A w ξ * conj (coefficient A w ζ)) •
        (∑ u : SelectedSourceCoordinates w S, ∑ v : SelectedSourceCoordinates w S,
          (∏ e : S, E e.1
            (choiceAt A w ξ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2)))
            (choiceAt A w ζ e.1.1 (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2)))
            (u e) (v e)) •
            (partialCoordinateBasisMatrix A w S u ξ * ρ *
              (partialCoordinateBasisMatrix A w S v ζ)ᴴ)) := by
  classical
  rw [correctedSourceTerm_eq_sum_partial A w S hS E ρ]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ congrArg (_ • ·) ?_
  have hK (u : SourceBasisChoice w S) := partialSourceBasisMatrix_eq_ite A w S hS u ξ
  have hK' (u : SourceBasisChoice w S) := partialSourceBasisMatrix_eq_ite A w S hS u ζ
  simp only [hK, hK']
  exact sum_labelBasis_density (L := fun e : S ↦ w.branchLabels e.1.1)
    (C := fun e : S ↦ w.leftBasis e.1 × w.rightBasis e.1) _ _ (fun e ↦ E e.1)
    (partialCoordinateBasisMatrix A w S · ξ) (partialCoordinateBasisMatrix A w S · ζ) ρ

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- **The coordinate-substituted partial matrix is the residual of the branch after prepared
slots**, for every choice of basis vectors; the unselected slots keep their vectors. Source:
Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem partialCoordinateBasisMatrix_eq_preparedMatrix (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (u : SelectedSourceCoordinates w S) (ξ : Choices A w) :
    partialCoordinateBasisMatrix A w S u ξ =
      reindex (blockConfigEquiv (affectedOwner A) Y) (blockConfigEquiv (affectedOwner A) X)
        ((partialResidual A w ξ).preparedMatrix (partialSlots A w) (partialSlotBases A w)
          (fun i ↦ selectedSourceVectors w S (coordinateBasisVectors w S u)
            (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i))
          (blockSystem (affectedOwner A) X)) := by
  exact congrArg _ (op_partialResidual_mul_prepareSlots_substituted A w _
    (selectedSourceVectors_exterior A w S (coordinateBasisVectors w S u) hS) ξ).symm

/-- **The substitution at the selected positions is the preparation of basis vectors in the
selected slots**, read through the identification of the selected slots with the positions.
Source: Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem partialCoordinateBasisMatrix_reindex (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (u : ∀ i : selectedPartialSlots A w S,
      w.leftBasis (partialSlotEquiv A w i.1).1 × w.rightBasis (partialSlotEquiv A w i.1).1)
    (ξ : Choices A w) :
    partialCoordinateBasisMatrix A w S (selectedSourceCoordinateEquiv A w S hS u) ξ =
      reindex (blockConfigEquiv (affectedOwner A) Y) (blockConfigEquiv (affectedOwner A) X)
        ((partialResidual A w ξ).preparedMatrix (partialSlots A w) (partialSlotBases A w)
          (fun i ↦ if h : i ∈ selectedPartialSlots A w S then EuclideanSpace.single (u ⟨i, h⟩) 1
            else partialSlotVector A w ξ i)
          (blockSystem (affectedOwner A) X)) := by
  rw [partialCoordinateBasisMatrix_eq_preparedMatrix A w S hS]
  congr 3
  funext i
  by_cases hi : i ∈ selectedPartialSlots A w S
  · have he := (mem_selectedPartialSlots A w S i).mp hi
    have hc := selectedSourceCoordinateEquiv_apply A w S hS u ⟨i, hi⟩
    simp only [selectedSourceVectors, he, ite_true, coordinateBasisVectors, dite_true, hi]
    exact congrArg (fun z ↦ EuclideanSpace.single z (1 : ℂ)) hc
  · have he := mt (mem_selectedPartialSlots A w S i).mpr hi
    rw [dite_eq_right hi]
    simp only [selectedSourceVectors, he, ite_false, partialSlotVector]

/-- **The corrected term of a set of positions is the partial-branch sum of source contractions
of the residuals**: for every affected set meeting each selected position, the selected slots
carry the corrected operators at the labels of the branches, all other slots the rank-one
operators of their vectors. Source: Theorem 5.2, `04-compression.tex`, lines 338–434. -/
theorem correctedSourceTerm_eq_sourceContraction (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    correctedSourceTerm w S E ρ =
      ∑ ξ, ∑ ζ, (coefficient A w ξ * conj (coefficient A w ζ)) •
        reindex (blockConfigEquiv (affectedOwner A) Y) (blockConfigEquiv (affectedOwner A) Y)
          (sourceContraction
            (fun z ↦ (partialResidual A w ξ).preparedDensityCoefficient (partialSlots A w)
              (partialSlotBases A w) (blockSystem (affectedOwner A) X)
              (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
              (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
              (partialResidual A w ζ)
              (reindex (blockConfigEquiv (affectedOwner A) X).symm
                (blockConfigEquiv (affectedOwner A) X).symm ρ)
              (fun i ↦ (z i).1) (fun i ↦ (z i).2))
            (fun i ↦ if i ∈ selectedPartialSlots A w S then
                E (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i) (partialSlotChoice A w ζ i)
              else vecMulVec (fun a ↦ partialSlotVector A w ξ i a)
                (fun a ↦ conj (partialSlotVector A w ζ i a)))) := by
  classical
  rw [correctedSourceTerm_eq_sum_coordinates A w S hS]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ congrArg (_ • ·) ?_
  rw [Word.sourceContraction_preparedDensityCoefficient_selected (partialSlots A w)
    (partialSlotBases A w) (blockSystem (affectedOwner A) X) (partialSlotVector A w ξ)
    (partialSlotVector A w ζ) (selectedPartialSlots A w S)
    (fun i ↦ E (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i) (partialSlotChoice A w ζ i))
    (partialResidual A w ξ) (partialResidual A w ζ)]
  rw [← Matrix.coe_reindexLinearEquiv ℂ ℂ, map_sum]
  symm
  refine Fintype.sum_equiv (selectedSourceCoordinateEquiv A w S hS) _ _ fun a ↦ ?_
  rw [map_sum]
  refine Fintype.sum_equiv (selectedSourceCoordinateEquiv A w S hS) _ _ fun b ↦ ?_
  rw [LinearEquiv.map_smul, partialCoordinateBasisMatrix_reindex,
    partialCoordinateBasisMatrix_reindex, reindex_mul_mul_conjTranspose,
    Matrix.coe_reindexLinearEquiv]
  congr 1
  refine Fintype.prod_equiv (selectedPartialSlotEquiv A w S hS) _ _ fun i ↦ ?_
  rw [selectedSourceCoordinateEquiv_apply, selectedSourceCoordinateEquiv_apply]
  rfl

end SourceCircuit

end QuantumCircuit.Party
