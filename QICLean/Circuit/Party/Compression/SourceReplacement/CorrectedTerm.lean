/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Substitution
import QICLean.Algebra.Matrix.MatrixDensitySum

/-!
# Corrected source terms of a source circuit

A selected set `S` of source positions carries, at each position, a label of its gate and a pair
of basis elements of its slot (`SourceCircuit.SourceBasisChoice`); the basis vector is inserted at
the selected label and zero at the other labels of the same gate (`labelBasisVectors`), so
different selected slots of one gate keep a common label and the coefficient of the gate occurs
once on each side. The operator of the circuit after this substitution is
`SourceCircuit.sourceBasisMatrix`, and the corrected term of `S` with source operators `E` is the
sum of their entries times the mixed densities of these operators
(`SourceCircuit.correctedSourceTerm`); the empty set gives the density of the circuit. For every
set `A` of affected parties meeting each selected position, the same term is a sum over the
branches of the partial expansion at `A` (`correctedSourceTerm_eq_sum_partial`). The selected
positions correspond to the slots of the partial expansion they occupy
(`selectedPartialSlotEquiv`).

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.SourceBasisChoice`,
  `QuantumCircuit.Party.SourceCircuit.labelBasisVectors`,
  `QuantumCircuit.Party.SourceCircuit.sourceBasisMatrix`,
  `QuantumCircuit.Party.SourceCircuit.correctedSourceTerm`,
  `QuantumCircuit.Party.SourceCircuit.partialSourceBasisMatrix`.
* `QuantumCircuit.Party.SourceCircuit.SelectedSourceCoordinates`,
  `QuantumCircuit.Party.SourceCircuit.coordinateBasisVectors`,
  `QuantumCircuit.Party.SourceCircuit.partialCoordinateBasisMatrix`.
* `QuantumCircuit.Party.SourceCircuit.selectedPartialSlots`,
  `QuantumCircuit.Party.SourceCircuit.selectedPartialSlotEquiv`,
  `QuantumCircuit.Party.SourceCircuit.selectedSourceCoordinateEquiv`.

## Main results

* `QuantumCircuit.Party.SourceCircuit.correctedSourceTerm_empty`.
* `QuantumCircuit.Party.SourceCircuit.sourceBasisMatrix_eq_sum_partial`,
  `QuantumCircuit.Party.SourceCircuit.correctedSourceTerm_eq_sum_partial`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 338–417 (equation `eq:compression-subset-expansion`).

Adapted from TNLean, `TNLean/Lattice/Compression/SourceCorrectedTerm.lean`,
`TNLean/Lattice/Compression/SourceCorrectedSlots.lean` and the definitions of
`TNLean/Lattice/Compression/SourceCorrectedContraction.lean` (Apache-2.0). Changes: the input and
output coordinates are the configurations, so the endpoint coordinates are the bases of the
slots; partial matrices are read back along `ManyBody.blockConfigEquiv`.
-/

open Matrix ManyBody
open scoped ComplexConjugate

namespace QuantumCircuit.Party

namespace SourceCircuit

variable {P : Type} [DecidableEq P] {X Y : P → Type}

/-! ### Label-selective basis substitutions -/

/-- A label of the gate and a pair of basis elements of the slot at every selected position.
Source: Theorem 5.2, `04-compression.tex`, lines 342–355. -/
def SourceBasisChoice (w : SourceCircuit X Y) (S : Finset w.sourceLocations) : Type :=
  ∀ e : S, w.branchLabels e.1.1 × (w.leftBasis e.1 × w.rightBasis e.1)

/-- There are finitely many labels and basis elements at the selected positions. -/
noncomputable instance instFintypeSourceBasisChoice (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations) : Fintype (SourceBasisChoice w S) := by
  classical
  exact inferInstanceAs (Fintype (∀ e : S, w.branchLabels e.1.1 ×
    (w.leftBasis e.1 × w.rightBasis e.1)))

open Classical in
/-- The basis vector at the selected label of a selected position, and zero at the other labels
of its gate; the values outside the selected positions are zero and are not used. Source:
Theorem 5.2, `04-compression.tex`, lines 342–381. -/
noncomputable def labelBasisVectors (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (u : SourceBasisChoice w S) (e : w.sourceLocations) (ξ : w.branchLabels e.1) :
    EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e) :=
  if he : e ∈ S then if ξ = (u ⟨e, he⟩).1 then EuclideanSpace.single (u ⟨e, he⟩).2 1 else 0
  else 0

/-- A pair of basis elements of the slot at every selected position. Source: Theorem 5.2,
`04-compression.tex`, lines 351–417. -/
def SelectedSourceCoordinates (w : SourceCircuit X Y) (S : Finset w.sourceLocations) : Type :=
  ∀ e : S, w.leftBasis e.1 × w.rightBasis e.1

/-- There are finitely many basis elements at the selected positions. -/
noncomputable instance instFintypeSelectedSourceCoordinates (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations) : Fintype (SelectedSourceCoordinates w S) := by
  classical
  exact inferInstanceAs (Fintype (∀ e : S, w.leftBasis e.1 × w.rightBasis e.1))

section Slots

variable (A : P → Bool)

/-! ### Selected positions in the slots -/

open Classical in
/-- The slots of the partial expansion at `A` occupied by the selected positions. Source:
Theorem 5.2, `04-compression.tex`, lines 351–417. -/
noncomputable def selectedPartialSlots (w : SourceCircuit X Y) (S : Finset w.sourceLocations) :
    Finset (Fin (partialSlots A w).length) :=
  Finset.univ.filter fun i ↦ (partialSlotEquiv A w i).1 ∈ S

/-- A slot is selected exactly when its position is. Source: Theorem 5.2, `04-compression.tex`,
lines 351–417. -/
theorem mem_selectedPartialSlots (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (i : Fin (partialSlots A w).length) :
    i ∈ selectedPartialSlots A w S ↔ (partialSlotEquiv A w i).1 ∈ S := by
  classical
  simp [selectedPartialSlots]

/-- **Every selected position with an affected endpoint occupies exactly one slot.** Source:
Theorem 5.2, `04-compression.tex`, lines 351–417. -/
noncomputable def selectedPartialSlotEquiv (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true) :
    selectedPartialSlots A w S ≃ S where
  toFun i := ⟨(partialSlotEquiv A w i.1).1, (mem_selectedPartialSlots A w S i.1).mp i.2⟩
  invFun e := ⟨(partialSlotEquiv A w).symm ⟨e.1, hS e.1 e.2⟩, by
    rw [mem_selectedPartialSlots, Equiv.apply_symm_apply]
    exact e.2⟩
  left_inv i := Subtype.ext ((partialSlotEquiv A w).symm_apply_apply i.1)
  right_inv e := by
    have h := congrArg Subtype.val ((partialSlotEquiv A w).apply_symm_apply ⟨e.1, hS e.1 e.2⟩)
    exact Subtype.ext h

/-- The position of a selected slot. -/
@[simp] theorem selectedPartialSlotEquiv_apply (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (i : selectedPartialSlots A w S) :
    (selectedPartialSlotEquiv A w S hS i).1 = (partialSlotEquiv A w i.1).1 :=
  rfl

/-- The basis elements at the selected slots read at the selected positions. Source: Theorem 5.2,
`04-compression.tex`, lines 351–417. -/
noncomputable def selectedSourceCoordinateEquiv (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true) :
    (∀ i : selectedPartialSlots A w S,
      w.leftBasis (partialSlotEquiv A w i.1).1 × w.rightBasis (partialSlotEquiv A w i.1).1) ≃
      SelectedSourceCoordinates w S :=
  Equiv.piCongrLeft (fun e : S ↦ w.leftBasis e.1 × w.rightBasis e.1)
    (selectedPartialSlotEquiv A w S hS)

/-- At the position of a selected slot the reindexed coordinates are those of the slot. Source:
Theorem 5.2, `04-compression.tex`, lines 351–417. -/
theorem selectedSourceCoordinateEquiv_apply (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (u : ∀ i : selectedPartialSlots A w S,
      w.leftBasis (partialSlotEquiv A w i.1).1 × w.rightBasis (partialSlotEquiv A w i.1).1)
    (i : selectedPartialSlots A w S) :
    selectedSourceCoordinateEquiv A w S hS u (selectedPartialSlotEquiv A w S hS i) = u i :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

end Slots

variable [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- The operator of the circuit after a label-selective basis substitution at the selected
positions. Source: Theorem 5.2, `04-compression.tex`, lines 342–381. -/
noncomputable def sourceBasisMatrix (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (u : SourceBasisChoice w S) : Matrix (Config Y) (Config X) ℂ :=
  opWithSources w (selectedSourceVectors w S (labelBasisVectors w S u))

/-- **The corrected term of a set of source positions**: the entries of the source operators
`E e ξ ζ` at the labels and basis elements of the ket and bra substitutions times the mixed
density of the substituted operators. It does not depend on an affected set or a partial
expansion. Source: Theorem 5.2, `eq:compression-subset-expansion`, `04-compression.tex`,
lines 338–381. -/
noncomputable def correctedSourceTerm (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (ρ : Matrix (Config X) (Config X) ℂ) : Matrix (Config Y) (Config Y) ℂ :=
  ∑ u : SourceBasisChoice w S, ∑ v : SourceBasisChoice w S,
    (∏ e : S, E e.1 (u e).1 (v e).1 (u e).2 (v e).2) •
      (sourceBasisMatrix w S u * ρ * (sourceBasisMatrix w S v)ᴴ)

/-- **The empty corrected set is the density of the circuit.** Source: Theorem 5.2,
`04-compression.tex`, lines 342–355. -/
theorem correctedSourceTerm_empty (w : SourceCircuit X Y)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    correctedSourceTerm w ∅ E ρ = w.op * ρ * w.opᴴ := by
  classical
  let : Unique (SourceBasisChoice w ∅) := by
    unfold SourceBasisChoice
    infer_instance
  have hη (u : SourceBasisChoice w ∅) :
      selectedSourceVectors w ∅ (labelBasisVectors w ∅ u) = w.sourceVectorAt := by
    funext e ξ
    simp [selectedSourceVectors]
  simp only [correctedSourceTerm, sourceBasisMatrix, hη, opWithSources_original,
    Fintype.sum_unique]
  simp

variable (A : P → Bool)

/-- A label-selective basis substitution in one branch of the partial expansion at `A`, read
back on the parties along `ManyBody.blockConfigEquiv`. Source: Theorem 5.2,
`04-compression.tex`, lines 351–381. -/
noncomputable def partialSourceBasisMatrix (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations) (u : SourceBasisChoice w S) (ξ : Choices A w) :
    Matrix (Config Y) (Config X) ℂ :=
  reindex (blockConfigEquiv (affectedOwner A) Y) (blockConfigEquiv (affectedOwner A) X)
    (Word.op (partialWithSources A w (selectedSourceVectors w S (labelBasisVectors w S u)) ξ))

/-- **The substitution is obtained by expanding only the gates touching the affected parties**,
when every selected position has an affected endpoint; the other gates stay whole. Source:
Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem sourceBasisMatrix_eq_sum_partial (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (u : SourceBasisChoice w S)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true) :
    sourceBasisMatrix w S u = ∑ ξ, coefficient A w ξ • partialSourceBasisMatrix A w S u ξ := by
  have h := sum_coefficient_smul_op_partialWithSources_selected A w S (labelBasisVectors w S u) hS
  ext y x
  have h' := congrFun (congrFun h ((blockConfigEquiv (affectedOwner A) Y).symm y))
    ((blockConfigEquiv (affectedOwner A) X).symm x)
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    Matrix.sum_apply, Matrix.smul_apply] at h'
  simp only [sourceBasisMatrix, partialSourceBasisMatrix, Matrix.sum_apply, Matrix.smul_apply,
    reindex_apply, submatrix_apply, h']

/-- **The corrected term admits the partial expansion at every affected set meeting each selected
position**, with the same positions and labels; gates outside the set are not expanded. Source:
Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem correctedSourceTerm_eq_sum_partial (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    correctedSourceTerm w S E ρ =
      ∑ ξ, ∑ ζ, (coefficient A w ξ * conj (coefficient A w ζ)) •
        (∑ u : SourceBasisChoice w S, ∑ v : SourceBasisChoice w S,
          (∏ e : S, E e.1 (u e).1 (v e).1 (u e).2 (v e).2) •
            (partialSourceBasisMatrix A w S u ξ * ρ * (partialSourceBasisMatrix A w S v ζ)ᴴ)) := by
  classical
  unfold correctedSourceTerm
  simp_rw [sourceBasisMatrix_eq_sum_partial A w S _ hS, Matrix.sum_smul_mul_mul_conjTranspose,
    Finset.smul_sum, smul_smul]
  conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext ξ; arg 2; ext u; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext ξ; rw [Finset.sum_comm]
  simp only [mul_comm]

/-! ### Label-independent basis substitutions -/

open Classical in
/-- The basis vector at a selected position at every label; zero elsewhere (not used). Source:
Theorem 5.2, `04-compression.tex`, lines 351–417. -/
noncomputable def coordinateBasisVectors (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (u : SelectedSourceCoordinates w S) (e : w.sourceLocations) (_ξ : w.branchLabels e.1) :
    EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e) :=
  if he : e ∈ S then EuclideanSpace.single (u ⟨e, he⟩) 1 else 0

/-- A branch of the partial expansion with the basis vectors at the selected positions and the
vectors of the gates elsewhere, read back on the parties. Source: Theorem 5.2,
`04-compression.tex`, lines 351–417. -/
noncomputable def partialCoordinateBasisMatrix (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations) (u : SelectedSourceCoordinates w S) (ξ : Choices A w) :
    Matrix (Config Y) (Config X) ℂ :=
  reindex (blockConfigEquiv (affectedOwner A) Y) (blockConfigEquiv (affectedOwner A) X)
    (Word.op (partialWithSources A w (selectedSourceVectors w S (coordinateBasisVectors w S u)) ξ))

end SourceCircuit

end QuantumCircuit.Party
