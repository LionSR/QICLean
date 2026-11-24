/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceReplacement.Density

/-!
# Source columns of prepared words

On a pure input `ψ`, the matrix of a word `v` applied after prepared slots has the columns
`v (|a⟩ ⊗ ψ)` indexed by the pairs `a` of basis elements of the slots
(`Word.pureSourceMatrix`); every density coefficient of basis vectors is the outer product of two
such columns, so a source contraction with matrices `T i` is the product of the ket columns, the
Kronecker product `⊗_i T i` and the conjugated bra columns
(`Word.sourceContraction_preparedDensityCoefficient_pure_eq_mul`). For the partial expansion of a
source circuit along all parties on the product input `⊗_p φ_p`, the columns are those of the
prepared source word (`SourceCircuit.partialSourceGlobalMatrix`), whose operator is the product
over the parties of their local operations (`partialSourceGlobalMatrix_eq_piKronecker`); a word
without sources inserted between ket and bra columns factors in the same way. The
source-replaced density on the product input, and its physical partial trace, are the weighted
sums of the mixed products of these columns; a change of the physical and discarded coordinates
of the readout conjugates the physical partial trace.

## Main definitions

* `QuantumCircuit.Party.Word.pureSourceMatrix`.
* `QuantumCircuit.Party.SourceInventory.slotFreshEquiv`,
  `QuantumCircuit.Party.SourceCircuit.allSourceColumnEquiv`,
  `QuantumCircuit.Party.SourceCircuit.partialSourceGlobalMatrix`.

## Main results

* `QuantumCircuit.Party.Word.preparedDensityCoefficient_pure_eq_vecMulVec`,
  `QuantumCircuit.Party.Word.sourceContraction_preparedDensityCoefficient_pure_eq_mul`.
* `QuantumCircuit.Party.SourceCircuit.partialSourceGlobalMatrix_eq_piKronecker`,
  `QuantumCircuit.Party.SourceCircuit.partialSourceGlobalMatrix_mixed_word`.
* `QuantumCircuit.Party.SourceCircuit.sourceContraction_preparedDensityCoefficient_pure_eq_mul`,
  `QuantumCircuit.Party.SourceCircuit.sourceReplacedDensity_pure_eq_sum_actualColumns`,
  `QuantumCircuit.Party.SourceCircuit.physicalSourceReplacedDensity_pure_eq_sum_actualColumnTraces`,
  `QuantumCircuit.Party.SourceCircuit.partialTraceRight_kronecker_mul_actualColumns`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 137–139, 246–267, 279–355, 409–434 and 565–588.

Adapted from TNLean, `TNLean/Lattice/Compression/SourceColumnContraction.lean`,
`PureSourceMatrix.lean`, `PurePreparedContraction.lean`, `ActualSourceColumnCoordinates.lean`,
`ActualPartySourceMatrix.lean`, `ActualMixedSourceMatrix.lean`, `ActualPureSourceMatrix.lean`,
`ActualPureSourceReplacement.lean` and `ActualPurePhysicalSourceReplacement.lean` (Apache-2.0).
Changes: the coordinates of a party are its configurations, so no change of basis between source
and party coordinates remains; the literal product source matrix is `Matrix.piKronecker`.
-/

open Matrix ManyBody
open scoped ComplexConjugate Kronecker

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Columns of a word applied after prepared slots -/

namespace Word

variable [Fintype P] (R : SourceInventory P) (B : SourceInventory.SlotBases R.length)
  (X : P → Type) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] {Y : P → Type}

/-- The source-to-output matrix on the input `ψ`: its column at the basis elements `a` of the
slots is the output of the word on `|a⟩ ⊗ ψ`. Source: `04-compression.tex`, lines 137–139 and
409–434. -/
noncomputable def pureSourceMatrix (v : Word (SourceInventory.slotSystem R B X) Y)
    (ψ : EuclideanSpace ℂ (Config X)) : Matrix (Config Y) (∀ i, B.left i × B.right i) ℂ :=
  v.op * prepMatrix ((SourceInventory.slotColumnEquiv R B X).trans (Equiv.prodComm _ _)) ψ

omit [DecidableEq P] [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- The slot vector of basis vectors is a basis vector. -/
private theorem slotVector_single (a : ∀ i, B.left i × B.right i) :
    SourceInventory.slotVector R B (fun i ↦ EuclideanSpace.vecKron
      (EuclideanSpace.single (a i).1 (1 : ℂ)) (EuclideanSpace.single (a i).2 1)) =
      EuclideanSpace.single a 1 := by
  ext f
  rw [SourceInventory.slotVector_apply, PiLp.single_apply]
  split_ifs with h
  · subst h
    simp [EuclideanSpace.vecKron]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    by_cases h₁ : (f i).1 = (a i).1
    · have h₂ : (f i).2 ≠ (a i).2 := fun h₂ ↦ hi (Prod.ext h₁ h₂)
      simp [EuclideanSpace.vecKron, h₂]
    · simp [EuclideanSpace.vecKron, h₁]

/-- The prepared matrix of the basis vectors `a` applied to `ψ` is the column of `a`. -/
private theorem preparedMatrix_single_mulVec (v : Word (SourceInventory.slotSystem R B X) Y)
    (ψ : EuclideanSpace ℂ (Config X)) (a : ∀ i, B.left i × B.right i) :
    v.preparedMatrix R B (fun i ↦ EuclideanSpace.vecKron (EuclideanSpace.single (a i).1 1)
        (EuclideanSpace.single (a i).2 1)) X *ᵥ WithLp.ofLp ψ =
      fun r ↦ v.pureSourceMatrix R B X ψ r a := by
  rw [preparedMatrix, ← mulVec_mulVec, SourceInventory.op_prepareSlots, slotVector_single]
  ext r
  simp only [pureSourceMatrix, mulVec, dotProduct, mul_apply]
  refine Finset.sum_congr rfl fun z _ ↦ congrArg (_ * ·) ?_
  simp only [prepMatrix_apply, PiLp.single_apply, Equiv.trans_apply, Equiv.prodComm_apply,
    Prod.fst_swap, Prod.snd_swap, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  by_cases h : (SourceInventory.slotColumnEquiv R B X z).1 = a <;> simp [h]

/-- **A density coefficient of basis vectors on a pure input is the outer product of two
columns.** Source: `04-compression.tex`, lines 279–355 and 409–434. -/
theorem preparedDensityCoefficient_pure_eq_vecMulVec
    (v v' : Word (SourceInventory.slotSystem R B X) Y) (ψ : EuclideanSpace ℂ (Config X))
    (x y : ∀ i, B.left i × B.right i) :
    v.preparedDensityCoefficient R B X (fun _ a ↦ EuclideanSpace.single a 1)
        (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
        (fun _ a ↦ EuclideanSpace.single a 1) v' (euclideanOuterProduct ψ ψ) x y =
      vecMulVec (fun r ↦ v.pureSourceMatrix R B X ψ r x)
        (fun s ↦ conj (v'.pureSourceMatrix R B X ψ s y)) := by
  rw [preparedDensityCoefficient, euclideanOuterProduct, mul_vecMulVec, vecMulVec_mul,
    ← star_mulVec, preparedMatrix_single_mulVec, preparedMatrix_single_mulVec]
  rfl

/-- **On a pure input, the source contraction is the Kronecker product of the source matrices
between the ket and bra source-to-output matrices.** The input need not be normalized and the
two words may differ. Source: `04-compression.tex`, lines 279–355 and 409–434. -/
theorem sourceContraction_preparedDensityCoefficient_pure_eq_mul
    (v v' : Word (SourceInventory.slotSystem R B X) Y) (ψ : EuclideanSpace ℂ (Config X))
    (T : ∀ i, Matrix (B.left i × B.right i) (B.left i × B.right i) ℂ) :
    sourceContraction
        (fun x ↦ v.preparedDensityCoefficient R B X (fun _ a ↦ EuclideanSpace.single a 1)
          (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
          (fun _ a ↦ EuclideanSpace.single a 1) v' (euclideanOuterProduct ψ ψ)
          (fun i ↦ (x i).1) (fun i ↦ (x i).2)) T =
      v.pureSourceMatrix R B X ψ * piKronecker T * (v'.pureSourceMatrix R B X ψ)ᴴ := by
  simp only [preparedDensityCoefficient_pure_eq_vecMulVec]
  exact sourceContraction_vecMulVec_eq_mul_piKronecker _ _ T

end Word

/-! ### The prepared source word along all parties -/

namespace SourceInventory

/-- The fresh configurations of slots are a pair of basis elements at every slot. -/
def slotFreshEquiv : (R : SourceInventory P) → (B : SlotBases R.length) →
    slotFresh R B ≃ ∀ i, B.left i × B.right i
  | [], B =>
    haveI : IsEmpty (Fin ([] : SourceInventory P).length) := Fin.isEmpty'
    (Equiv.ofUnique Unit (∀ i, B.left i × B.right i) :)
  | _ :: R, B => ((Equiv.refl _).prodCongr (slotFreshEquiv R B.tail)).trans
      (Fin.consEquiv fun i ↦ B.left i × B.right i)

/-- The source coordinates of a configuration of a slot system are its fresh configuration. -/
theorem slotColumnEquiv_apply (R : SourceInventory P) (B : SlotBases R.length) (Z : P → Type)
    (z : Config (slotSystem R B Z)) :
    slotColumnEquiv R B Z z =
      (slotFreshEquiv R B (slotConfigEquiv R B Z z).1, (slotConfigEquiv R B Z z).2) := by
  induction R with
  | nil =>
    have : IsEmpty (Fin ([] : SourceInventory P).length) := Fin.isEmpty'
    exact Prod.ext (Subsingleton.elim _ _) rfl
  | cons r R ih =>
    rw [slotColumnEquiv_cons_apply, ih]
    rfl

end SourceInventory

namespace SourceCircuit

variable [Fintype P] {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The configurations of the input of the prepared source word are the basis elements of its
slots. Source: `04-compression.tex`, lines 246–267 and 409–434. -/
noncomputable def allSourceColumnEquiv (w : SourceCircuit X Y) :
    (∀ i, (partialSlotBases (fun _ ↦ true) w).left i × (partialSlotBases (fun _ ↦ true) w).right i)
      ≃ Config (allSourceSystem w) :=
  ((SourceInventory.slotColumnEquiv _ _ _).trans (Equiv.prodUnique _ _)).symm

/-- **The source-to-output matrix of a branch of the expansion along all parties on the product
input**: the columns of the prepared source word at the basis elements of the slots. Source:
`04-compression.tex`, lines 137–139 and 409–434. -/
noncomputable def partialSourceGlobalMatrix (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ : Choices (fun _ ↦ true) w) :
    Matrix (Config (blockSystem (affectedOwner fun _ ↦ true) Y))
      (∀ i, (partialSlotBases (fun _ ↦ true) w).left i ×
        (partialSlotBases (fun _ ↦ true) w).right i) ℂ :=
  (partialSourceWord w φ ξ).op.submatrix id (allSourceColumnEquiv w)

/-- A column of the source-to-output matrix is the column of the operator of the prepared source
word at the corresponding input configuration. Source: `04-compression.tex`, lines 137–139,
409–434 and 565–588. -/
@[simp] theorem partialSourceGlobalMatrix_apply (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ : Choices (fun _ ↦ true) w)
    (r : Config (blockSystem (affectedOwner fun _ ↦ true) Y))
    (a : ∀ i, (partialSlotBases (fun _ ↦ true) w).left i ×
      (partialSlotBases (fun _ ↦ true) w).right i) :
    partialSourceGlobalMatrix w φ ξ r a =
      (partialSourceWord w φ ξ).op r (allSourceColumnEquiv w a) :=
  rfl

/-- **The columns are the product over the parties of the local operations of the prepared
source word**, including the exterior party. Source: `04-compression.tex`, lines 137–139,
409–434 and 565–588. -/
theorem partialSourceGlobalMatrix_eq_piKronecker (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ : Choices (fun _ ↦ true) w) :
    partialSourceGlobalMatrix w φ ξ =
      (piKronecker (PartyCircuit.partyOp (partialSourceWord w φ ξ))).submatrix id
        (allSourceColumnEquiv w) := by
  rw [partialSourceGlobalMatrix, Word.op, PartyCircuit.op_eq_piKronecker_partyOp SourceGate.ev _
    ((Word.isLocal_iff_sources_eq_nil _).mpr (sources_partialSourceWord w φ ξ))]

/-- **A word without sources between the ket and bra columns factors over the parties** into
the products of the local operations. Source: `04-compression.tex`, lines 279–355, 409–434 and
565–588. -/
theorem partialSourceGlobalMatrix_mixed_word (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ ζ : Choices (fun _ ↦ true) w)
    (u : Word (allSourceSystem w) (allSourceSystem w)) (hu : u.sources = []) :
    partialSourceGlobalMatrix w φ ξ * u.op.submatrix (allSourceColumnEquiv w)
        (allSourceColumnEquiv w) * (partialSourceGlobalMatrix w φ ζ)ᴴ =
      piKronecker fun q ↦ PartyCircuit.partyOp (partialSourceWord w φ ξ) q *
        PartyCircuit.partyOp u q * (PartyCircuit.partyOp (partialSourceWord w φ ζ) q)ᴴ := by
  rw [partialSourceGlobalMatrix, partialSourceGlobalMatrix, conjTranspose_submatrix,
    submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id, Word.op, Word.op, Word.op,
    PartyCircuit.op_eq_piKronecker_partyOp SourceGate.ev _
      ((Word.isLocal_iff_sources_eq_nil _).mpr (sources_partialSourceWord w φ ξ)),
    PartyCircuit.op_eq_piKronecker_partyOp SourceGate.ev _
      ((Word.isLocal_iff_sources_eq_nil _).mpr (sources_partialSourceWord w φ ζ)),
    PartyCircuit.op_eq_piKronecker_partyOp SourceGate.ev _
      ((Word.isLocal_iff_sources_eq_nil _).mpr hu),
    conjTranspose_piKronecker, piKronecker_mul, piKronecker_mul]

/-- The product input read on the blocks of the expansion along all parties. Source:
`04-compression.tex`, lines 137–139. -/
noncomputable def blockProductVector (φ : ∀ p, EuclideanSpace ℂ (X p)) :
    EuclideanSpace ℂ (Config (blockSystem (affectedOwner fun _ ↦ true) X)) :=
  WithLp.toLp 2 fun y ↦ productVector (fun p x ↦ φ p x)
    (blockConfigEquiv (affectedOwner fun _ ↦ true) X y)

/-- The prepared product input, read on the blocks, is the product input read on the blocks. -/
private theorem op_coarsen_prepareProduct_apply (φ : ∀ p, EuclideanSpace ℂ (X p))
    (y : Config (blockSystem (affectedOwner fun _ ↦ true) X))
    (u : Config (blockSystem (affectedOwner fun _ ↦ true) fun _ ↦ Unit)) :
    Word.op (Word.coarsen (affectedOwner fun _ ↦ true) (Word.prepareProduct φ)) y u =
      blockProductVector φ y := by
  rw [Word.op_coarsen, reindex_apply, submatrix_apply]
  have h := congrFun (Word.op_prepareProduct_mulVec φ)
    (blockConfigEquiv (affectedOwner fun _ ↦ true) X y)
  simp only [mulVec, dotProduct, mul_one, Fintype.sum_unique] at h
  rw [Subsingleton.elim ((blockConfigEquiv (affectedOwner fun _ ↦ true) fun _ ↦ Unit).symm.symm u)
    default]
  exact h

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)] in
/-- The configuration of the input of the prepared source word at a column. -/
private theorem slotConfigEquiv_allSourceColumnEquiv (w : SourceCircuit X Y)
    (a : ∀ i, (partialSlotBases (fun _ ↦ true) w).left i ×
      (partialSlotBases (fun _ ↦ true) w).right i) :
    (SourceInventory.slotConfigEquiv _ _ _ (allSourceColumnEquiv w a)).1 =
      (SourceInventory.slotFreshEquiv _ _).symm a := by
  have h0 : SourceInventory.slotColumnEquiv _ _ _ (allSourceColumnEquiv w a) = (a, default) := by
    simp only [allSourceColumnEquiv, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
    rfl
  rw [SourceInventory.slotColumnEquiv_apply] at h0
  exact (Equiv.eq_symm_apply _).mpr (congrArg Prod.fst h0)

/-- The source columns of a residual on the product input are the columns of the prepared
source word. -/
private theorem pureSourceMatrix_partialResidual (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ : Choices (fun _ ↦ true) w) :
    (partialResidual (fun _ ↦ true) w ξ).pureSourceMatrix (partialSlots (fun _ ↦ true) w)
        (partialSlotBases (fun _ ↦ true) w) (blockSystem (affectedOwner fun _ ↦ true) X)
        (blockProductVector φ) =
      partialSourceGlobalMatrix w φ ξ := by
  rw [partialSourceGlobalMatrix, op_partialSourceWord, Word.pureSourceMatrix]
  ext r a
  simp only [submatrix_apply, id_eq, mul_apply]
  refine Finset.sum_congr rfl fun z _ ↦ congrArg (_ * ·) ?_
  simp only [prepMatrix_apply, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap,
    Prod.snd_swap, reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply,
    op_coarsen_prepareProduct_apply, slotConfigEquiv_allSourceColumnEquiv,
    SourceInventory.slotColumnEquiv_apply, Matrix.one_apply, Equiv.eq_symm_apply]
  split_ifs <;> simp

/-- **On the product input, the source contraction of the residuals is the Kronecker product of
the source matrices between the ket and bra columns of the prepared source words.** Source:
`04-compression.tex`, lines 137–139, 279–355 and 409–434. -/
theorem sourceContraction_preparedDensityCoefficient_pure_eq_mul (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ ζ : Choices (fun _ ↦ true) w)
    (T : ∀ i, Matrix ((partialSlotBases (fun _ ↦ true) w).left i ×
      (partialSlotBases (fun _ ↦ true) w).right i) ((partialSlotBases (fun _ ↦ true) w).left i ×
      (partialSlotBases (fun _ ↦ true) w).right i) ℂ) :
    sourceContraction
        (fun x ↦ (partialResidual (fun _ ↦ true) w ξ).preparedDensityCoefficient
          (partialSlots (fun _ ↦ true) w) (partialSlotBases (fun _ ↦ true) w)
          (blockSystem (affectedOwner fun _ ↦ true) X) (fun _ a ↦ EuclideanSpace.single a 1)
          (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
          (fun _ a ↦ EuclideanSpace.single a 1) (partialResidual (fun _ ↦ true) w ζ)
          (euclideanOuterProduct (blockProductVector φ) (blockProductVector φ))
          (fun i ↦ (x i).1) (fun i ↦ (x i).2)) T =
      partialSourceGlobalMatrix w φ ξ * piKronecker T * (partialSourceGlobalMatrix w φ ζ)ᴴ := by
  rw [Word.sourceContraction_preparedDensityCoefficient_pure_eq_mul,
    pureSourceMatrix_partialResidual, pureSourceMatrix_partialResidual]

/-- **The source-replaced density on the product input is the weighted sum of the mixed
products of the columns of the prepared source words**, with the original coefficients, the
source positions and independent ket and bra choices; the replacement matrices are arbitrary.
Source: Theorem 5.2, `04-compression.tex`, lines 279–355, 409–434 and 565–588. -/
theorem sourceReplacedDensity_pure_eq_sum_actualColumns (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p))
    (T : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ) :
    sourceReplacedDensity w T (euclideanOuterProduct (WithLp.toLp 2 (productVector fun p x ↦ φ p x))
        (WithLp.toLp 2 (productVector fun p x ↦ φ p x))) =
      ∑ ξ, ∑ ζ, (coefficient (fun _ ↦ true) w ξ * conj (coefficient (fun _ ↦ true) w ζ)) •
        ((partialSourceGlobalMatrix w φ ξ).submatrix
            (blockConfigEquiv (affectedOwner fun _ ↦ true) Y).symm id *
          (piKronecker (fun i ↦ T (partialSlotEquiv (fun _ ↦ true) w i).1
            (partialSlotChoice (fun _ ↦ true) w ξ i) (partialSlotChoice (fun _ ↦ true) w ζ i)) :
            Matrix (∀ i, (partialSlotBases (fun _ ↦ true) w).left i ×
              (partialSlotBases (fun _ ↦ true) w).right i)
              (∀ i, (partialSlotBases (fun _ ↦ true) w).left i ×
              (partialSlotBases (fun _ ↦ true) w).right i) ℂ) *
          ((partialSourceGlobalMatrix w φ ζ).submatrix
            (blockConfigEquiv (affectedOwner fun _ ↦ true) Y).symm id)ᴴ) := by
  have hin : reindex (blockConfigEquiv (affectedOwner fun _ ↦ true) X).symm
      (blockConfigEquiv (affectedOwner fun _ ↦ true) X).symm
      (euclideanOuterProduct (WithLp.toLp 2 (productVector fun p x ↦ φ p x))
        (WithLp.toLp 2 (productVector fun p x ↦ φ p x))) =
      euclideanOuterProduct (blockProductVector φ) (blockProductVector φ) := by
    ext y x
    rfl
  rw [sourceReplacedDensity_eq_sum_sourceContraction, hin]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ congrArg (_ • ·) ?_
  rw [sourceContraction_preparedDensityCoefficient_pure_eq_mul w φ ξ ζ
    (fun i ↦ T (partialSlotEquiv (fun _ ↦ true) w i).1 (partialSlotChoice (fun _ ↦ true) w ξ i)
      (partialSlotChoice (fun _ ↦ true) w ζ i)), reindex_apply,
    conjTranspose_submatrix, ← submatrix_mul_equiv (e₂ := Equiv.refl _), ← submatrix_mul_equiv
      (e₂ := Equiv.refl _)]
  rfl

/-- **The physical source-replaced density on the product input is the weighted sum of the
partial traces of the mixed column products read through `K`.** Source: Theorem 5.2,
`04-compression.tex`, lines 338–383 and 565–588. -/
theorem physicalSourceReplacedDensity_pure_eq_sum_actualColumnTraces {Phys Env : Type}
    [Fintype Env] (w : SourceCircuit X Y) (φ : ∀ p, EuclideanSpace ℂ (X p))
    (T : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (K : Matrix (Phys × Env) (Config Y) ℂ) :
    physicalSourceReplacedDensity w T K
        (euclideanOuterProduct (WithLp.toLp 2 (productVector fun p x ↦ φ p x))
          (WithLp.toLp 2 (productVector fun p x ↦ φ p x))) =
      ∑ ξ, ∑ ζ, (coefficient (fun _ ↦ true) w ξ * conj (coefficient (fun _ ↦ true) w ζ)) •
        partialTraceRight
          (K * (partialSourceGlobalMatrix w φ ξ).submatrix
              (blockConfigEquiv (affectedOwner fun _ ↦ true) Y).symm id *
            (piKronecker (fun i ↦ T (partialSlotEquiv (fun _ ↦ true) w i).1
              (partialSlotChoice (fun _ ↦ true) w ξ i) (partialSlotChoice (fun _ ↦ true) w ζ i)) :
              Matrix (∀ i, (partialSlotBases (fun _ ↦ true) w).left i ×
                (partialSlotBases (fun _ ↦ true) w).right i)
                (∀ i, (partialSlotBases (fun _ ↦ true) w).left i ×
                (partialSlotBases (fun _ ↦ true) w).right i) ℂ) *
            (K * (partialSourceGlobalMatrix w φ ζ).submatrix
              (blockConfigEquiv (affectedOwner fun _ ↦ true) Y).symm id)ᴴ) := by
  rw [physicalSourceReplacedDensity, sourceReplacedDensity_pure_eq_sum_actualColumns]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, conjTranspose_mul,
    Matrix.mul_assoc]
  exact (map_sum (partialTraceRightLM (α := Phys) (β := Env)) _ _).trans
    (Finset.sum_congr rfl fun ξ _ ↦ (map_sum partialTraceRightLM _ _).trans
      (Finset.sum_congr rfl fun ζ _ ↦ LinearMap.map_smul _ _ _))

/-- **Changing the physical and discarded coordinates of the mixed column products**: reading the
output through `(U ⊗ V) * K` for a matrix `U` of the physical factor and an isometry `V` of the
discarded factor (possibly onto a larger index type) conjugates the physical partial trace by
`U`, for every middle matrix `M`; for a unitary or permutation `U` this is the independence of
the reduced mixed column operator from the coordinates of both factors. Source: Theorem 5.2,
`04-compression.tex`, lines 279–355, 409–434 and 565–588. -/
theorem partialTraceRight_kronecker_mul_actualColumns {Phys Env Phys' Env' : Type}
    [Fintype Phys] [Fintype Env] [DecidableEq Env] [Fintype Env'] (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ ζ : Choices (fun _ ↦ true) w)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (U : Matrix Phys' Phys ℂ) (V : Matrix Env' Env ℂ)
    (hV : Vᴴ * V = 1)
    (M : Matrix (∀ i, (partialSlotBases (fun _ ↦ true) w).left i ×
        (partialSlotBases (fun _ ↦ true) w).right i)
      (∀ i, (partialSlotBases (fun _ ↦ true) w).left i ×
        (partialSlotBases (fun _ ↦ true) w).right i) ℂ) :
    partialTraceRight ((U ⊗ₖ V) * K * (partialSourceGlobalMatrix w φ ξ).submatrix
          (blockConfigEquiv (affectedOwner fun _ ↦ true) Y).symm id * M *
        ((U ⊗ₖ V) * K * (partialSourceGlobalMatrix w φ ζ).submatrix
          (blockConfigEquiv (affectedOwner fun _ ↦ true) Y).symm id)ᴴ) =
      U * partialTraceRight (K * (partialSourceGlobalMatrix w φ ξ).submatrix
          (blockConfigEquiv (affectedOwner fun _ ↦ true) Y).symm id * M *
        (K * (partialSourceGlobalMatrix w φ ζ).submatrix
          (blockConfigEquiv (affectedOwner fun _ ↦ true) Y).symm id)ᴴ) * Uᴴ := by
  rw [← partialTraceRight_kronecker_conj_of_right_isometry U V hV]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

end SourceCircuit

end QuantumCircuit.Party
