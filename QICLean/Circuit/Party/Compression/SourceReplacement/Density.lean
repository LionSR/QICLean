/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceReplacement.CorrectedContraction
import QICLean.Algebra.PartialTrace

/-!
# Source-replaced densities of a source circuit

Replacing the rank-one source operators of the partial expansion of a source circuit along all
parties by arbitrary matrices `T e ξ ζ`, indexed by the source positions and the ket and bra
labels of their gates, defines a density matrix directly through the residuals of the branches
(`SourceCircuit.sourceReplacedDensity`). The exact rank-one operators
(`SourceCircuit.exactSourceMatrix`) give the density of the circuit back; replacing the
operators on a set of positions gives the corrected term of that set; and the difference between
corrected and exact operators is the sum of the corrected terms of the nonempty sets of positions
(`sourceReplacedDensity_sub_exact`, `eq:compression-subset-expansion`). Reading the output through
a readout matrix `K` into a physical and a discarded factor and tracing the discarded factor, the
identity descends to the physical densities, without a dimension factor of the discarded factor
(`physicalSourceReplacedDensity_sub_exact`,
`rectangularTraceNorm_physicalSourceReplacedDensity_sub_le`).
The identities hold for every input matrix and every readout; a reordering of the physical and
discarded coordinates, or any isometric change of them, does not change the trace norm of a
physical corrected term.

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.exactSourceMatrix`,
  `QuantumCircuit.Party.SourceCircuit.sourceReplacedDensity`.
* `QuantumCircuit.Party.SourceCircuit.physicalDensity`,
  `QuantumCircuit.Party.SourceCircuit.physicalCorrectedSourceTerm`,
  `QuantumCircuit.Party.SourceCircuit.physicalSourceReplacedDensity`.

## Main results

* `QuantumCircuit.Party.SourceCircuit.sourceReplacedDensity_exact`,
  `QuantumCircuit.Party.SourceCircuit.sourceReplacedDensity_piecewise`,
  `QuantumCircuit.Party.SourceCircuit.sourceReplacedDensity_sub_exact`.
* `QuantumCircuit.Party.SourceCircuit.physicalSourceReplacedDensity_sub_exact`,
  `QuantumCircuit.Party.SourceCircuit.rectangularTraceNorm_physicalSourceReplacedDensity_sub_le`.
* `QuantumCircuit.Party.SourceCircuit.physicalDensity_pure_input`,
  `QuantumCircuit.Party.SourceCircuit.sourceBasisMatrix_mul_euclideanOuterProduct`,
  `SourceCircuit.rectangularTraceNorm_physicalCorrectedSourceTerm_kronecker_isometry_mul`,
  `QuantumCircuit.Party.SourceCircuit.rectangularTraceNorm_physicalCorrectedSourceTerm_reindex`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 4–30, 218–227 and 338–383 (equations `eq:compression-subset-expansion`,
  `eq:compression-total-error`).

Adapted from TNLean, `TNLean/Lattice/Compression/SourceCompressedDensity.lean`,
`TNLean/Lattice/Compression/SourcePhysicalDensity.lean`,
`TNLean/Lattice/Compression/PhysicalDensityPureInput.lean` and
`TNLean/Lattice/Compression/SourcePhysicalBasisInvariance.lean` (Apache-2.0). Changes: the input
and output coordinates are configurations; the physical and discarded memories are read through
a readout matrix `K : Matrix (Phys × Env) (Config Y) ℂ` instead of orthonormal bases of two
register lists.
-/

open Matrix ManyBody
open scoped ComplexConjugate Kronecker

namespace QuantumCircuit.Party

namespace SourceCircuit

variable {P : Type} [DecidableEq P] [Fintype P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)]

/-- The exact rank-one source operator at a position and a pair of labels of its gate. Source:
Theorem 5.2, `04-compression.tex`, lines 279–355. -/
noncomputable def exactSourceMatrix (w : SourceCircuit X Y) (e : w.sourceLocations)
    (ξ ζ : w.branchLabels e.1) :
    Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ :=
  vecMulVec (fun a ↦ w.sourceVectorAt e ξ a) (fun a ↦ conj (w.sourceVectorAt e ζ a))

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- **The source-replaced density**: the source operators `T e ξ ζ` substituted in the partial
expansion along all parties, read on the parties. It is defined independently of the
corrected-subset identity. Source: Theorem 5.2, `04-compression.tex`, lines 279–355. -/
noncomputable def sourceReplacedDensity (w : SourceCircuit X Y)
    (T : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (ρ : Matrix (Config X) (Config X) ℂ) : Matrix (Config Y) (Config Y) ℂ :=
  reindex (blockConfigEquiv (affectedOwner fun _ ↦ true) Y)
    (blockConfigEquiv (affectedOwner fun _ ↦ true) Y)
    (Word.sourceOperatorDensity (partialSlots (fun _ ↦ true) w)
      (partialSlotBases (fun _ ↦ true) w) (blockSystem (affectedOwner fun _ ↦ true) X)
      (K := fun _ i ↦ (partialSlotBases (fun _ ↦ true) w).left i)
      (L := fun _ i ↦ (partialSlotBases (fun _ ↦ true) w).right i)
      (fun _ _ a ↦ EuclideanSpace.single a 1) (fun _ _ a ↦ EuclideanSpace.single a 1)
      (coefficient (fun _ ↦ true) w) (partialResidual (fun _ ↦ true) w)
      (reindex (blockConfigEquiv (affectedOwner fun _ ↦ true) X).symm
        (blockConfigEquiv (affectedOwner fun _ ↦ true) X).symm ρ)
      (fun ξ ζ i ↦ T (partialSlotEquiv (fun _ ↦ true) w i).1
        (partialSlotChoice (fun _ ↦ true) w ξ i) (partialSlotChoice (fun _ ↦ true) w ζ i)))

/-- The source-replaced density is the weighted sum over pairs of branches of the source
contractions of the residuals, read on the parties. Source: Theorem 5.2, `04-compression.tex`,
lines 279–355 and 409–434. -/
theorem sourceReplacedDensity_eq_sum_sourceContraction (w : SourceCircuit X Y)
    (T : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    sourceReplacedDensity w T ρ =
      ∑ ξ, ∑ ζ, (coefficient (fun _ ↦ true) w ξ * conj (coefficient (fun _ ↦ true) w ζ)) •
        reindex (blockConfigEquiv (affectedOwner fun _ ↦ true) Y)
          (blockConfigEquiv (affectedOwner fun _ ↦ true) Y)
          (sourceContraction
            (fun z ↦ (partialResidual (fun _ ↦ true) w ξ).preparedDensityCoefficient
              (partialSlots (fun _ ↦ true) w) (partialSlotBases (fun _ ↦ true) w)
              (blockSystem (affectedOwner fun _ ↦ true) X)
              (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
              (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
              (partialResidual (fun _ ↦ true) w ζ)
              (reindex (blockConfigEquiv (affectedOwner fun _ ↦ true) X).symm
                (blockConfigEquiv (affectedOwner fun _ ↦ true) X).symm ρ)
              (fun i ↦ (z i).1) (fun i ↦ (z i).2))
            (fun i ↦ T (partialSlotEquiv (fun _ ↦ true) w i).1
              (partialSlotChoice (fun _ ↦ true) w ξ i)
              (partialSlotChoice (fun _ ↦ true) w ζ i))) := by
  unfold sourceReplacedDensity Word.sourceOperatorDensity
  rw [← coe_reindexLinearEquiv ℂ ℂ, map_sum]
  simp only [map_sum, LinearEquiv.map_smul]

/-- **Exact source operators give the density of the circuit back.** Source: Theorem 5.2,
`04-compression.tex`, lines 338–355. -/
theorem sourceReplacedDensity_exact (w : SourceCircuit X Y) (ρ : Matrix (Config X) (Config X) ℂ) :
    sourceReplacedDensity w (exactSourceMatrix w) ρ = w.op * ρ * w.opᴴ := by
  classical
  have h := correctedSourceTerm_eq_sourceContraction (fun _ ↦ true) w ∅
    (fun _ _ ↦ Or.inl rfl) (exactSourceMatrix w) ρ
  rw [correctedSourceTerm_empty] at h
  have h0 : selectedPartialSlots (fun _ ↦ true) w ∅ = ∅ := by
    ext i
    simp [mem_selectedPartialSlots]
  simp only [h0, Finset.notMem_empty] at h
  rw [h, sourceReplacedDensity_eq_sum_sourceContraction]
  rfl

open Classical in
/-- **Replacing the operators on a set of positions gives the corrected term of that set**, the
exact operators elsewhere. Source: Theorem 5.2, `04-compression.tex`, lines 338–383. -/
theorem sourceReplacedDensity_piecewise (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    sourceReplacedDensity w (S.piecewise E (exactSourceMatrix w)) ρ =
      correctedSourceTerm w S E ρ := by
  classical
  rw [correctedSourceTerm_eq_sourceContraction (fun _ ↦ true) w S (fun _ _ ↦ Or.inl rfl) E ρ,
    sourceReplacedDensity_eq_sum_sourceContraction]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ ?_
  congr 4
  funext i
  by_cases hi : (partialSlotEquiv (fun _ ↦ true) w i).1 ∈ S
  · have h' := (mem_selectedPartialSlots _ w S i).mpr hi
    simp [h', Finset.piecewise_eq_of_mem _ _ _ hi]
  · have h' := mt (mem_selectedPartialSlots _ w S i).mp hi
    simp [h', Finset.piecewise_eq_of_notMem _ _ _ hi, exactSourceMatrix]
    rfl

omit [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)] in
/-- The slots of the positions of a set of slots, enumerated along all positions, are that set.
-/
private theorem selectedPartialSlots_map_allSourceSlotEquiv (w : SourceCircuit X Y)
    (S : Finset (Fin (partialSlots (fun _ ↦ true) w).length)) :
    selectedPartialSlots (fun _ ↦ true) w (S.map (allSourceSlotEquiv w).toEmbedding) = S := by
  ext i
  rw [mem_selectedPartialSlots, ← allSourceSlotEquiv_apply, Finset.mem_map_equiv,
    Equiv.symm_apply_apply]

open Classical in
/-- **The corrected-subset identity**: the density with corrected source operators differs from
the density of the circuit by the sum of the corrected terms of the nonempty sets of positions;
the branch coefficients and the ket and bra labels are kept. Source: Theorem 5.2,
`eq:compression-subset-expansion`, `04-compression.tex`, lines 338–383. -/
theorem sourceReplacedDensity_sub_exact (w : SourceCircuit X Y)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    sourceReplacedDensity w (E + exactSourceMatrix w) ρ - w.op * ρ * w.opᴴ =
      ∑ S ∈ (Finset.univ : Finset (Finset w.sourceLocations)).erase ∅,
        correctedSourceTerm w S E ρ := by
  rw [← sourceReplacedDensity_exact w ρ, sourceReplacedDensity, sourceReplacedDensity,
    ← coe_reindexLinearEquiv ℂ ℂ, ← map_sub]
  erw [Word.sourceOperatorDensity_sub]
  rw [map_sum, ← sum_nonempty_allSourceSlots w (fun S ↦ correctedSourceTerm w S E ρ)]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [← sourceReplacedDensity_piecewise, sourceReplacedDensity, coe_reindexLinearEquiv]
  congr 2
  funext ξ ζ i
  by_cases hi : i ∈ S <;> simp [Finset.piecewise, hi, ← allSourceSlotEquiv_apply] <;> rfl

/-! ### Physical densities -/

variable {Phys Env : Type} [Fintype Env]

/-- The physical density of a source circuit on the input matrix `ρ`: its output read through
`K` into a physical and a discarded factor, the discarded factor traced. For a circuit satisfying
the source's conditions and a normalized pure input, it is the density of its physical output.
Source: Theorem 5.2, `04-compression.tex`, lines 4–19 and 23–30. -/
noncomputable def physicalDensity (w : SourceCircuit X Y) (K : Matrix (Phys × Env) (Config Y) ℂ)
    (ρ : Matrix (Config X) (Config X) ℂ) : Matrix Phys Phys ℂ :=
  partialTraceRight (K * w.op * ρ * (K * w.op)ᴴ)

/-- The physical corrected term: the corrected term read through `K`, the discarded factor
traced, with its positions and labels unchanged. Source: Theorem 5.2, `04-compression.tex`,
lines 338–383. -/
noncomputable def physicalCorrectedSourceTerm (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (ρ : Matrix (Config X) (Config X) ℂ) :
    Matrix Phys Phys ℂ :=
  partialTraceRight (K * correctedSourceTerm w S E ρ * Kᴴ)

/-- The physical source-replaced density, defined before and independently of the
corrected-subset identity. Source: Theorem 5.2, `04-compression.tex`, lines 338–383. -/
noncomputable def physicalSourceReplacedDensity (w : SourceCircuit X Y)
    (T : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (ρ : Matrix (Config X) (Config X) ℂ) :
    Matrix Phys Phys ℂ :=
  partialTraceRight (K * sourceReplacedDensity w T ρ * Kᴴ)

/-- **Exact source operators give the physical density of the circuit back.** Source:
Theorem 5.2, `04-compression.tex`, lines 338–355. -/
theorem physicalSourceReplacedDensity_exact (w : SourceCircuit X Y)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (ρ : Matrix (Config X) (Config X) ℂ) :
    physicalSourceReplacedDensity w (exactSourceMatrix w) K ρ = physicalDensity w K ρ := by
  rw [physicalSourceReplacedDensity, physicalDensity, sourceReplacedDensity_exact,
    conjTranspose_mul]
  simp only [Matrix.mul_assoc]

open Classical in
/-- **The physical replacement error is the sum of the nonempty physical corrected terms**; no
dimension factor of the discarded factor appears. Source: Theorem 5.2,
`eq:compression-subset-expansion`, `04-compression.tex`, lines 338–383. -/
theorem physicalSourceReplacedDensity_sub_exact (w : SourceCircuit X Y)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (ρ : Matrix (Config X) (Config X) ℂ) :
    physicalSourceReplacedDensity w (E + exactSourceMatrix w) K ρ - physicalDensity w K ρ =
      ∑ S ∈ (Finset.univ : Finset (Finset w.sourceLocations)).erase ∅,
        physicalCorrectedSourceTerm w S E K ρ := by
  rw [← physicalSourceReplacedDensity_exact, physicalSourceReplacedDensity,
    physicalSourceReplacedDensity]
  have h := congrArg (fun M ↦ partialTraceRightLM (α := Phys) (β := Env) (K * M * Kᴴ))
    (sourceReplacedDensity_sub_exact w E ρ)
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sum, Matrix.sum_mul, map_sub,
    map_sum] at h
  rw [← sourceReplacedDensity_exact w ρ] at h
  exact h

open Classical in
/-- **The physical trace-norm error is at most the sum of the trace norms of the physical
corrected terms**, without dependence on the dimension of the discarded factor. Source:
Theorem 5.2, `eq:compression-total-error`. -/
theorem rectangularTraceNorm_physicalSourceReplacedDensity_sub_le [Fintype Phys] [DecidableEq Phys]
    (w : SourceCircuit X Y)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (ρ : Matrix (Config X) (Config X) ℂ) :
    rectangularTraceNorm
        (physicalSourceReplacedDensity w (E + exactSourceMatrix w) K ρ - physicalDensity w K ρ) ≤
      ∑ S ∈ (Finset.univ : Finset (Finset w.sourceLocations)).erase ∅,
        rectangularTraceNorm (physicalCorrectedSourceTerm w S E K ρ) := by
  rw [physicalSourceReplacedDensity_sub_exact]
  exact rectangularTraceNorm_sum_le _ _

/-- **The physical density of a pure input** is the partial trace of the outer product of its
read output vector. No normalization is needed. Source: `04-compression.tex`, lines 218–227 and
338–355. -/
theorem physicalDensity_pure_input (w : SourceCircuit X Y) (K : Matrix (Phys × Env) (Config Y) ℂ)
    (ψ : EuclideanSpace ℂ (Config X)) :
    physicalDensity w K (euclideanOuterProduct ψ ψ) =
      partialTraceRight (euclideanOuterProduct
        (Matrix.toEuclideanLin K (Matrix.toEuclideanLin w.op ψ))
        (Matrix.toEuclideanLin K (Matrix.toEuclideanLin w.op ψ))) := by
  rw [physicalDensity, euclideanOuterProduct, euclideanOuterProduct, mul_vecMulVec, vecMulVec_mul]
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, mulVec_mulVec, star_mulVec]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- A label-selective basis substitution acts on a mixed pure input as the outer product of the
two substituted output vectors. Source: Theorem 5.2, `04-compression.tex`, lines 338–383. -/
theorem sourceBasisMatrix_mul_euclideanOuterProduct (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations) (u v : SourceBasisChoice w S)
    (ψ φ : EuclideanSpace ℂ (Config X)) :
    sourceBasisMatrix w S u * euclideanOuterProduct ψ φ * (sourceBasisMatrix w S v)ᴴ =
      euclideanOuterProduct
        (Matrix.toEuclideanLin
          (opWithSources w (selectedSourceVectors w S (labelBasisVectors w S u))) ψ)
        (Matrix.toEuclideanLin
          (opWithSources w (selectedSourceVectors w S (labelBasisVectors w S v))) φ) := by
  rw [euclideanOuterProduct, euclideanOuterProduct, mul_vecMulVec, vecMulVec_mul]
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, star_mulVec]
  rfl

omit [∀ p, DecidableEq (Y p)] in
/-- **The trace norm of a physical corrected term does not depend on the orthonormal coordinates
of the physical and of the discarded factor**: reading the output through `(U ⊗ V) * K` instead of
`K`, for isometries `U` of the physical and `V` of the discarded factor (possibly onto larger
index types, so unitaries in particular), leaves it unchanged, for any input matrix and any
correction operators. Source: Theorem 5.2, `04-compression.tex`, lines 338–549. -/
theorem rectangularTraceNorm_physicalCorrectedSourceTerm_kronecker_isometry_mul
    {Phys' Env' : Type} [Fintype Phys] [Fintype Phys'] [Fintype Env'] [DecidableEq Phys]
    [DecidableEq Phys'] [DecidableEq Env] (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (U : Matrix Phys' Phys ℂ) (V : Matrix Env' Env ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (ρ : Matrix (Config X) (Config X) ℂ) :
    rectangularTraceNorm (physicalCorrectedSourceTerm w S E ((U ⊗ₖ V) * K) ρ) =
      rectangularTraceNorm (physicalCorrectedSourceTerm w S E K ρ) := by
  have h : (U ⊗ₖ V) * K * correctedSourceTerm w S E ρ * ((U ⊗ₖ V) * K)ᴴ =
      (U ⊗ₖ V) * (K * correctedSourceTerm w S E ρ * Kᴴ) * (U ⊗ₖ V)ᴴ := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [physicalCorrectedSourceTerm, physicalCorrectedSourceTerm, h,
    partialTraceRight_kronecker_conj_of_right_isometry U V hV,
    rectangularTraceNorm_isometry_sandwich _ U U hU hU]

/-- The permutation matrix of an equivalence, as a matrix with orthonormal columns. -/
private theorem conjTranspose_mul_submatrix_one {m n : Type} [Fintype m] [DecidableEq n]
    (e : n ≃ m) :
    ((1 : Matrix n n ℂ).submatrix e.symm id)ᴴ * (1 : Matrix n n ℂ).submatrix e.symm id = 1 := by
  let : Fintype n := Fintype.ofEquiv m e.symm
  simp only [conjTranspose_submatrix, conjTranspose_one, submatrix_mul_equiv, Matrix.one_mul,
    submatrix_id_id]

omit [∀ p, DecidableEq (Y p)] in
/-- **A reordering of the physical and discarded coordinates does not change the trace norm of a
physical corrected term**, the case of permutation matrices of
`rectangularTraceNorm_physicalCorrectedSourceTerm_kronecker_isometry_mul`. Source: Theorem 5.2,
`04-compression.tex`, lines 338–549. -/
theorem rectangularTraceNorm_physicalCorrectedSourceTerm_reindex {Phys' Env' : Type}
    [Fintype Phys] [Fintype Phys'] [Fintype Env'] [DecidableEq Phys] [DecidableEq Phys']
    (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 → w.branchLabels e.1 →
      Matrix (w.leftBasis e × w.rightBasis e) (w.leftBasis e × w.rightBasis e) ℂ)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (eP : Phys ≃ Phys') (eE : Env ≃ Env')
    (ρ : Matrix (Config X) (Config X) ℂ) :
    rectangularTraceNorm (physicalCorrectedSourceTerm w S E
        (reindex (eP.prodCongr eE) (Equiv.refl _) K) ρ) =
      rectangularTraceNorm (physicalCorrectedSourceTerm w S E K ρ) := by
  classical
  have hK : reindex (eP.prodCongr eE) (Equiv.refl _) K =
      ((1 : Matrix Phys Phys ℂ).submatrix eP.symm id ⊗ₖ
        (1 : Matrix Env Env ℂ).submatrix eE.symm id) * K := by
    ext ⟨a, b⟩ y
    simp [reindex_apply, mul_apply, Fintype.sum_prod_type, Matrix.one_apply, ite_mul]
  rw [hK, rectangularTraceNorm_physicalCorrectedSourceTerm_kronecker_isometry_mul w S E K _ _
    (conjTranspose_mul_submatrix_one eP) (conjTranspose_mul_submatrix_one eE)]

end SourceCircuit

end QuantumCircuit.Party
