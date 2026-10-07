/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.TypicalPureState
import QICLean.Algebra.MatrixIsometryKronecker

/-!
# Selected Schmidt vectors on the selected coordinate space

The selected columns of the spectral unitary identify the selected coordinate
space with its spectral subspace. Applying the adjoint of this isometry to the
original pure vector and normalizing gives a pure vector on the smaller space.
Its first marginal is the selected diagonal spectrum, and its complementary
marginal agrees with that of the typical truncation on the original space.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 240–247 and `comparator:post-marginal`,
at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Labels: comparator:typical-set, comparator:post-marginal.
Provenance-ID: 8753-qic-typical-pure-compression-01
Downstream declaration:
Matrix.IsHermitian.spectralSelectionEmbedding
Provenance-ID: 8753-qic-typical-pure-compression-02
Downstream declaration:
Matrix.IsHermitian.isIsometry_spectralSelectionEmbedding
Provenance-ID: 8753-qic-typical-pure-compression-03
Downstream declaration:
Matrix.IsHermitian.spectralSelectionEmbedding_mul_conjTranspose
Provenance-ID: 8753-qic-typical-pure-compression-04
Downstream declaration:
Matrix.compressedTypicalPureState
Provenance-ID: 8753-qic-typical-pure-compression-05
Downstream declaration:
Matrix.kronecker_mulVec_compressedTypicalPureState
Provenance-ID: 8753-qic-typical-pure-compression-06
Downstream declaration:
Matrix.partialTraceRight_compressedTypicalPureState
Provenance-ID: 8753-qic-typical-pure-compression-07
Downstream declaration:
Matrix.partialTraceLeft_compressedTypicalPureState
Provenance-ID: 8753-qic-typical-pure-compression-08
Downstream declaration:
Matrix.norm_compressedTypicalPureState
-/

open scoped BigOperators Matrix Kronecker ComplexOrder

noncomputable section

namespace Matrix

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The spectral isometry from the selected coordinate space to the original space.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
def IsHermitian.spectralSelectionEmbedding {ρ : Matrix A A ℂ} (hρ : ρ.IsHermitian)
    (E : Finset A) : Matrix A E ℂ :=
  (hρ.eigenvectorUnitary : Matrix A A ℂ).submatrix id Subtype.val

/-- Selected orthonormal eigenvectors define an isometry.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem IsHermitian.isIsometry_spectralSelectionEmbedding {ρ : Matrix A A ℂ}
    (hρ : ρ.IsHermitian) (E : Finset A) :
    (hρ.spectralSelectionEmbedding E).IsIsometry := by
  have h := congrArg (fun M : Matrix A A ℂ ↦
    (M.submatrix Subtype.val Subtype.val : Matrix E E ℂ))
    (Unitary.coe_star_mul_self hρ.eigenvectorUnitary)
  simpa [IsIsometry, spectralSelectionEmbedding, conjTranspose_submatrix,
    star_eq_conjTranspose, submatrix_mul _ _ _ id _ Function.bijective_id,
    submatrix_one _ Subtype.val_injective] using h

/-- The range projection of the spectral isometry is the selected projection.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem IsHermitian.spectralSelectionEmbedding_mul_conjTranspose {ρ : Matrix A A ℂ}
    (hρ : ρ.IsHermitian) (E : Finset A) :
    hρ.spectralSelectionEmbedding E * (hρ.spectralSelectionEmbedding E)ᴴ =
      hρ.spectralSelection E := by
  ext a b
  simp only [spectralSelectionEmbedding, conjTranspose_submatrix, mul_apply,
    Finset.univ_eq_attach, submatrix_apply, id_eq, eigenvectorUnitary_apply,
    conjTranspose_apply, RCLike.star_def, spectralSelection, Unitary.conjStarAlgAut_apply,
    star_eq_conjTranspose, diagonal_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ite_mul, zero_mul,
    Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_attach E (fun i ↦
    (hρ.eigenvectorBasis i).ofLp a * (starRingEnd ℂ) ((hρ.eigenvectorBasis i).ofLp b))

private theorem spectralSelectionEmbedding_compression {ρ : Matrix A A ℂ}
    (hρ : ρ.IsHermitian) (E : Finset A) :
    (hρ.spectralSelectionEmbedding E)ᴴ * ρ * hρ.spectralSelectionEmbedding E =
      diagonal (fun i : E ↦ (hρ.eigenvalues i : ℂ)) := by
  have h := congrArg (fun M : Matrix A A ℂ ↦ (M.submatrix Subtype.val Subtype.val : Matrix E E ℂ))
    hρ.conjStarAlgAut_star_eigenvectorUnitary
  simpa [Unitary.conjStarAlgAut_star_apply, star_eq_conjTranspose,
    submatrix_mul _ _ _ id _ Function.bijective_id, submatrix_id_id,
    submatrix_diagonal _ _ Subtype.val_injective, Function.comp_def,
    IsHermitian.spectralSelectionEmbedding, conjTranspose_submatrix] using h

private theorem kronecker_one_mulVec_matrix {R S : Type*} [Fintype S]
    (J : Matrix R S ℂ) (C : Matrix S B ℂ) :
    (J ⊗ₖ (1 : Matrix B B ℂ)) *ᵥ (fun x : S × B ↦ C x.1 x.2) =
      (fun x : R × B ↦ (J * C) x.1 x.2) := by
  ext x
  simp [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply,
    one_apply, Matrix.mul_apply]

variable (ψ : EuclideanSpace ℂ (A × B)) (E : Finset A)

local notation "ρA" => partialTraceRight (vecMulVec ψ (star ψ))
local notation "hρA" => Matrix.PosSemidef.partialTraceRight (posSemidef_vecMulVec_self_star ψ)
local notation "zE" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian hρA) E
local notation "JE" => Matrix.IsHermitian.spectralSelectionEmbedding
  (Matrix.PosSemidef.isHermitian hρA) E

/-- The normalized selected Schmidt vector on the selected coordinate space.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
def compressedTypicalPureState : EuclideanSpace ℂ (E × B) :=
  (Real.sqrt zE : ℂ)⁻¹ • WithLp.toLp 2 (fun x ↦ (JEᴴ * schmidtCoeffMatrix ψ) x.1 x.2)

/-- Embedding the compressed vector gives the actual typical truncation.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem kronecker_mulVec_compressedTypicalPureState :
    WithLp.toLp 2 ((JE ⊗ₖ (1 : Matrix B B ℂ)) *ᵥ compressedTypicalPureState ψ E) =
      typicalPureState ψ E := by
  simp only [compressedTypicalPureState, typicalPureState, leftFilteredVector,
    WithLp.ofLp_toLp, Matrix.mulVec_smul,
    kronecker_one_mulVec_matrix, ← WithLp.toLp_smul]
  rw [← Matrix.mul_assoc, IsHermitian.spectralSelectionEmbedding_mul_conjTranspose]

omit [DecidableEq B] in
/-- The actual selected-space marginal is the normalized selected diagonal spectrum.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem partialTraceRight_compressedTypicalPureState (hz : 0 < zE) :
    partialTraceRight (vecMulVec (compressedTypicalPureState ψ E)
      (star (compressedTypicalPureState ψ E))) =
      diagonal (fun i : E ↦ (((hρA).isHermitian.eigenvalues i / zE : ℝ) : ℂ)) := by
  rw [partialTraceRight_vecMulVec_eq]
  change ((Real.sqrt zE : ℂ)⁻¹ • (JEᴴ * schmidtCoeffMatrix ψ)) *
    ((Real.sqrt zE : ℂ)⁻¹ • (JEᴴ * schmidtCoeffMatrix ψ))ᴴ = _
  simp only [conjTranspose_smul, Complex.star_def, map_inv₀, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjTranspose_mul,
    conjTranspose_conjTranspose]
  rw [← mul_inv, ← sq, ← Complex.ofReal_pow, Real.sq_sqrt hz.le,
    Matrix.mul_assoc, ← Matrix.mul_assoc (schmidtCoeffMatrix ψ),
    ← partialTraceRight_vecMulVec_eq]
  rw [← Matrix.mul_assoc, spectralSelectionEmbedding_compression]
  simp [← diagonal_smul, div_eq_mul_inv, mul_comm]

omit [DecidableEq B] in
/-- Compressing the selected factor preserves the entire complementary marginal.
OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem partialTraceLeft_compressedTypicalPureState :
    partialTraceLeft (vecMulVec (compressedTypicalPureState ψ E)
      (star (compressedTypicalPureState ψ E))) =
      partialTraceLeft (vecMulVec (typicalPureState ψ E) (star (typicalPureState ψ E))) := by
  classical
  have h := partialTraceLeft_kronecker_conj_of_left_isometry JE (1 : Matrix B B ℂ)
    ((hρA).isHermitian.isIsometry_spectralSelectionEmbedding E)
    (vecMulVec (compressedTypicalPureState ψ E) (star (compressedTypicalPureState ψ E)))
  rw [← kronecker_mulVec_compressedTypicalPureState ψ E]
  simpa only [WithLp.ofLp_toLp, conjTranspose_one, one_mul, mul_one,
    mul_vecMulVec, vecMulVec_mul, vecMul_conjTranspose, star_star] using h.symm

omit [DecidableEq B] in
/-- A positive selected mass gives a normalized compressed pure vector.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem norm_compressedTypicalPureState (hz : 0 < zE) :
    ‖compressedTypicalPureState ψ E‖ = 1 := by
  classical
  have h := congrArg (fun M : Matrix B B ℂ ↦ M.trace.re)
    (partialTraceLeft_compressedTypicalPureState ψ E)
  simp only [trace_partialTraceLeft, trace_vecMulVec] at h
  rw [dotProduct_comm, ← norm_toLp_sq, dotProduct_comm, ← norm_toLp_sq,
    WithLp.toLp_ofLp, WithLp.toLp_ofLp, norm_typicalPureState ψ E hz, one_pow] at h
  nlinarith [norm_nonneg (compressedTypicalPureState ψ E)]

end Matrix
