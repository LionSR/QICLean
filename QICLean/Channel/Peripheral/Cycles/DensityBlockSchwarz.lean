/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.Cycles.DensityBlockFacePermutation
import QICLean.Channel.Peripheral.Cycles.MatchedBlockEndomorphism
import QICLean.Channel.Schwarz.AbstractMultiplicativeDomain
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import QICLean.Channel.Determinant.PositiveInverse

/-!
# Schwarz inequalities on Wolf's matched density blocks

This file implements the scalar repair omitted in the proof of Wolf Theorem
6.16, at `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines
1660--1663.  The argument first uses the ordinary Schwarz hypothesis on the
ambient positive trace-preserving map to prove unitality.  Exact identity
coordinates then remove the zero summand and make every density factor
maximally mixed.  Trace preservation on the matched full-matrix blocks gives
equality of the corresponding multiplicities.  Only after that equality is
known do we compress the ambient weighted Schwarz defect and cancel its common
positive scalar.

The direct Schwarz hypothesis on `T` and the trace-adjoint Schwarz hypothesis
used by Wolf Theorem 6.14 remain separate.  No complete-positivity, Kraus,
literal weighted-subalgebra restriction, or modified-product argument is used.

It also contains the following results.

* `Matrix.DirectSumFacePermutation.exists_reindexedUnitaryBlockAction`,
  `IsPositiveMap.exists_wolfTheorem616`: structure of cycles (Wolf Theorem 6.16).
-/

section DensityBlockSchwarz

open scoped Matrix MatrixOrder ComplexOrder BigOperators Kronecker

noncomputable section

namespace Matrix

/-- Exact identity witnesses in Wolf's zero-extended density-block coordinates.

Once the recurrent projection fixes the ambient identity, compression supplies
the unique full-matrix coordinate family.  Re-embedding that family is the
identity, so the zero summand vanishes and every density weight is maximally
mixed.  This is the first omitted step at Wolf Theorem 6.16, proof lines
1660--1663. -/
theorem exists_densityBlockIdentityCoordinates
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hd : ∀ k, 0 < d k) (hm : ∀ k, 0 < m k)
    (hsigmaTrace : ∀ k, (sigma k).trace = 1)
    {P : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hfixed : ∀ B, P B = B ↔
      ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        star U * B * U = Matrix.reindex e₀ e₀
          (Matrix.fromBlocks 0 0 0
            (Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))))
    (hPone : P 1 = 1) :
    ∃ Xone : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
      densityBlockWithZeroEmbedding e e₀ U hU sigma Xone = 1 ∧
      n = D ∧
      ∀ k, sigma k = (m k : ℂ)⁻¹ • 1 ∧
        Xone k = (m k : ℂ) • 1 := by
  let Xone := densityBlockWithZeroCompression e e₀ U hU (1 : Matrix (Fin D) (Fin D) ℂ)
  have hEncode : densityBlockWithZeroEmbedding e e₀ U hU sigma Xone = 1 :=
    densityBlockWithZeroEmbedding_compression_of_fixed
      e e₀ U hU sigma hsigmaTrace hfixed hPone
  obtain ⟨hn, hblocks⟩ := densityBlockWithZeroEmbedding_eq_one
    e e₀ U hU sigma hd hm hsigmaTrace Xone hEncode
  exact ⟨Xone, hEncode, hn, hblocks⟩

/-- Multiplication of a single maximally-mixed density block produces exactly
one additional inverse-multiplicity scalar.

This is the weighted-coordinate calculation omitted at Wolf Theorem 6.16,
proof lines 1660--1663. -/
theorem densityBlockWithZeroEmbedding_single_conjTranspose_mul
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigma : ∀ k, sigma k = (m k : ℂ)⁻¹ • 1)
    (k : Fin K) (X : Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    (densityBlockWithZeroEmbedding e e₀ U hU sigma
        (Pi.single k X))ᴴ *
        densityBlockWithZeroEmbedding e e₀ U hU sigma (Pi.single k X) =
      (m k : ℂ)⁻¹ •
        densityBlockWithZeroEmbedding e e₀ U hU sigma
          (Pi.single k (Xᴴ * X)) := by
  classical
  let Phi := Matrix.unitaryReindexLinearEquiv e₀ U hU
  have hcoord (Z : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ) :
      Phi (densityBlockWithZeroEmbedding e e₀ U hU sigma Z) =
        Matrix.fromBlocks 0 0 0
          (Matrix.reindex e e
            (Matrix.blockDiagonal' fun j ↦ sigma j ⊗ₖ Z j)) := by
    change Phi (Phi.symm _) = _
    exact Phi.apply_symm_apply _
  apply Phi.injective
  rw [Matrix.unitaryReindexLinearEquiv_mul]
  rw [← Matrix.star_eq_conjTranspose,
    Matrix.unitaryReindexLinearEquiv_star]
  rw [map_smul]
  rw [hcoord (Pi.single k X)]
  rw [hcoord (Pi.single k (Xᴴ * X))]
  simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
    zero_add]
  rw [Matrix.fromBlocks_smul]
  congr 1
  · simp
  · simp
  · simp
  · let A := Matrix.blockDiagonal' fun j ↦ sigma j ⊗ₖ
        (Pi.single k X : ∀ l, Matrix (Fin (d l)) (Fin (d l)) ℂ) j
    let B := Matrix.blockDiagonal' fun j ↦ sigma j ⊗ₖ
        (Pi.single k (Xᴴ * X) : ∀ l, Matrix (Fin (d l)) (Fin (d l)) ℂ) j
    change (Matrix.reindexLinearEquiv ℂ ℂ e e A)ᴴ *
        Matrix.reindexLinearEquiv ℂ ℂ e e A =
      (m k : ℂ)⁻¹ • Matrix.reindexLinearEquiv ℂ ℂ e e B
    simp only [Matrix.coe_reindexLinearEquiv]
    rw [Matrix.conjTranspose_reindex]
    let R := Matrix.reindexAlgEquiv ℂ ℂ e
    change R Aᴴ * R A = (m k : ℂ)⁻¹ • R B
    rw [← map_mul, ← map_smul]
    apply congrArg R
    simp only [A, B, Matrix.blockDiagonal'_conjTranspose]
    rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_smul]
    congr 1
    funext j
    by_cases hj : j = k
    · subst j
      simp only [Pi.single_eq_same, Pi.smul_apply]
      rw [hsigma k]
      simp [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        Matrix.smul_kronecker, smul_smul]
    · simp [Pi.single_eq_of_ne hj]

/-- Intertwining with a unital ambient map fixes the exact identity-coordinate
family.

Injectivity is obtained from the existing density-block compression; no
algebra structure is imposed on the weighted embedding.  Source: Wolf Theorem
6.16, proof lines 1660--1663. -/
theorem densityBlockMap_fixed_identityCoordinates
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigmaTrace : ∀ k, (sigma k).trace = 1)
    {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    {Tbar : Module.End ℂ (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (hencode : ∀ X,
      densityBlockWithZeroEmbedding e e₀ U hU sigma (Tbar X) =
        T (densityBlockWithZeroEmbedding e e₀ U hU sigma X))
    (hTone : T 1 = 1)
    (Xone : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)
    (hXone : densityBlockWithZeroEmbedding e e₀ U hU sigma Xone = 1) :
    Tbar Xone = Xone := by
  have hEmbed : densityBlockWithZeroEmbedding e e₀ U hU sigma (Tbar Xone) =
      densityBlockWithZeroEmbedding e e₀ U hU sigma Xone := by
    calc
      densityBlockWithZeroEmbedding e e₀ U hU sigma (Tbar Xone) =
          T (densityBlockWithZeroEmbedding e e₀ U hU sigma Xone) := hencode Xone
      _ = T 1 := congrArg T hXone
      _ = 1 := hTone
      _ = densityBlockWithZeroEmbedding e e₀ U hU sigma Xone := hXone.symm
  have hCompressed := congrArg
    (densityBlockWithZeroCompression e e₀ U hU) hEmbed
  simpa only [densityBlockWithZeroCompression_embedding
    e e₀ U hU sigma hsigmaTrace] using hCompressed

/-- Matched density blocks have equal multiplicity dimensions once the
identity-coordinate family is fixed.

The proof uses only the full-family block action, ordinary block trace
preservation, and the previously established equality of the full-matrix
dimensions.  This is the multiplicity calculation omitted at Wolf Theorem
6.16, proof line 1663. -/
theorem DirectSumFacePermutation.multiplicity_eq_of_fixed_scalar_identity
    {K : ℕ} {d m : Fin K → ℕ}
    {Tbar Sbar : Module.End ℂ (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (F : DirectSumFacePermutation Tbar Sbar)
    (hd : ∀ k, 0 < d k)
    (Xone : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)
    (hXone : ∀ k, Xone k = (m k : ℂ) • 1)
    (hFixed : Tbar Xone = Xone) (i : Fin K) :
    m i = m (F.blockEquiv i) := by
  have hAction := F.map_apply Xone (F.blockEquiv i)
  rw [show F.blockEquiv.symm (F.blockEquiv i) = i from
    F.blockEquiv.symm_apply_apply i] at hAction
  have hBlock : directSumBlockMap Tbar i (F.blockEquiv i) (Xone i) =
      Xone (F.blockEquiv i) := hAction.symm.trans (congrFun hFixed (F.blockEquiv i))
  have hTrace := congrArg Matrix.trace hBlock
  rw [hXone i, map_smul, Matrix.trace_smul, F.blockMap_trace,
    Matrix.trace_one, Fintype.card_fin, hXone (F.blockEquiv i),
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, ← F.dimension_eq i] at hTrace
  simp only [smul_eq_mul] at hTrace
  have hdComplex : (d i : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hd i))
  have hmComplex : (m i : ℂ) = m (F.blockEquiv i) :=
    mul_right_cancel₀ hdComplex hTrace
  exact_mod_cast hmComplex

/-- A raw matched block map fixes the identity after the matched
multiplicities have been identified. -/
theorem DirectSumFacePermutation.blockMap_one_of_fixed_scalar_identity
    {K : ℕ} {d m : Fin K → ℕ}
    {Tbar Sbar : Module.End ℂ (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (F : DirectSumFacePermutation Tbar Sbar)
    (hm : ∀ k, 0 < m k)
    (Xone : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)
    (hXone : ∀ k, Xone k = (m k : ℂ) • 1)
    (hFixed : Tbar Xone = Xone)
    (hmMatch : ∀ i, m i = m (F.blockEquiv i)) (i : Fin K) :
    directSumBlockMap Tbar i (F.blockEquiv i) 1 = 1 := by
  have hAction := F.map_apply Xone (F.blockEquiv i)
  rw [show F.blockEquiv.symm (F.blockEquiv i) = i from
    F.blockEquiv.symm_apply_apply i] at hAction
  have hBlock : directSumBlockMap Tbar i (F.blockEquiv i) (Xone i) =
      Xone (F.blockEquiv i) := hAction.symm.trans (congrFun hFixed (F.blockEquiv i))
  rw [hXone i, map_smul, hXone (F.blockEquiv i), ← hmMatch i] at hBlock
  have hmComplex : (m i : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hm i))
  exact smul_right_injective _ hmComplex hBlock

set_option maxHeartbeats 800000 in
-- The indexed density-block rewrites elaborate through several dependent matrix types.
/-- Compressing the ambient Schwarz defect gives the ordinary Schwarz
inequality on every raw matched density-block map.

The two density-block multiplications initially contribute the unequal
coefficients `(m i : ℂ)⁻¹ * (m (F.blockEquiv i) : ℂ)⁻¹` and
`(m (F.blockEquiv i) : ℂ)⁻¹ * (m (F.blockEquiv i) : ℂ)⁻¹`.
They are identified only by `hmMatch`; the resulting positive scalar is then
cancelled before positivity is reflected through the nonzero identity tensor
factor.  This is Wolf Theorem 6.16, proof line 1663. -/
theorem DirectSumFacePermutation.rawBlock_isSchwarzMap_of_ambientDensityBlocks
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigma : ∀ k, sigma k = (m k : ℂ)⁻¹ • 1)
    {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    {Tbar Sbar : Module.End ℂ (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (F : DirectSumFacePermutation Tbar Sbar)
    (hm : ∀ k, 0 < m k)
    (hmMatch : ∀ i, m i = m (F.blockEquiv i))
    (hPos : IsPositiveMap T) (hSchwarz : IsSchwarzMap T)
    (hencode : ∀ X,
      densityBlockWithZeroEmbedding e e₀ U hU sigma (Tbar X) =
        T (densityBlockWithZeroEmbedding e e₀ U hU sigma X))
    (i : Fin K) :
    ∀ X : Matrix (Fin (d i)) (Fin (d i)) ℂ,
      (directSumBlockMap Tbar i (F.blockEquiv i) (Xᴴ * X) -
        directSumBlockMap Tbar i (F.blockEquiv i) Xᴴ *
          directSumBlockMap Tbar i (F.blockEquiv i) X).PosSemidef := by
  classical
  intro X
  let j := F.blockEquiv i
  let raw := directSumBlockMap Tbar i j
  have hRawPos : IsPositiveMap raw := fun Z hZ ↦ F.blockMap_pos i Z hZ
  let E := densityBlockWithZeroEmbedding e e₀ U hU sigma
  let A := E (Pi.single i X)
  have hTsingle (Z : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
      T (E (Pi.single i Z)) = E (Pi.single j (raw Z)) := by
    calc
      T (E (Pi.single i Z)) = E (Tbar (Pi.single i Z)) :=
        (hencode (Pi.single i Z)).symm
      _ = E (Pi.single j (raw Z)) := by
        rw [F.map_single]
  have hAprod :
      Aᴴ * A = (m i : ℂ)⁻¹ • E (Pi.single i (Xᴴ * X)) := by
    exact densityBlockWithZeroEmbedding_single_conjTranspose_mul
      e e₀ U hU sigma hsigma i X
  have hFirst :
      T (Aᴴ * A) =
        (m i : ℂ)⁻¹ • E (Pi.single j (raw (Xᴴ * X))) := by
    rw [hAprod, map_smul, hTsingle]
  have hTA : T A = E (Pi.single j (raw X)) := hTsingle X
  have hSecond :
      T Aᴴ * T A =
        (m j : ℂ)⁻¹ • E (Pi.single j ((raw X)ᴴ * raw X)) := by
    rw [hPos.map_conjTranspose A, hTA]
    exact densityBlockWithZeroEmbedding_single_conjTranspose_mul
      e e₀ U hU sigma hsigma j (raw X)
  have hAmbient := hSchwarz A
  rw [hFirst, hSecond] at hAmbient
  have hCompressed := densityBlockWithZeroPrincipalCompression_posSemidef
    e e₀ U hU j hAmbient
  dsimp only [E] at hCompressed
  simp only [map_sub, map_smul,
    densityBlockWithZeroPrincipalCompression_embedding, Pi.single_eq_same,
    hsigma, Matrix.smul_kronecker, smul_smul] at hCompressed
  change
    (((m i : ℂ)⁻¹ * (m j : ℂ)⁻¹) •
          ((1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ raw (Xᴴ * X)) -
        ((m j : ℂ)⁻¹ * (m j : ℂ)⁻¹) •
          ((1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ
            ((raw X)ᴴ * raw X))).PosSemidef at hCompressed
  have hmScalar : (m i : ℂ)⁻¹ = (m j : ℂ)⁻¹ := by
    exact congrArg (fun a : ℕ ↦ (a : ℂ)⁻¹) (hmMatch i)
  rw [hmScalar] at hCompressed
  let c : ℂ := (m j : ℂ)⁻¹ * (m j : ℂ)⁻¹
  let defect := raw (Xᴴ * X) - (raw X)ᴴ * raw X
  have hScaled :
      (c • ((1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ defect)).PosSemidef := by
    convert hCompressed using 1
    ext a b
    simp only [c, defect, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Matrix.sub_apply, smul_eq_mul]
    ring
  have hmComplexPos : (0 : ℂ) < m j := by
    exact_mod_cast hm j
  have hcPos : (0 : ℂ) < c := by
    exact mul_pos (inv_pos.mpr hmComplexPos) (inv_pos.mpr hmComplexPos)
  have hOneTensor :
      ((1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ defect).PosSemidef := by
    have hRescaled := hScaled.smul (inv_pos.mpr hcPos).le
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hcPos), one_smul] using hRescaled
  let _ : NeZero (m j) := ⟨Nat.ne_of_gt (hm j)⟩
  have hRawStar : raw Xᴴ = (raw X)ᴴ := hRawPos.map_conjTranspose X
  simpa only [defect, raw, j, hRawStar] using
    Matrix.PosSemidef.right_of_one_kronecker hOneTensor

end Matrix

namespace IsPositiveMap

/-- A positive trace-preserving Schwarz map and its recurrent projection both
fix the identity.

The first equality is the direct-Schwarz unitality step.  The second places the
identity in Wolf's asymptotic image before density-block coordinates are
normalized.  Source: Wolf Theorem 6.16, proof lines 1629--1633 and 1660--1663. -/
theorem map_one_and_peripheralProjection_one_of_tracePreserving_of_isSchwarzMap
    {D : ℕ} [NeZero D]
    {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap T) :
    T 1 = 1 ∧ T.peripheralProjection 1 = 1 := by
  have hTone := hPos.map_one_eq_one_of_tracePreserving_of_isSchwarzMap hTP hSchwarz
  have hEig : Module.End.HasEigenvalue T 1 :=
    hasEigenvalue_of_eigenvector_eq T 1 1
      (by simpa only [one_smul] using hTone) one_ne_zero
  have hOneMem : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ T.eigenspace 1 :=
    Module.End.mem_eigenspace_iff.mpr (by simpa only [one_smul] using hTone)
  exact ⟨hTone,
    T.peripheralProjection_apply_of_mem_eigenspace hEig (by simp) hOneMem⟩

/-- **Wolf Theorem 6.16: Schwarz maps on the matched density blocks.**

This is the source-facing handoff after the pure-state-face permutation and
before excluding the transpose alternative.  In addition to the exact
density-block data and actions returned by
`exists_peripheralDensityBlockFacePermutation`, it proves that the zero
summand disappears, the weights are maximally mixed, matched multiplicities
agree, and both the raw and canonically reindexed matched block maps satisfy
the ordinary Schwarz inequality.

The direct Schwarz hypothesis on `T` is intentionally distinct from the
trace-adjoint Schwarz hypothesis used to obtain Wolf Theorem 6.14.  No unitary
classification or Equation (6.68) is asserted here. -/
theorem exists_peripheralDensityBlockSchwarz
    {D : ℕ} [NeZero D]
    {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hPos : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap T)
    (hAdjointSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T)) :
    ∃ (n K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
      (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
      (U : Matrix (Fin D) (Fin D) ℂ)
      (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
      (S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)),
      (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ k, (sigma k).PosDef) ∧ (∀ k, (sigma k).trace = 1) ∧
        (∀ B, T.peripheralProjection B = B ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * B * U = Matrix.reindex e₀ e₀
              (Matrix.fromBlocks 0 0 0
                (Matrix.reindex e e
                  (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k)))) ∧
        IsPositiveMap S ∧ IsTracePreservingMap S ∧
        (let Tbar := Matrix.densityBlockDynamics e e₀ U hU sigma T
         let Sbar := Matrix.densityBlockDynamics e e₀ U hU sigma S
         (∀ X, Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma (Tbar X) =
            T (Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma X)) ∧
         (∀ X, Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma (Sbar X) =
            S (Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma X)) ∧
         Sbar.comp Tbar = LinearMap.id ∧
         Tbar.comp Sbar = LinearMap.id ∧
         Matrix.IsPositiveDirectSumMap Tbar ∧
         Matrix.IsPositiveDirectSumMap Sbar ∧
         Matrix.IsTracePreservingBetweenDirectSums Tbar ∧
         Matrix.IsTracePreservingBetweenDirectSums Sbar ∧
         ∃ F : Matrix.DirectSumFacePermutation Tbar Sbar,
           let pi := F.blockEquiv.symm
           (∀ X j, Tbar X j =
             Matrix.directSumBlockMap Tbar (pi j) j (X (pi j))) ∧
           (∀ Y i, Sbar Y i =
             Matrix.directSumBlockMap Sbar (pi.symm i) i (Y (pi.symm i))) ∧
           (∀ j, d (pi j) = d j) ∧
           n = D ∧
           (∀ k, sigma k = (m k : ℂ)⁻¹ • 1) ∧
           (∀ i, m i = m (F.blockEquiv i)) ∧
           (∀ i, Matrix.directSumBlockMap Tbar i (F.blockEquiv i) 1 = 1) ∧
           (∀ i X, (Matrix.directSumBlockMap Tbar i (F.blockEquiv i) (Xᴴ * X) -
             Matrix.directSumBlockMap Tbar i (F.blockEquiv i) Xᴴ *
               Matrix.directSumBlockMap Tbar i (F.blockEquiv i) X).PosSemidef) ∧
           ∀ i, IsSchwarzMap (F.matchedBlockEndomorphism i)) := by
  classical
  obtain ⟨n, K, d, m, e, e₀, U, sigma, hU, S, hd, hm, hsigmaPosDef,
      hsigmaTrace, hfixed, hSPos, hSTP, hDynamics⟩ :=
    hPos.exists_peripheralDensityBlockFacePermutation hTP hAdjointSchwarz
  obtain ⟨hTone, hPone⟩ :=
    hPos.map_one_and_peripheralProjection_one_of_tracePreserving_of_isSchwarzMap
      hTP hSchwarz
  obtain ⟨Xone, hXone, hn, hIdentityBlocks⟩ :=
    Matrix.exists_densityBlockIdentityCoordinates e e₀ U hU sigma hd hm
      hsigmaTrace hfixed hPone
  have hsigma : ∀ k, sigma k = (m k : ℂ)⁻¹ • 1 :=
    fun k ↦ (hIdentityBlocks k).1
  have hXoneScalar : ∀ k, Xone k = (m k : ℂ) • 1 :=
    fun k ↦ (hIdentityBlocks k).2
  dsimp only at hDynamics
  rcases hDynamics with
    ⟨hTencode, hSencode, hST, hTS, hTPos, hSbarPos, hTTP, hSTPbar,
      F, hMap, hInverseMap, hDimension⟩
  have hXoneFixed := Matrix.densityBlockMap_fixed_identityCoordinates
    e e₀ U hU sigma hsigmaTrace hTencode hTone Xone hXone
  have hmMatch : ∀ i, m i = m (F.blockEquiv i) := fun i ↦
    F.multiplicity_eq_of_fixed_scalar_identity hd Xone hXoneScalar hXoneFixed i
  have hBlockOne : ∀ i,
      Matrix.directSumBlockMap
        (Matrix.densityBlockDynamics e e₀ U hU sigma T)
        i (F.blockEquiv i) 1 = 1 := fun i ↦
    F.blockMap_one_of_fixed_scalar_identity hm Xone hXoneScalar
      hXoneFixed hmMatch i
  have hRawSchwarz : ∀ i X,
      (Matrix.directSumBlockMap
          (Matrix.densityBlockDynamics e e₀ U hU sigma T)
          i (F.blockEquiv i) (Xᴴ * X) -
        Matrix.directSumBlockMap
          (Matrix.densityBlockDynamics e e₀ U hU sigma T)
          i (F.blockEquiv i) Xᴴ *
        Matrix.directSumBlockMap
          (Matrix.densityBlockDynamics e e₀ U hU sigma T)
          i (F.blockEquiv i) X).PosSemidef := fun i ↦
    F.rawBlock_isSchwarzMap_of_ambientDensityBlocks e e₀ U hU sigma hsigma
      hm hmMatch hPos hSchwarz hTencode i
  have hMatchedSchwarz : ∀ i, IsSchwarzMap (F.matchedBlockEndomorphism i) :=
    fun i ↦ F.matchedBlockEndomorphism_isSchwarzMap_of_raw i (hRawSchwarz i)
  refine ⟨n, K, d, m, e, e₀, U, sigma, hU, S, hd, hm, hsigmaPosDef,
    hsigmaTrace, hfixed, hSPos, hSTP, ?_⟩
  dsimp only
  exact ⟨hTencode, hSencode, hST, hTS, hTPos, hSbarPos, hTTP, hSTPbar,
    F, hMap, hInverseMap, hDimension, hn, hsigma, hmMatch, hBlockOne,
    hRawSchwarz, hMatchedSchwarz⟩

end IsPositiveMap

end

end DensityBlockSchwarz

section StructureOfCycles

/-!
## Structure of cycles (Wolf Theorem 6.16)

This file assembles the source-facing density-block statement and dynamics in
Wolf Theorem 6.16, Equations (6.66)--(6.68).  The direct Schwarz hypothesis on
the map and the Schwarz hypothesis on its trace adjoint remain separate.

The formal density-block coordinates use the tensor order `sigma k ⊗ₖ X k`.
Wolf prints `x k ⊗ rho k`; the two conventions differ only by the canonical
interchange of the tensor factors.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines
1597--1664.
-/

open scoped Matrix MatrixOrder ComplexOrder Kronecker

noncomputable section

namespace Matrix

/-- The matched full-matrix maps in Wolf Theorem 6.16 are unitary
conjugations, expressed with Wolf's output-to-input permutation.

The face permutation `F.blockEquiv` sends an input block to its output block.
Thus Wolf's permutation is `pi := F.blockEquiv.symm`.  The unitary returned by
the positive-invertible Schwarz classification acts first on the input-indexed
copy of the matrix algebra; simultaneous reindexing along `d (pi k) = d k`
makes it an output-indexed unitary `V k`.

Source: Wolf Theorem 6.16, proof lines 1637--1663. -/
theorem DirectSumFacePermutation.exists_reindexedUnitaryBlockAction
    {K : ℕ} {d : Fin K → ℕ}
    {Tbar Sbar : Module.End ℂ
      (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (F : DirectSumFacePermutation Tbar Sbar)
    (hd : ∀ k, 0 < d k)
    (hSchwarz : ∀ i, IsSchwarzMap (F.matchedBlockEndomorphism i)) :
    let pi := F.blockEquiv.symm
    ∃ (hdpi : ∀ k, d (pi k) = d k)
      (V : ∀ k, Matrix.unitaryGroup (Fin (d k)) ℂ),
      ∀ X k,
        Tbar X k =
          (V k : Matrix (Fin (d k)) (Fin (d k)) ℂ) *
            Matrix.reindex (finCongr (hdpi k)) (finCongr (hdpi k))
              (X (pi k)) *
            (V k : Matrix (Fin (d k)) (Fin (d k)) ℂ)ᴴ := by
  classical
  dsimp only
  let : ∀ k, NeZero (d k) := fun k ↦ ⟨Nat.ne_of_gt (hd k)⟩
  have hdpi : ∀ k, d (F.blockEquiv.symm k) = d k := fun k ↦ by
    simpa only [Equiv.apply_symm_apply] using
      F.dimension_eq (F.blockEquiv.symm k)
  have hUnitary : ∀ i, ∃ W : Matrix.unitaryGroup (Fin (d i)) ℂ,
      F.matchedBlockEndomorphism i =
        unitaryChannel W := by
    intro i
    let hBij := F.matchedBlockEndomorphism_bijective i
    exact ChannelDeterminant.Internal.wolfPositiveInvertibleSchwarzMaps hBij
      (F.matchedBlockEndomorphism_isPositiveMap i)
      (F.matchedBlockEndomorphism_isTracePreservingMap i)
      (F.matchedBlockCanonicalInverse_isPositiveMap i hBij) (hSchwarz i)
  choose W hW using hUnitary
  let V : ∀ k, Matrix.unitaryGroup (Fin (d k)) ℂ := fun k ↦
    ⟨Matrix.reindex (finCongr (hdpi k)) (finCongr (hdpi k))
        (W (F.blockEquiv.symm k) :
          Matrix (Fin (d (F.blockEquiv.symm k)))
            (Fin (d (F.blockEquiv.symm k))) ℂ),
      Matrix.reindex_mem_unitaryGroup (finCongr (hdpi k)) _
        (W (F.blockEquiv.symm k)).property⟩
  refine ⟨hdpi, V, ?_⟩
  have hActionAtSource
      (X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) (i : Fin K) :
      Tbar X (F.blockEquiv i) =
        (V (F.blockEquiv i) :
          Matrix (Fin (d (F.blockEquiv i)))
            (Fin (d (F.blockEquiv i))) ℂ) *
          Matrix.reindex (finCongr (hdpi (F.blockEquiv i)))
            (finCongr (hdpi (F.blockEquiv i)))
            (X (F.blockEquiv.symm (F.blockEquiv i))) *
          (V (F.blockEquiv i) :
            Matrix (Fin (d (F.blockEquiv i)))
              (Fin (d (F.blockEquiv i))) ℂ)ᴴ := by
    have hMatched :
        F.matchedBlockEndomorphism i (X i) =
          (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ) * X i *
            (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ)ᴴ := by
      simpa only [unitaryChannel, LinearMap.coe_mk, AddHom.coe_mk] using
        LinearMap.congr_fun (hW i) (X i)
    have hRawAtEquiv :
        Matrix.directSumBlockMap Tbar i (F.blockEquiv i) (X i) =
          Matrix.reindex (finCongr (F.dimension_eq i))
            (finCongr (F.dimension_eq i))
            ((W i : Matrix (Fin (d i)) (Fin (d i)) ℂ) * X i *
              (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ)ᴴ) := by
      let R := Matrix.reindexAlgEquiv ℂ ℂ (finCongr (F.dimension_eq i))
      apply R.symm.injective
      change R.symm (Matrix.directSumBlockMap Tbar i (F.blockEquiv i) (X i)) =
        R.symm (R ((W i : Matrix (Fin (d i)) (Fin (d i)) ℂ) * X i *
          (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ)ᴴ))
      rw [R.symm_apply_apply]
      simpa only [R, F.matchedBlockEndomorphism_apply,
        Matrix.symm_reindexAlgEquiv, Matrix.coe_reindexAlgEquiv] using hMatched
    rw [F.map_apply_blockEquiv, hRawAtEquiv]
    dsimp only [V]
    suffices ∀ (s : Fin K), s = i →
        ∀ hsi : d s = d (F.blockEquiv i),
          Matrix.reindex (finCongr (F.dimension_eq i))
              (finCongr (F.dimension_eq i))
              ((W i : Matrix (Fin (d i)) (Fin (d i)) ℂ) * X i *
                (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ)ᴴ) =
            Matrix.reindex (finCongr hsi) (finCongr hsi)
                (W s : Matrix (Fin (d s)) (Fin (d s)) ℂ) *
              Matrix.reindex (finCongr hsi) (finCongr hsi) (X s) *
              (Matrix.reindex (finCongr hsi) (finCongr hsi)
                (W s : Matrix (Fin (d s)) (Fin (d s)) ℂ))ᴴ by
      exact this (F.blockEquiv.symm (F.blockEquiv i))
        (F.blockEquiv.symm_apply_apply i) (hdpi (F.blockEquiv i))
    intro s hs hsi
    subst s
    have hhsi : hsi = F.dimension_eq i := Subsingleton.elim _ _
    cases hhsi
    rw [Matrix.conjTranspose_reindex]
    let R := Matrix.reindexAlgEquiv ℂ ℂ (finCongr (F.dimension_eq i))
    change R ((W i : Matrix (Fin (d i)) (Fin (d i)) ℂ) * X i *
        (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ)ᴴ) =
      R (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ) * R (X i) *
        R (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ)ᴴ
    rw [map_mul, map_mul]
  intro X k
  obtain ⟨i, rfl⟩ := F.blockEquiv.surjective k
  exact hActionAtSource X i

end Matrix

namespace IsPositiveMap

/-- **Wolf Theorem 6.16, Equations (6.66)--(6.68).**

Let `T` be a positive trace-preserving map satisfying the Schwarz inequality,
and suppose separately that its trace adjoint is Schwarz as required by Wolf
Theorem 6.14.  Its asymptotic image has the zero-extended density-block form
of Equations (6.66)--(6.67).  The zero summand has dimension zero, every
density factor is maximally mixed, and the coordinate action permutes equal
`d`- and `m`-dimensional blocks and conjugates by output-indexed unitaries.
The final equality is the ambient form of Equation (6.68).

The formal coordinates retain `sigma k ⊗ₖ X k`, whereas Wolf prints
`x k ⊗ rho k`; these are related by the canonical tensor-factor swap.  The
explicit `e₀` and `Matrix.fromBlocks 0 0 0` are deliberately retained even
though `n = D`, avoiding a dependent rewrite of the zero summand.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines
1597--1664, Equations (6.66)--(6.68). -/
theorem exists_wolfTheorem616
    {D : ℕ} [NeZero D]
    {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hPos : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap T)
    (hAdjointSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T)) :
    ∃ (n K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
      (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
      (U : Matrix (Fin D) (Fin D) ℂ)
      (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
      (pi : Fin K ≃ Fin K)
      (hdpi : ∀ k, d (pi k) = d k)
      (V : ∀ k, Matrix.unitaryGroup (Fin (d k)) ℂ)
      (A : Module.End ℂ (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)),
      (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ k, (sigma k).PosDef) ∧ (∀ k, (sigma k).trace = 1) ∧
        (∀ B, B ∈ T.peripheralSubspace ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * B * U = Matrix.reindex e₀ e₀
              (Matrix.fromBlocks 0 0 0
                (Matrix.reindex e e
                  (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k)))) ∧
        n = D ∧
        (∀ k, sigma k = (m k : ℂ)⁻¹ • 1) ∧
        (∀ k, m (pi k) = m k) ∧
        (∀ X k,
          A X k =
            (V k : Matrix (Fin (d k)) (Fin (d k)) ℂ) *
              Matrix.reindex (finCongr (hdpi k)) (finCongr (hdpi k))
                (X (pi k)) *
              (V k : Matrix (Fin (d k)) (Fin (d k)) ℂ)ᴴ) ∧
        ∀ X,
          T (Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma X) =
            Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma (A X) := by
  classical
  obtain ⟨n, K, d, m, e, e₀, U, sigma, hU, S, hd, hm, hsigmaPosDef,
      hsigmaTrace, hfixed, hSPos, hSTP, hDynamics⟩ :=
    hPos.exists_peripheralDensityBlockSchwarz hTP hSchwarz hAdjointSchwarz
  dsimp only at hDynamics
  rcases hDynamics with
    ⟨hTencode, hSencode, hST, hTS, hTPos, hSbarPos, hTTP, hSTPbar,
      F, hMap, hInverseMap, hDimension, hn, hsigma, hmMatch, hBlockOne,
      hRawSchwarz, hMatchedSchwarz⟩
  obtain ⟨hdpi, V, hAction⟩ :=
    F.exists_reindexedUnitaryBlockAction hd hMatchedSchwarz
  let pi : Fin K ≃ Fin K := F.blockEquiv.symm
  let A := Matrix.densityBlockDynamics e e₀ U hU sigma T
  have hmpi : ∀ k, m (pi k) = m k := fun k ↦ by
    simpa only [pi, Equiv.apply_symm_apply] using
      hmMatch (F.blockEquiv.symm k)
  have hperipheral : ∀ B, B ∈ T.peripheralSubspace ↔
      ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        star U * B * U = Matrix.reindex e₀ e₀
          (Matrix.fromBlocks 0 0 0
            (Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))) := fun B ↦
    (Module.End.peripheralProjection_apply_eq_self_iff T B).symm.trans
      (hfixed B)
  refine ⟨n, K, d, m, e, e₀, U, sigma, hU, pi, hdpi, V, A,
    hd, hm, hsigmaPosDef, hsigmaTrace, hperipheral, hn, hsigma, hmpi, ?_, ?_⟩
  · simpa only [A, pi] using hAction
  · intro X
    simpa only [A] using (hTencode X).symm

end IsPositiveMap

end

end StructureOfCycles
