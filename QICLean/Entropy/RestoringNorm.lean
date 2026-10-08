/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RestoringOperators
import QICLean.Channel.PartialTrace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Operator norm bounds for singular restoration

The three typical spectral inequalities bound the actual weighted block sum
`B_Y`, hence the actual restoring and column operators. Only selected
probabilities are inverted. No full-rank hypothesis or commutation between
`Q` and `I ⊗ T` is used. Norms are the Euclidean operator norms.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `09-amplification.tex`, lines 374–397.
<https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex>
Independently written from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix Finset
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Entropy

variable {X Y : Type*} [Fintype X] [Fintype Y]

private theorem compression_mono {A B : Matrix Y Y ℂ} (h : A ≤ B)
    {T : Matrix Y Y ℂ} (hT : T.IsHermitian) : T * A * T ≤ T * B * T := by
  have hp := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same T
  rw [hT.eq] at hp
  exact (Matrix.le_iff).mpr (by simpa only [mul_sub, sub_mul] using hp)

omit [Fintype Y] in
private theorem block_sum_le_partialTrace {Q : Matrix (X × Y) (X × Y) ℂ}
    (hQ : Q.PosSemidef) (E : Finset X) :
    ∑ x ∈ E, restoringBlock Q x ≤ partialTraceLeft Q := by
  have hsum : (∑ x : X, restoringBlock Q x) = partialTraceLeft Q := by
    ext i j
    simp only [Matrix.sum_apply, restoringBlock, submatrix_apply, partialTraceLeft_apply]
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
    fun x _ _ ↦ (hQ.submatrix _).nonneg

/-- The selected weighted block sum is bounded by the compressed full partial
trace. Unselected coordinates, including zero-probability coordinates, only
contribute nonnegative terms to the full partial trace.
Source: `09-amplification.tex`, lines 374–389. -/
theorem restoringGram_le_compressed_partialTrace (E : Finset X) (p : X → ℝ)
    {Q : Matrix (X × Y) (X × Y) ℂ} {T : Matrix Y Y ℂ}
    (hQ : Q.PosSemidef) (hT : T.IsHermitian) {cX : ℝ} (hcX : 0 ≤ cX)
    (hpX : ∀ x ∈ E, (p x)⁻¹ ≤ cX) :
    restoringGram E p Q T ≤ cX • (T * partialTraceLeft Q * T) := by
  calc
    _ ≤ ∑ x ∈ E, cX • (T * restoringBlock Q x * T) := by
      apply Finset.sum_le_sum
      intro x hx
      have hblock := (hQ.submatrix (fun y ↦ (x, y))).conjTranspose_mul_mul_same T
      rw [hT.eq] at hblock
      exact smul_le_smul_of_nonneg_right (hpX x hx) hblock.nonneg
    _ = cX • (T * (∑ x ∈ E, restoringBlock Q x) * T) := by
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
    _ ≤ _ := smul_le_smul_of_nonneg_left
      (compression_mono (block_sum_le_partialTrace hQ E) hT) hcX

/-- The three typical spectral inequalities control the actual matrix `B_Y`.
The matrix in the third hypothesis is the actual marginal `tr_X ρ`.
Source: `09-amplification.tex`, lines 374–395. -/
theorem restoringGram_le [DecidableEq Y] (E : Finset X) (p : X → ℝ)
    {ρ Q : Matrix (X × Y) (X × Y) ℂ} {T : Matrix Y Y ℂ}
    (hQ : IsStarProjection Q) (hT : IsStarProjection T)
    {cX cQ cY : ℝ} (hcX : 0 ≤ cX) (hcQ : 0 ≤ cQ) (hcY : 0 ≤ cY)
    (hpX : ∀ x ∈ E, (p x)⁻¹ ≤ cX) (hQρ : Q ≤ cQ • ρ)
    (hρY : T * partialTraceLeft ρ * T ≤ cY • T) :
    restoringGram E p Q T ≤ (cX * cQ * cY) • (1 : Matrix Y Y ℂ) := by
  have htrace : partialTraceLeft Q ≤ cQ • partialTraceLeft ρ := by
    have hp := (Matrix.le_iff.mp hQρ).partialTraceLeft
    apply Matrix.le_iff.mpr
    convert hp using 1
    ext i j
    simp [partialTraceLeft_apply, Finset.sum_sub_distrib, Finset.smul_sum]
  calc
    _ ≤ cX • (T * partialTraceLeft Q * T) :=
      restoringGram_le_compressed_partialTrace E p hQ.nonneg.posSemidef
        hT.isSelfAdjoint hcX hpX
    _ ≤ cX • (T * (cQ • partialTraceLeft ρ) * T) :=
      smul_le_smul_of_nonneg_left (compression_mono htrace hT.isSelfAdjoint) hcX
    _ = (cX * cQ) • (T * partialTraceLeft ρ * T) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    _ ≤ (cX * cQ) • (cY • T) :=
      smul_le_smul_of_nonneg_left hρY (mul_nonneg hcX hcQ)
    _ = (cX * cQ * cY) • T := by rw [smul_smul]
    _ ≤ _ := smul_le_smul_of_nonneg_left hT.le_one (mul_nonneg (mul_nonneg hcX hcQ) hcY)

/-- A unit blank vector has an orthogonal outer-product projection. The unit
condition uses the Euclidean norm on the vector. -/
theorem blankOuterProduct_isStarProjection (b : X → ℂ)
    (hb : ‖(WithLp.toLp 2 b : EuclideanSpace ℂ X)‖ = 1) :
    IsStarProjection (blankOuterProduct b) where
  isIdempotentElem := by
    have hunit : star b ⬝ᵥ b = 1 := by
      have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 b)
      simpa only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, hb,
        RCLike.ofReal_one, one_pow] using h
    change vecMulVec b (star b) * vecMulVec b (star b) = vecMulVec b (star b)
    simp only [vecMulVec_mul_vecMulVec, hunit, one_smul]
  isSelfAdjoint := (posSemidef_vecMulVec_self_star b).isHermitian

private theorem kronecker_le_smul_one {M N : Type*}
    [Finite M] [DecidableEq M] [Finite N] [DecidableEq N]
    {A : Matrix M M ℂ} {B : Matrix N N ℂ} (hA : A ≤ 1)
    (hB : B.PosSemidef) {c : ℝ} (hBc : B ≤ c • (1 : Matrix N N ℂ)) :
    A ⊗ₖ B ≤ c • (1 : Matrix (M × N) (M × N) ℂ) := by
  have h₁ : A ⊗ₖ B ≤ (1 : Matrix M M ℂ) ⊗ₖ B := by
    exact Matrix.le_iff.mpr (by
      convert (Matrix.le_iff.mp hA).kronecker hB using 1
      ext i j
      simp only [Matrix.sub_apply, kroneckerMap_apply, sub_mul])
  have h₂ : (1 : Matrix M M ℂ) ⊗ₖ B ≤
      (1 : Matrix M M ℂ) ⊗ₖ (c • (1 : Matrix N N ℂ)) := by
    exact Matrix.le_iff.mpr (by
      convert (PosSemidef.one : (1 : Matrix M M ℂ).PosSemidef).kronecker
        (Matrix.le_iff.mp hBc) using 1
      ext i j
      simp only [Matrix.sub_apply, kroneckerMap_apply, mul_sub])
  exact (h₁.trans h₂).trans_eq (by rw [kronecker_smul, one_kronecker_one])

private theorem norm_le_sqrt_of_gram_le {N : Type*} [Fintype N] [DecidableEq N]
    (A : Matrix N N ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hA : Aᴴ * A ≤ c • (1 : Matrix N N ℂ)) : ‖A‖ ≤ Real.sqrt c := by
  have hnorm : ‖Aᴴ * A‖ ≤ c :=
    (CStarAlgebra.norm_le_iff_le_algebraMap _ hc
      (posSemidef_conjTranspose_mul_self A).nonneg).mpr (by
        simpa only [Algebra.algebraMap_eq_smul_one] using hA)
  rw [← star_eq_conjTranspose, CStarRing.norm_star_mul_self] at hnorm
  exact (Real.le_sqrt (norm_nonneg A) hc).mpr (by simpa only [pow_two] using hnorm)


/-- The actual restoring operator is bounded by the square root of the three
spectral constants. Blank vectors are arbitrary Euclidean unit vectors.
Source: `eq:amplification-operator-norm`, lines 374–395. -/
theorem restoringOperator_norm_le [DecidableEq X] [DecidableEq Y]
    (E : Finset X) (p : X → ℝ) (hp : ∀ x ∈ E, 0 < p x)
    (sBlank xBlank : X → ℂ)
    (hs : ‖(WithLp.toLp 2 sBlank : EuclideanSpace ℂ X)‖ = 1)
    (hx : ‖(WithLp.toLp 2 xBlank : EuclideanSpace ℂ X)‖ = 1)
    {ρ Q : Matrix (X × Y) (X × Y) ℂ} {T : Matrix Y Y ℂ}
    (hQ : IsStarProjection Q) (hT : IsStarProjection T)
    {cX cQ cY : ℝ} (hcX : 0 ≤ cX) (hcQ : 0 ≤ cQ) (hcY : 0 ≤ cY)
    (hpX : ∀ x ∈ E, (p x)⁻¹ ≤ cX) (hQρ : Q ≤ cQ • ρ)
    (hρY : T * partialTraceLeft ρ * T ≤ cY • T) :
    ‖restoringOperator E p sBlank xBlank Q T‖ ≤ Real.sqrt (cX * cQ * cY) := by
  apply norm_le_sqrt_of_gram_le _ (mul_nonneg (mul_nonneg hcX hcQ) hcY)
  rw [restoringOperator_gram E p hp sBlank xBlank hQ.isSelfAdjoint
    hQ.isIdempotentElem.eq hT.isSelfAdjoint]
  have hB := restoringGram_posSemidef E p hp hQ.nonneg.posSemidef hT.isSelfAdjoint
  have hBc := restoringGram_le E p hQ hT hcX hcQ hcY hpX hQρ hρY
  have hxb := kronecker_le_smul_one (blankOuterProduct_isStarProjection xBlank hx).le_one
    hB hBc
  exact kronecker_le_smul_one (blankOuterProduct_isStarProjection sBlank hs).le_one
    ((posSemidef_vecMulVec_self_star xBlank).kronecker hB) hxb

/-- The actual full-basis column operator obeys the same operator norm bound.
The full basis still includes all zero-probability coordinates.
Source: `eq:amplification-operator-norm`, lines 374–395. -/
theorem columnOperator_norm_le [DecidableEq X] [DecidableEq Y]
    (E : Finset X) (p : X → ℝ) (hp : ∀ x ∈ E, 0 < p x)
    (sBlank eBlank : X → ℂ)
    (hs : ‖(WithLp.toLp 2 sBlank : EuclideanSpace ℂ X)‖ = 1)
    (he : ‖(WithLp.toLp 2 eBlank : EuclideanSpace ℂ X)‖ = 1)
    {ρ Q : Matrix (X × Y) (X × Y) ℂ} {T : Matrix Y Y ℂ}
    (hQ : IsStarProjection Q) (hT : IsStarProjection T)
    {cX cQ cY : ℝ} (hcX : 0 ≤ cX) (hcQ : 0 ≤ cQ) (hcY : 0 ≤ cY)
    (hpX : ∀ x ∈ E, (p x)⁻¹ ≤ cX) (hQρ : Q ≤ cQ • ρ)
    (hρY : T * partialTraceLeft ρ * T ≤ cY • T) :
    ‖columnOperator E p sBlank eBlank Q T‖ ≤ Real.sqrt (cX * cQ * cY) := by
  apply norm_le_sqrt_of_gram_le _ (mul_nonneg (mul_nonneg hcX hcQ) hcY)
  rw [columnOperator_gram E p hp sBlank eBlank hQ.isSelfAdjoint
    hQ.isIdempotentElem.eq hT.isSelfAdjoint]
  have hB := restoringGram_posSemidef E p hp hQ.nonneg.posSemidef hT.isSelfAdjoint
  have hBc := restoringGram_le E p hQ hT hcX hcQ hcY hpX hQρ hρY
  have hse : blankOuterProduct sBlank ⊗ₖ blankOuterProduct eBlank ≤ 1 := by
    simpa only [one_smul, blankOuterProduct] using kronecker_le_smul_one
      (blankOuterProduct_isStarProjection sBlank hs).le_one
      (posSemidef_vecMulVec_self_star eBlank)
      (show blankOuterProduct eBlank ≤ (1 : ℝ) • (1 : Matrix X X ℂ) by
        simpa only [one_smul] using (blankOuterProduct_isStarProjection eBlank he).le_one)
  exact kronecker_le_smul_one hse
    ((PosSemidef.one : (1 : Matrix X X ℂ).PosSemidef).kronecker hB)
    (kronecker_le_smul_one (le_refl (1 : Matrix X X ℂ)) hB hBc)

/-- The source constants give exactly `exp ((I + 3w) / 2)`, where
`I = S(X) + S(XY) - S(Y)`. No extra constant enters the norm estimate.
Source: `eq:amplification-operator-norm`, lines 385–397. -/
theorem restoringOperators_norm_le_exp [DecidableEq X] [DecidableEq Y]
    (E : Finset X) (p : X → ℝ) (hp : ∀ x ∈ E, 0 < p x)
    (sBlank xBlank eBlank : X → ℂ)
    (hs : ‖(WithLp.toLp 2 sBlank : EuclideanSpace ℂ X)‖ = 1)
    (hx : ‖(WithLp.toLp 2 xBlank : EuclideanSpace ℂ X)‖ = 1)
    (he : ‖(WithLp.toLp 2 eBlank : EuclideanSpace ℂ X)‖ = 1)
    {ρ Q : Matrix (X × Y) (X × Y) ℂ} {T : Matrix Y Y ℂ}
    (hQ : IsStarProjection Q) (hT : IsStarProjection T)
    (SX SXY SY w I : ℝ) (hI : I = SX + SXY - SY)
    (hpX : ∀ x ∈ E, (p x)⁻¹ ≤ Real.exp (SX + w))
    (hQρ : Q ≤ Real.exp (SXY + w) • ρ)
    (hρY : T * partialTraceLeft ρ * T ≤ Real.exp (-SY + w) • T) :
    ‖restoringOperator E p sBlank xBlank Q T‖ ≤ Real.exp ((I + 3 * w) / 2) ∧
      ‖columnOperator E p sBlank eBlank Q T‖ ≤ Real.exp ((I + 3 * w) / 2) := by
  have hconstant : Real.sqrt (Real.exp (SX + w) * Real.exp (SXY + w) *
      Real.exp (-SY + w)) = Real.exp ((I + 3 * w) / 2) := by
    apply (Real.sqrt_eq_iff_eq_sq
      (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        (Real.exp_pos _).le) (Real.exp_pos _).le).mpr
    rw [← Real.exp_add, ← Real.exp_add, sq, ← Real.exp_add]
    congr 1
    rw [hI]
    ring
  constructor
  · rw [← hconstant]
    exact restoringOperator_norm_le E p hp sBlank xBlank hs hx hQ hT
      (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
      (le_of_lt (Real.exp_pos _)) hpX hQρ hρY
  · rw [← hconstant]
    exact columnOperator_norm_le E p hp sBlank eBlank hs he hQ hT
      (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
      (le_of_lt (Real.exp_pos _)) hpX hQρ hρY

end Entropy
