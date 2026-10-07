/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.TypicalDensity
import QICLean.Entropy.ConditionalEntropy
import QICLean.Entropy.PurificationSplitting
import QICLean.Entropy.Bipartite

/-!
# Typical spectral restrictions of bipartite pure states

Orthogonal projection onto a selected family of marginal eigenvectors,
followed by normalization, gives the typical Schmidt truncation. Both
marginals are computed directly from this vector.

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
Provenance-ID: 8753-qic-typical-pure-state-01
Downstream declaration:
Matrix.leftFilteredVector
Provenance-ID: 8753-qic-typical-pure-state-02
Downstream declaration:
Matrix.leftFilteredVector_eq_kronecker
Provenance-ID: 8753-qic-typical-pure-state-03
Downstream declaration:
Matrix.partialTraceLeft_projection_split
Provenance-ID: 8753-qic-typical-pure-state-04
Downstream declaration:
Matrix.typicalPureState
Provenance-ID: 8753-qic-typical-pure-state-05
Downstream declaration:
Matrix.partialTraceRight_typicalPureState
Provenance-ID: 8753-qic-typical-pure-state-06
Downstream declaration:
Matrix.norm_typicalPureState
Provenance-ID: 8753-qic-typical-pure-state-07
Downstream declaration:
Matrix.inner_typicalPureState
Provenance-ID: 8753-qic-typical-pure-state-08
Downstream declaration:
Matrix.norm_sub_typicalPureState_sq
Provenance-ID: 8753-qic-typical-pure-state-09
Downstream declaration:
Matrix.norm_sub_typicalPureState_sq_le
Provenance-ID: 8753-qic-typical-pure-state-10
Downstream declaration:
Matrix.partialTraceLeft_typicalPureState
Provenance-ID: 8753-qic-typical-pure-state-11
Downstream declaration:
Matrix.partialTraceLeft_typicalPureState_decomposition
Provenance-ID: 8753-qic-typical-pure-state-12
Downstream declaration:
Matrix.partialTraceLeft_typicalPureState_le
Provenance-ID: 8753-qic-typical-pure-state-13
Downstream declaration:
Matrix.entropy_partialTraceLeft_typicalPureState_le
Provenance-ID: 8753-qic-typical-pure-state-14
Downstream declaration:
Matrix.partialTraceRight_partialTraceLeft_typicalPureState_decomposition
Provenance-ID: 8753-qic-typical-pure-state-15
Downstream declaration:
Matrix.partialTraceRight_partialTraceLeft_typicalPureState_le
Provenance-ID: 8753-qic-typical-pure-state-16
Downstream declaration:
Matrix.entropy_partialTraceRight_partialTraceLeft_typicalPureState_le
-/

open scoped BigOperators Matrix ComplexOrder InnerProductSpace Kronecker

noncomputable section

namespace Matrix

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

omit [Fintype B] [DecidableEq B] in
private theorem gram_projection_split (C : Matrix A B ℂ) {P : Matrix A A ℂ}
    (hP : IsStarProjection P) :
    Cᴴ * C = (P * C)ᴴ * (P * C) + ((1 - P) * C)ᴴ * ((1 - P) * C) := by
  rw [conjTranspose_mul, conjTranspose_mul]
  simp only [show Pᴴ = P from hP.isSelfAdjoint,
    show (1 - P)ᴴ = 1 - P from hP.one_sub.isSelfAdjoint,
    Matrix.mul_assoc, ← Matrix.mul_assoc P P C, hP.isIdempotentElem.eq,
    ← Matrix.mul_assoc (1 - P) (1 - P) C, hP.one_sub.isIdempotentElem.eq,
    ← Matrix.mul_add, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]

/-- Applying a matrix on the first tensor factor of a bipartite vector.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
def leftFilteredVector (P : Matrix A A ℂ) (ψ : EuclideanSpace ℂ (A × B)) :
    EuclideanSpace ℂ (A × B) :=
  WithLp.toLp 2 (fun x ↦ (P * schmidtCoeffMatrix ψ) x.1 x.2)

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
private theorem schmidtCoeffMatrix_leftFilteredVector (P : Matrix A A ℂ)
    (ψ : EuclideanSpace ℂ (A × B)) :
    schmidtCoeffMatrix (leftFilteredVector P ψ) = P * schmidtCoeffMatrix ψ := rfl

omit [DecidableEq A] in
/-- The coefficient-matrix action equals the physical action on the first
tensor factor. OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem leftFilteredVector_eq_kronecker (P : Matrix A A ℂ)
    (ψ : EuclideanSpace ℂ (A × B)) :
    leftFilteredVector P ψ = WithLp.toLp 2 ((P ⊗ₖ (1 : Matrix B B ℂ)) *ᵥ ψ) := by
  ext x
  simp [leftFilteredVector, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    schmidtCoeffMatrix_apply]

omit [Fintype B] [DecidableEq B] in
/-- Tracing the first factor removes the cross terms between orthogonal selected
and discarded subspaces. OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem partialTraceLeft_projection_split (ψ : EuclideanSpace ℂ (A × B))
    {P : Matrix A A ℂ} (hP : IsStarProjection P) :
    partialTraceLeft (vecMulVec ψ (star ψ)) =
      partialTraceLeft (vecMulVec (leftFilteredVector P ψ) (star (leftFilteredVector P ψ))) +
      partialTraceLeft (vecMulVec (leftFilteredVector (1 - P) ψ)
        (star (leftFilteredVector (1 - P) ψ))) := by
  simp only [Entropy.partialTraceLeft_vecMulVec_eq_map_conj,
    schmidtCoeffMatrix_leftFilteredVector]
  rw [gram_projection_split (schmidtCoeffMatrix ψ) hP]
  exact Matrix.map_add (starRingEnd ℂ) (starRingEnd ℂ).map_add _ _

omit [DecidableEq A] [DecidableEq B] in
private theorem partialTraceRight_leftFilteredVector (P : Matrix A A ℂ)
    (ψ : EuclideanSpace ℂ (A × B)) :
    partialTraceRight (vecMulVec (leftFilteredVector P ψ) (star (leftFilteredVector P ψ))) =
      P * partialTraceRight (vecMulVec ψ (star ψ)) * Pᴴ := by
  simp only [partialTraceRight_vecMulVec_eq, schmidtCoeffMatrix_leftFilteredVector,
    conjTranspose_mul, Matrix.mul_assoc]

private theorem entropy_sub_negMulLog_trace_nonneg {R : Matrix B B ℂ} (hR : R.PosSemidef) :
    0 ≤ vonNeumannEntropy R hR.isHermitian - Real.negMulLog R.trace.re := by
  by_cases ht : R.trace.re = 0
  · have hzero : R = 0 := hR.eq_zero_of_re_trace_eq_zero ht
    subst R
    simp
  · have htpos : 0 < R.trace.re := lt_of_le_of_ne hR.re_trace_nonneg (Ne.symm ht)
    let σ := R.trace.re⁻¹ • R
    have hσ : σ.PosSemidef := hR.smul (inv_nonneg.mpr htpos.le)
    have hσtr : σ.trace = 1 := by
      rw [show σ.trace = (R.trace.re⁻¹ : ℂ) * R.trace from by simp [σ, trace_smul]]
      rw [hR.trace_eq_ofReal_re, Complex.ofReal_re,
        inv_mul_cancel₀ (by exact_mod_cast ht)]
    have hback : R.trace.re • σ = R := by simp [σ, smul_smul, ht]
    have hs := vonNeumannEntropy_real_smul R.trace.re hσ.isHermitian
      (hσ.smul htpos.le).isHermitian
    rw [vonNeumannEntropy_congr hback _ hR.isHermitian, hσtr, Complex.one_re, mul_one] at hs
    linarith [mul_nonneg htpos.le (vonNeumannEntropy_nonneg_of_posSemidef_trace_one hσ hσtr)]

private theorem normalized_entropy_le_of_sum {M R : Matrix B B ℂ}
    (hM : M.PosSemidef) (hR : R.PosSemidef) (htr : (M + R).trace = 1)
    (hz : 0 < M.trace.re) :
    M.trace.re * vonNeumannEntropy (M.trace.re⁻¹ • M)
        (hM.smul (inv_nonneg.mpr hz.le)).isHermitian ≤
      vonNeumannEntropy (M + R) (hM.add hR).isHermitian := by
  have hc := Entropy.sum_vonNeumannEntropy_sub_negMulLog_le
    (fun b : Bool ↦ cond b M R) (fun b ↦ Bool.rec hR hM b)
  simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, htr, Complex.one_re,
    Real.negMulLog_one, sub_zero] at hc
  let σ := M.trace.re⁻¹ • M
  have hσ : σ.PosSemidef := hM.smul (inv_nonneg.mpr hz.le)
  have hσtr : σ.trace = 1 := by
    rw [show σ.trace = (M.trace.re⁻¹ : ℂ) * M.trace from by simp [σ, trace_smul]]
    rw [hM.trace_eq_ofReal_re, Complex.ofReal_re,
      inv_mul_cancel₀ (by exact_mod_cast hz.ne')]
  have hback : M.trace.re • σ = M := by simp [σ, smul_smul, hz.ne']
  have hs := vonNeumannEntropy_real_smul M.trace.re hσ.isHermitian (hσ.smul hz.le).isHermitian
  rw [vonNeumannEntropy_congr hback _ hM.isHermitian, hσtr, Complex.one_re, mul_one] at hs
  linarith [entropy_sub_negMulLog_trace_nonneg hR]

private theorem trace_spectralCompression {ρ : Matrix A A ℂ} (hρ : ρ.IsHermitian)
    (E : Finset A) (hz : hρ.spectralRestrictionMass E ≠ 0) :
    (hρ.spectralSelection E * ρ * hρ.spectralSelection E).trace =
      (hρ.spectralRestrictionMass E : ℂ) := by
  have h := hρ.trace_normalizedSpectralRestriction E hz
  rw [hρ.normalizedSpectralRestriction_eq, trace_smul, smul_eq_mul] at h
  simpa using (inv_mul_eq_iff_eq_mul₀ (by exact_mod_cast hz)).mp h

section Typical

variable (ψ : EuclideanSpace ℂ (A × B)) (E : Finset A)

local notation "ρA" => partialTraceRight (vecMulVec ψ (star ψ))
local notation "hρA" => Matrix.PosSemidef.partialTraceRight (posSemidef_vecMulVec_self_star ψ)
local notation "zE" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian hρA) E
local notation "PE" => Matrix.IsHermitian.spectralSelection
  (Matrix.PosSemidef.isHermitian hρA) E

/-- The normalized selected Schmidt vector, on the original bipartite space.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
def typicalPureState : EuclideanSpace ℂ (A × B) :=
  (Real.sqrt zE : ℂ)⁻¹ • leftFilteredVector PE ψ

omit [DecidableEq B] in
private theorem trace_leftFiltered_spectralSelection (hz : zE ≠ 0) :
    (partialTraceRight (vecMulVec (leftFilteredVector PE ψ)
      (star (leftFilteredVector PE ψ)))).trace = (zE : ℂ) := by
  rw [partialTraceRight_leftFilteredVector,
    show PEᴴ = PE from ((hρA).isHermitian.isStarProjection_spectralSelection E).isSelfAdjoint]
  exact trace_spectralCompression (hρA).isHermitian E hz

omit [DecidableEq B] in
private theorem pureMatrix_typicalPureState (hz : 0 < zE) :
    vecMulVec (typicalPureState ψ E) (star (typicalPureState ψ E)) =
      (zE : ℂ)⁻¹ • vecMulVec (leftFilteredVector PE ψ) (star (leftFilteredVector PE ψ)) := by
  simp only [typicalPureState, WithLp.ofLp_smul, star_smul,
    Complex.star_def, map_inv₀, Complex.conj_ofReal,
    smul_vecMulVec, vecMulVec_smul, smul_smul]
  rw [← mul_inv, ← sq, ← Complex.ofReal_pow, Real.sq_sqrt hz.le]

omit [DecidableEq B] in
/-- The actual first marginal of the selected pure vector is the normalized
spectral restriction. OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem partialTraceRight_typicalPureState (hz : 0 < zE) :
    partialTraceRight (vecMulVec (typicalPureState ψ E) (star (typicalPureState ψ E))) =
      (hρA).isHermitian.normalizedSpectralRestriction E := by
  rw [pureMatrix_typicalPureState ψ E hz, partialTraceRight_smul,
    partialTraceRight_leftFilteredVector,
    show PEᴴ = PE from ((hρA).isHermitian.isStarProjection_spectralSelection E).isSelfAdjoint,
    (hρA).isHermitian.normalizedSpectralRestriction_eq]

omit [DecidableEq B] in
/-- A positive-mass typical Schmidt truncation is a unit vector.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem norm_typicalPureState (hz : 0 < zE) : ‖typicalPureState ψ E‖ = 1 := by
  have ht := (hρA).isHermitian.trace_normalizedSpectralRestriction E hz.ne'
  have hs := norm_toLp_sq (typicalPureState ψ E : A × B → ℂ)
  rw [WithLp.toLp_ofLp, ← trace_partialTraceRight_vecMulVec,
    partialTraceRight_typicalPureState ψ E hz, ht, Complex.one_re] at hs
  nlinarith [norm_nonneg (typicalPureState ψ E)]

omit [DecidableEq B] in
private theorem star_dotProduct_leftFiltered_spectralSelection (hz : zE ≠ 0) :
    star (ψ : A × B → ℂ) ⬝ᵥ (leftFilteredVector PE ψ : A × B → ℂ) = (zE : ℂ) := by
  rw [star_dotProduct_eq_trace_conjTranspose_mul, schmidtCoeffMatrix_leftFilteredVector]
  rw [← Matrix.mul_assoc, trace_mul_cycle]
  have ht := trace_spectralCompression (hρA).isHermitian E hz
  rw [trace_mul_cycle, ((hρA).isHermitian.isStarProjection_spectralSelection E).isIdempotentElem.eq,
    trace_mul_comm] at ht
  simpa only [partialTraceRight_vecMulVec_eq] using ht

omit [DecidableEq B] in
/-- The overlap with the normalized selected vector is the square root of the
selected mass. OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem inner_typicalPureState (hz : 0 < zE) :
    ⟪ψ, typicalPureState ψ E⟫_ℂ = (Real.sqrt zE : ℂ) := by
  rw [typicalPureState, inner_smul_right, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct_comm, star_dotProduct_leftFiltered_spectralSelection ψ E hz.ne']
  norm_cast
  exact (inv_mul_eq_iff_eq_mul₀ (Real.sqrt_pos.mpr hz).ne').mpr (Real.mul_self_sqrt hz.le).symm

omit [DecidableEq B] in
/-- The exact squared vector error of typical Schmidt truncation.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem norm_sub_typicalPureState_sq (hψ : ‖ψ‖ = 1) (hz : 0 < zE) :
    ‖ψ - typicalPureState ψ E‖ ^ 2 = 2 * (1 - Real.sqrt zE) := by
  rw [@norm_sub_sq ℂ, hψ, norm_typicalPureState ψ E hz,
    inner_typicalPureState ψ E hz, RCLike.re_eq_complex_re, Complex.ofReal_re]
  ring

omit [DecidableEq A] [DecidableEq B] in
private theorem trace_pure_of_norm_one (hψ : ‖ψ‖ = 1) :
    (vecMulVec ψ (star ψ)).trace = 1 := by
  change ⟪ψ, ψ⟫_ℂ = 1
  simp [hψ]

omit [DecidableEq B] in
/-- The squared vector error is at most twice the discarded mass.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem norm_sub_typicalPureState_sq_le (hψ : ‖ψ‖ = 1) (hz : 0 < zE) :
    ‖ψ - typicalPureState ψ E‖ ^ 2 ≤ 2 * (1 - zE) := by
  have hz1 := (hρA).spectralRestrictionMass_le_one
    (by rw [trace_partialTraceRight, trace_pure_of_norm_one ψ hψ]) E
  have hs : zE ≤ Real.sqrt zE :=
    (Real.le_sqrt hz.le hz.le).mpr (by nlinarith)
  linarith [norm_sub_typicalPureState_sq ψ E hψ hz]

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
private theorem partialTraceLeft_complex_smul (c : ℂ)
    (X : Matrix (A × B) (A × B) ℂ) :
    partialTraceLeft (c • X) = c • partialTraceLeft X := by
  ext i j
  simp [partialTraceLeft_apply, Matrix.smul_apply, Finset.mul_sum]

local notation "ρB" => partialTraceLeft (vecMulVec ψ (star ψ))
local notation "σB" => partialTraceLeft
  (vecMulVec (typicalPureState ψ E) (star (typicalPureState ψ E)))
local notation "RB" => partialTraceLeft
  (vecMulVec (leftFilteredVector (1 - PE) ψ) (star (leftFilteredVector (1 - PE) ψ)))
local notation "MB" => partialTraceLeft
  (vecMulVec (leftFilteredVector PE ψ) (star (leftFilteredVector PE ψ)))

omit [DecidableEq B] in
/-- The actual complementary marginal is the normalized marginal of the selected
unnormalized vector. OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem partialTraceLeft_typicalPureState (hz : 0 < zE) : σB = zE⁻¹ • MB := by
  change σB = ((zE⁻¹ : ℝ) : ℂ) • MB
  rw [Complex.ofReal_inv, pureMatrix_typicalPureState ψ E hz, partialTraceLeft_complex_smul]

omit [DecidableEq B] in
/-- The actual complementary marginal is the sum of the selected and discarded
marginals. OpenAI area-law manuscript, `comparator:post-marginal`. The discarded
term remains unnormalized, so the formula also covers selected mass one. -/
theorem partialTraceLeft_typicalPureState_decomposition (hz : 0 < zE) :
    ρB = zE • σB + RB := by
  change ρB = (zE : ℂ) • σB + RB
  rw [partialTraceLeft_projection_split ψ
    ((hρA).isHermitian.isStarProjection_spectralSelection E),
    pureMatrix_typicalPureState ψ E hz, partialTraceLeft_complex_smul,
    smul_smul, mul_inv_cancel₀ (show (zE : ℂ) ≠ 0 from by exact_mod_cast hz.ne'), one_smul]

omit [DecidableEq B] in
/-- The normalized selected complementary marginal is bounded above by the
original marginal divided by the selected mass, in positive-semidefinite order.
OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem partialTraceLeft_typicalPureState_le (hz : 0 < zE) :
    (zE⁻¹ • ρB - σB).PosSemidef := by
  rw [partialTraceLeft_typicalPureState_decomposition ψ E hz,
    smul_add, smul_smul, inv_mul_cancel₀ hz.ne', one_smul, add_sub_cancel_left]
  exact (posSemidef_vecMulVec_self_star (leftFilteredVector (1 - PE) ψ)).partialTraceLeft.smul
    (inv_nonneg.mpr hz.le)

/-- Entropy of the actual selected complementary marginal is at most the original
entropy divided by the selected mass. OpenAI area-law manuscript,
`comparator:post-marginal`. -/
theorem entropy_partialTraceLeft_typicalPureState_le (hψ : ‖ψ‖ = 1) (hz : 0 < zE) :
    vonNeumannEntropy σB
        (posSemidef_vecMulVec_self_star (typicalPureState ψ E)).partialTraceLeft.isHermitian ≤
      vonNeumannEntropy ρB
        (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian / zE := by
  have hsplit := partialTraceLeft_projection_split ψ
    ((hρA).isHermitian.isStarProjection_spectralSelection E)
  have ht : (MB).trace.re = zE := by
    rw [trace_partialTraceLeft, ← trace_partialTraceRight,
      trace_leftFiltered_spectralSelection ψ E hz.ne', Complex.ofReal_re]
  have hc := normalized_entropy_le_of_sum
    (posSemidef_vecMulVec_self_star (leftFilteredVector PE ψ)).partialTraceLeft
    (posSemidef_vecMulVec_self_star (leftFilteredVector (1 - PE) ψ)).partialTraceLeft
    (by rw [← hsplit, trace_partialTraceLeft, trace_pure_of_norm_one ψ hψ])
    (by simpa only [ht] using hz)
  simp only [ht] at hc
  apply (le_div_iff₀ hz).mpr
  rw [mul_comm]
  simpa only [← hsplit, ← partialTraceLeft_typicalPureState ψ E hz] using hc

end Typical

section ComplementarySubsystem

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (ψ : EuclideanSpace ℂ (A × (B × C))) (E : Finset A)

local notation "ρA" => partialTraceRight (vecMulVec ψ (star ψ))
local notation "hρA" => Matrix.PosSemidef.partialTraceRight (posSemidef_vecMulVec_self_star ψ)
local notation "zE" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian hρA) E
local notation "PE" => Matrix.IsHermitian.spectralSelection
  (Matrix.PosSemidef.isHermitian hρA) E
local notation "ρB" => partialTraceRight (partialTraceLeft (vecMulVec ψ (star ψ)))
local notation "σB" => partialTraceRight (partialTraceLeft
  (vecMulVec (typicalPureState ψ E) (star (typicalPureState ψ E))))
local notation "RB" => partialTraceRight (partialTraceLeft
  (vecMulVec (leftFilteredVector (1 - PE) ψ) (star (leftFilteredVector (1 - PE) ψ))))
local notation "MB" => partialTraceRight (partialTraceLeft
  (vecMulVec (leftFilteredVector PE ψ) (star (leftFilteredVector PE ψ))))

omit [DecidableEq B] [DecidableEq C] in
/-- The actual marginal on any factor of the complement splits into selected and
discarded contributions. OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem partialTraceRight_partialTraceLeft_typicalPureState_decomposition (hz : 0 < zE) :
    ρB = zE • σB + RB := by
  have hs := congrArg partialTraceRight
    (partialTraceLeft_typicalPureState_decomposition ψ E hz)
  simpa only [partialTraceRight_add, partialTraceRight_real_smul] using hs

omit [DecidableEq B] [DecidableEq C] in
/-- The actual selected marginal on a factor of the complement is bounded by the
original marginal divided by the selected mass, in positive-semidefinite order.
OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem partialTraceRight_partialTraceLeft_typicalPureState_le (hz : 0 < zE) :
    (zE⁻¹ • ρB - σB).PosSemidef := by
  rw [partialTraceRight_partialTraceLeft_typicalPureState_decomposition ψ E hz,
    smul_add, smul_smul, inv_mul_cancel₀ hz.ne', one_smul, add_sub_cancel_left]
  have hR := posSemidef_vecMulVec_self_star (leftFilteredVector (1 - PE) ψ)
  exact hR.partialTraceLeft.partialTraceRight.smul (inv_nonneg.mpr hz.le)

omit [DecidableEq C] in
/-- Entropy of the actual selected marginal on any factor of the complement is
bounded by the original marginal entropy divided by the selected mass.
OpenAI area-law manuscript, `comparator:post-marginal`. -/
theorem entropy_partialTraceRight_partialTraceLeft_typicalPureState_le
    (hψ : ‖ψ‖ = 1) (hz : 0 < zE) :
    vonNeumannEntropy σB
        (posSemidef_vecMulVec_self_star
          (typicalPureState ψ E)).partialTraceLeft.partialTraceRight.isHermitian ≤
      vonNeumannEntropy ρB
        (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.partialTraceRight.isHermitian / zE := by
  have hsplit := congrArg partialTraceRight (partialTraceLeft_projection_split ψ
    ((hρA).isHermitian.isStarProjection_spectralSelection E))
  simp only [partialTraceRight_add] at hsplit
  have ht : (MB).trace.re = zE := by
    rw [trace_partialTraceRight, trace_partialTraceLeft, ← trace_partialTraceRight,
      trace_leftFiltered_spectralSelection ψ E hz.ne', Complex.ofReal_re]
  have hc := normalized_entropy_le_of_sum
    (posSemidef_vecMulVec_self_star (leftFilteredVector PE ψ)).partialTraceLeft.partialTraceRight
    (posSemidef_vecMulVec_self_star
      (leftFilteredVector (1 - PE) ψ)).partialTraceLeft.partialTraceRight
    (by rw [← hsplit, trace_partialTraceRight, trace_partialTraceLeft,
      trace_pure_of_norm_one ψ hψ])
    (by simpa only [ht] using hz)
  have hn : σB = zE⁻¹ • MB := by
    have hs := congrArg partialTraceRight (partialTraceLeft_typicalPureState ψ E hz)
    simpa only [partialTraceRight_real_smul] using hs
  simp only [ht] at hc
  apply (le_div_iff₀ hz).mpr
  rw [mul_comm]
  simpa only [← hsplit, ← hn] using hc

end ComplementarySubsystem

end Matrix
