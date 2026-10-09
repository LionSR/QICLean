/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.WeightedRectangular
import QICLean.Probability.MatrixSecondMoment
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Weighted corrected-source covariance and trace error

For a rectangular contraction on the full free input spaces, diagonal
coefficient covariance gives a dimension-independent expected trace error.
The block aggregation is proved from finite entry sums. Ordinary full
transpose preserves the coefficient, including its complex phase.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
Theorem 5.2, `eq:compression-block-second-moment`,
`eq:compression-dimension-free`, and `eq:compression-one-choice`,
`04-compression.tex:383–538`, immutable revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are original proofs. No OpenAI Lean code is copied or adapted.
The actual independent Gaussian covariance must be established before using
this generic covariance consumer in the complete density-compression theorem.
-/

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder ComplexConjugate

noncomputable section

namespace ProbabilityTheory

variable {I L T U : Type*} [Fintype I] [Fintype L] [Fintype T] [Fintype U]
  [DecidableEq I] [DecidableEq L] [DecidableEq T] [DecidableEq U]

/-- The `(l,i)` block of the full free-input contraction has ket columns `T`
and bra rows `U`. Source: `eq:compression-block-contraction`. -/
def sourceBlock (O : Matrix (L × U) (I × T) ℂ) (l : L) (i : I) : Matrix U T ℂ :=
  fun u t ↦ O (l, u) (i, t)

/-- Exterior-input error of a fixed expanded branch. The transpose is ordinary
full transpose, not an adjoint. Source: `eq:compression-exterior-input`. -/
def weightedSourceError (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (L × U) (I × T) ℂ) (z : I × L → ℂ) : Matrix T U ℂ :=
  ∑ b, z b • Matrix.halfWeighted tau tau' (sourceBlock O b.2 b.1)ᵀ

/-- The quarter-weighted block combination controlling the source error.
Source: the transpose step after `eq:compression-quarter-powers`. -/
def weightedSourceQuarter (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (L × U) (I × T) ℂ) (z : I × L → ℂ) : Matrix U T ℂ :=
  ∑ b, z b • Matrix.quarterWeighted tau' tau (sourceBlock O b.2 b.1)

omit [DecidableEq I] [DecidableEq L] in
/-- Square-root weighted source sums are linear in the free coefficient
matrix; no complex coefficient is conjugated. -/
theorem weightedSourceError_eq_halfWeighted
    (tau : T → ℝ) (tau' : U → ℝ) (O : Matrix (L × U) (I × T) ℂ) (z : I × L → ℂ) :
    weightedSourceError tau tau' O z =
      Matrix.halfWeighted tau tau' (∑ b, z b • (sourceBlock O b.2 b.1)ᵀ) := by
  ext t u
  simp only [weightedSourceError, Matrix.halfWeighted, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

omit [DecidableEq I] [DecidableEq L] in
/-- Ordinary transpose converts the quarter-weighted source sum to the
controlled ket-to-bra block combination, preserving every coefficient. -/
theorem quarterWeighted_source_sum_eq_transpose
    (tau : T → ℝ) (tau' : U → ℝ) (O : Matrix (L × U) (I × T) ℂ) (z : I × L → ℂ) :
    Matrix.quarterWeighted tau tau' (∑ b, z b • (sourceBlock O b.2 b.1)ᵀ) =
      (weightedSourceQuarter tau tau' O z)ᵀ := by
  ext t u
  simp only [weightedSourceQuarter, Matrix.quarterWeighted_apply, Matrix.transpose_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

omit [DecidableEq I] [DecidableEq L] in
/-- Pointwise dimension-independent trace/Hilbert--Schmidt comparison for the
source error. Source: `eq:compression-quarter-powers`. -/
theorem rectangularTraceNorm_weightedSourceError_le
    (tau : T → ℝ) (tau' : U → ℝ) (O : Matrix (L × U) (I × T) ℂ) (z : I × L → ℂ)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) :
    Matrix.rectangularTraceNorm (weightedSourceError tau tau' O z) ≤
      Real.sqrt (Matrix.frobeniusNormSq (weightedSourceQuarter tau tau' O z)) := by
  rw [weightedSourceError_eq_halfWeighted]
  have h := Matrix.rectangularTraceNorm_halfWeighted_le tau tau'
    (∑ b, z b • (sourceBlock O b.2 b.1)ᵀ) htau htau' htausum htau'sum
  rw [quarterWeighted_source_sum_eq_transpose] at h
  simpa only [Matrix.frobeniusNormSq, Matrix.frobenius_norm_transpose] using h

/-- Product probabilities on the complete free registers. Source: the
definition of `R` and `Rtilde` after `eq:compression-block-second-moment`. -/
def sourceProductProbability (p : I → ℝ) (tau : T → ℝ) : I × T → ℝ :=
  fun b ↦ p b.1 * tau b.2

omit [DecidableEq I] [DecidableEq T] in
/-- Product probabilities remain normalized, including zero probabilities. -/
theorem sum_sourceProductProbability
    (p : I → ℝ) (tau : T → ℝ) (hp : ∑ i, p i = 1) (htau : ∑ t, tau t = 1) :
    ∑ b, sourceProductProbability p tau b = 1 := by
  simp only [sourceProductProbability, Fintype.sum_prod_type, ← Finset.mul_sum,
    htau, mul_one, hp]

/-- Exact block aggregation into the Hilbert--Schmidt square on the full free
input spaces. Source: the equality preceding `eq:compression-dimension-free`.
The indices at the two corrected endpoints remain independent. -/
theorem weighted_source_block_aggregation
    (p : I → ℝ) (p' : L → ℝ) (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (L × U) (I × T) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hp' : ∀ l, 0 ≤ p' l)
    :
    ∑ b : I × L, Real.sqrt (p b.1 * p' b.2) *
        Matrix.frobeniusNormSq (Matrix.quarterWeighted tau' tau (sourceBlock O b.2 b.1)) =
      Matrix.frobeniusNormSq (Matrix.quarterWeighted
        (sourceProductProbability p' tau') (sourceProductProbability p tau) O) := by
  simp only [Matrix.frobeniusNormSq_quarterWeighted, sourceProductProbability,
    sourceBlock, Fintype.sum_prod_type, Real.sqrt_mul (hp _),
    Real.sqrt_mul (hp' _)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i l ↦ _)]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm (f := fun i u ↦ _)]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro t _
  ring

omit [DecidableEq L] in
/-- A rectangular full-register contraction bounds the variance-weighted
block sum with no input, private-memory, or discard dimension factor.
Source: `eq:compression-dimension-free`. -/
theorem weighted_source_block_sum_le_one
    (p : I → ℝ) (p' : L → ℝ) (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (L × U) (I × T) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hp' : ∀ l, 0 ≤ p' l)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (hpsum : ∑ i, p i = 1) (hp'sum : ∑ l, p' l = 1)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) (hO : ‖O‖ ≤ 1) :
    ∑ b : I × L, Real.sqrt (p b.1 * p' b.2) *
      Matrix.frobeniusNormSq (Matrix.quarterWeighted tau' tau (sourceBlock O b.2 b.1)) ≤ 1 := by
  classical
  rw [weighted_source_block_aggregation p p' tau tau' O hp hp']
  exact Matrix.frobeniusNormSq_quarterWeighted_le_one _ _ O
    (fun b ↦ mul_nonneg (hp' b.1) (htau' b.2))
    (fun b ↦ mul_nonneg (hp b.1) (htau b.2))
    (sum_sourceProductProbability p' tau' hp'sum htau'sum)
    (sum_sourceProductProbability p tau hpsum htausum) hO

open scoped Matrix.Norms.Frobenius in
private theorem sqrt_frobeniusNormSq {a b : Type*} [Fintype a] [Fintype b]
    (A : Matrix a b ℂ) : Real.sqrt (Matrix.frobeniusNormSq A) = ‖A‖ := by
  simp only [Matrix.frobeniusNormSq, Real.sqrt_sq_eq_abs, abs_norm]

variable {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω}

/-- Pairwise integrability supplies measurability of the nuclear norm, even
when a common coefficient phase is not measurable. The Gram matrix depends
only on the measurable pair products. Auxiliary to `eq:compression-one-choice`. -/
theorem aestronglyMeasurable_rectangularTraceNorm_sum
    {a b J : Type*} [Fintype a] [Fintype b] [Fintype J] [DecidableEq b]
    (z : J → Ω → ℂ)
    (hz : ∀ i j, Integrable (fun w ↦ z i w * conj (z j w)) mu)
    (A : J → Matrix a b ℂ) :
    AEStronglyMeasurable (fun w ↦ Matrix.rectangularTraceNorm (∑ i, z i w • A i)) mu := by
  classical
  let X : Ω → Matrix a b ℂ := fun w ↦ ∑ i, z i w • A i
  have hentry : ∀ r c, Integrable (fun w ↦ ((X w)ᴴ * X w) r c) mu := by
    intro r c
    have hsum : Integrable (fun w ↦ ∑ k, ∑ i, ∑ j,
        (z j w * conj (z i w)) * (conj (A i k r) * A j k c)) mu :=
      integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun i _ ↦
        integrable_finsetSum _ fun j _ ↦ (hz j i).mul_const _
    convert hsum using 1
    funext w
    simp only [X, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      simp only [RCLike.star_def]
      ring
  have hgram : AEMeasurable (fun w ↦ (X w)ᴴ * X w) mu :=
    aemeasurable_pi_iff.mpr fun r ↦ aemeasurable_pi_iff.mpr fun c ↦ (hentry r c).aemeasurable
  have hsqrt : AEMeasurable (fun w ↦ CFC.sqrt ((X w)ᴴ * X w)) mu :=
    CFC.measurable_sqrt.comp_aemeasurable hgram
  have hcont : Continuous (fun M : Matrix b b ℂ ↦ M.trace.re) := by
    simp only [Matrix.trace, Matrix.diag]
    fun_prop
  have htrace : AEStronglyMeasurable
      (fun w ↦ (CFC.sqrt ((X w)ᴴ * X w)).trace.re) mu :=
    (hcont.measurable.comp_aemeasurable hsqrt).aestronglyMeasurable
  apply htrace.congr
  filter_upwards [] with w
  have hH := Matrix.posSemidef_conjTranspose_mul_self (X w)
  rw [Matrix.rectangularTraceNorm_eq_sum_sqrt_eigenvalues, hH.sqrt_eq_cfc_real_sqrt]
  exact hH.isHermitian.trace_cfc_eq_sum_re Real.sqrt

omit [DecidableEq I] [DecidableEq L] in
/-- Pairwise coefficient integrability supplies integrability of the
Hilbert--Schmidt upper bound. Auxiliary to `eq:compression-one-choice`. -/
theorem integrable_weightedSourceQuarter_norm [IsProbabilityMeasure mu]
    (tau : T → ℝ) (tau' : U → ℝ) (O : Matrix (L × U) (I × T) ℂ)
    (z : I × L → Ω → ℂ)
    (hz : ∀ b c, Integrable (fun w ↦ z b w * conj (z c w)) mu) :
    Integrable (fun w ↦ Real.sqrt
      (Matrix.frobeniusNormSq (weightedSourceQuarter tau tau' O (fun b ↦ z b w)))) mu := by
  let f : Ω → ℝ := fun w ↦ Real.sqrt
    (Matrix.frobeniusNormSq (weightedSourceQuarter tau tau' O (fun b ↦ z b w)))
  have hsquare : Integrable (fun w ↦ f w ^ 2) mu := by
    simpa only [f, weightedSourceQuarter, sqrt_frobeniusNormSq] using
      integrable_frobenius_norm_sq_sum z hz
        (fun b ↦ Matrix.quarterWeighted tau' tau (sourceBlock O b.2 b.1))
  have hmeas : AEStronglyMeasurable f mu := by
    have h := Real.continuous_sqrt.comp_aestronglyMeasurable hsquare.aestronglyMeasurable
    simpa only [Function.comp_def, f, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using h
  have hLp : MemLp f 2 mu := (memLp_two_iff_integrable_sq hmeas).mpr hsquare
  exact hLp.integrable (by norm_num)

omit [DecidableEq I] [DecidableEq L] in
/-- The covariance-weighted block error has an integrable trace norm. This
rules out reliance on the integral's default value for a nonintegrable input.
Source: `eq:compression-one-choice`. -/
theorem integrable_rectangularTraceNorm_weightedSourceError [IsProbabilityMeasure mu]
    (tau : T → ℝ) (tau' : U → ℝ) (O : Matrix (L × U) (I × T) ℂ)
    (z : I × L → Ω → ℂ)
    (hz : ∀ b c, Integrable (fun w ↦ z b w * conj (z c w)) mu)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) :
    Integrable (fun w ↦ Matrix.rectangularTraceNorm
      (weightedSourceError tau tau' O (fun b ↦ z b w))) mu := by
  have hmeas := aestronglyMeasurable_rectangularTraceNorm_sum z hz
    (fun b ↦ Matrix.halfWeighted tau tau' (sourceBlock O b.2 b.1)ᵀ)
  refine (integrable_weightedSourceQuarter_norm tau tau' O z hz).mono' hmeas ?_
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (Matrix.rectangularTraceNorm_nonneg _)]
  exact rectangularTraceNorm_weightedSourceError_le tau tau' O _
    htau htau' htausum htau'sum

/-- Exact second moment of the quarter-weighted block source error.
Source: `eq:compression-block-second-moment`. -/
theorem integral_frobeniusNormSq_weightedSourceQuarter_eq
    (p : I → ℝ) (p' : L → ℝ) (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (L × U) (I × T) ℂ) (z : I × L → Ω → ℂ) (kappa : ℝ)
    (hz : ∀ b c, Integrable (fun w ↦ z b w * conj (z c w)) mu)
    (hcov : ∀ b c, (∫ w, z b w * conj (z c w) ∂mu) =
      if b = c then ((kappa * Real.sqrt (p b.1 * p' b.2) : ℝ) : ℂ) else 0) :
    (∫ w, Matrix.frobeniusNormSq
      (weightedSourceQuarter tau tau' O (fun b ↦ z b w)) ∂mu) =
      kappa * ∑ b : I × L, Real.sqrt (p b.1 * p' b.2) *
        Matrix.frobeniusNormSq (Matrix.quarterWeighted tau' tau (sourceBlock O b.2 b.1)) := by
  have h := integral_frobenius_norm_sq_sum_eq_sum z
    (fun b ↦ kappa * Real.sqrt (p b.1 * p' b.2)) hz hcov
    (fun b ↦ Matrix.quarterWeighted tau' tau (sourceBlock O b.2 b.1))
  simpa only [weightedSourceQuarter, Matrix.frobeniusNormSq, Finset.mul_sum,
    mul_assoc] using h

/-- The expected corrected-source trace error is bounded by the square root
of its covariance scale, independently of all input and private dimensions.
Source: Theorem 5.2, `eq:compression-one-choice`; setting `kappa = k^(-s)`
gives the paper's `k^(-s/2)` bound after scalar exponent arithmetic. -/
theorem integral_rectangularTraceNorm_weightedSourceError_le [IsProbabilityMeasure mu]
    (p : I → ℝ) (p' : L → ℝ) (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (L × U) (I × T) ℂ) (z : I × L → Ω → ℂ) (kappa : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp' : ∀ l, 0 ≤ p' l)
    (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (hpsum : ∑ i, p i = 1) (hp'sum : ∑ l, p' l = 1)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1)
    (hO : ‖O‖ ≤ 1) (hkappa : 0 ≤ kappa)
    (hz : ∀ b c, Integrable (fun w ↦ z b w * conj (z c w)) mu)
    (hcov : ∀ b c, (∫ w, z b w * conj (z c w) ∂mu) =
      if b = c then ((kappa * Real.sqrt (p b.1 * p' b.2) : ℝ) : ℂ) else 0) :
    (∫ w, Matrix.rectangularTraceNorm
      (weightedSourceError tau tau' O (fun b ↦ z b w)) ∂mu) ≤ Real.sqrt kappa := by
  have hnorm := integral_frobenius_norm_sum_le_sqrt z
    (fun b ↦ kappa * Real.sqrt (p b.1 * p' b.2)) hz hcov
    (fun b ↦ Matrix.quarterWeighted tau' tau (sourceBlock O b.2 b.1))
  have hsum := weighted_source_block_sum_le_one p p' tau tau' O hp hp' htau htau'
    hpsum hp'sum htausum htau'sum hO
  have hsecond : (∑ b : I × L, (kappa * Real.sqrt (p b.1 * p' b.2)) *
      Matrix.frobeniusNormSq (Matrix.quarterWeighted tau' tau (sourceBlock O b.2 b.1))) ≤
      kappa := by
    simpa only [Finset.mul_sum, mul_assoc, mul_one] using
      mul_le_mul_of_nonneg_left hsum hkappa
  calc
    _ ≤ ∫ w, Real.sqrt
        (Matrix.frobeniusNormSq (weightedSourceQuarter tau tau' O (fun b ↦ z b w))) ∂mu :=
      integral_mono
        (integrable_rectangularTraceNorm_weightedSourceError tau tau' O z hz
          htau htau' htausum htau'sum)
        (integrable_weightedSourceQuarter_norm tau tau' O z hz)
        (fun w ↦ rectangularTraceNorm_weightedSourceError_le tau tau' O _
          htau htau' htausum htau'sum)
    _ ≤ _ := by
      have hbound := hnorm.trans (Real.sqrt_le_sqrt hsecond)
      simpa only [weightedSourceQuarter, sqrt_frobeniusNormSq] using hbound

end ProbabilityTheory
