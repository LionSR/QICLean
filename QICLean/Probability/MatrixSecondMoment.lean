/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# Matrix second moments from diagonal coefficient covariance

For a finite complex coefficient family with diagonal covariance, the expected
Hilbert–Schmidt square of a linear combination of rectangular matrices is the
variance-weighted sum of their Hilbert–Schmidt squares. No matrix dimension
factor occurs. Integrability of every coefficient product is explicit.

## Main statements

* `integral_normSq_sum_eq_sum` computes the scalar second moment.
* `integral_frobenius_norm_sq_sum_eq_sum` computes the rectangular matrix second moment.
* `integral_frobenius_norm_sum_le_sqrt` bounds its mean by the square root of that moment.

## References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
Theorem 5.2, `eq:compression-block-second-moment`;
`04-compression.tex`, lines 502–527, at source revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The proofs in this module are original and use Mathlib's finite sums and integrals.
-/

/-!
Provenance-ID: p09-qic-second-moment-integrable_normsq_sum
Downstream declaration: ProbabilityTheory.integrable_normSq_sum
Source: September 24, 2026 paper.
Labels: eq:compression-block-second-moment.
Independently formalized; no upstream Lean proof text reused.
-/

/-!
Provenance-ID: p09-qic-second-moment-integral_normsq_sum_eq_sum
Downstream declaration: ProbabilityTheory.integral_normSq_sum_eq_sum
Source: September 24, 2026 paper.
Labels: eq:compression-block-second-moment.
Independently formalized; no upstream Lean proof text reused.
-/

/-!
Provenance-ID: p09-qic-second-moment-integrable_frobenius_norm_sq_sum
Downstream declaration: ProbabilityTheory.integrable_frobenius_norm_sq_sum
Source: September 24, 2026 paper.
Labels: eq:compression-block-second-moment.
Independently formalized; no upstream Lean proof text reused.
-/

/-!
Provenance-ID: p09-qic-second-moment-integral_frobenius_norm_sq_sum_eq_sum
Downstream declaration: ProbabilityTheory.integral_frobenius_norm_sq_sum_eq_sum
Source: September 24, 2026 paper.
Labels: eq:compression-block-second-moment.
Independently formalized; no upstream Lean proof text reused.
-/

/-!
Provenance-ID: p09-qic-second-moment-integral_frobenius_norm_sum_le_sqrt
Downstream declaration: ProbabilityTheory.integral_frobenius_norm_sum_le_sqrt
Source: September 24, 2026 paper.
Labels: eq:compression-block-second-moment, eq:compression-dimension-free.
Independently formalized; no upstream Lean proof text reused.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate Matrix.Norms.Frobenius

noncomputable section

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable {μ : Measure Ω}

private lemma normSq_sum_expand (z a : ι → ℂ) :
    (Complex.normSq (∑ i, z i * a i) : ℂ) =
      ∑ i, ∑ j, (z i * conj (z j)) * (a i * conj (a j)) := by
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul]
  simp_rw [map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Pairwise integrability implies integrability of the squared modulus of every
finite linear combination. This supplies the integrability required in the
second-moment calculation in Theorem 5.2. -/
theorem integrable_normSq_sum (z : ι → Ω → ℂ)
    (hz : ∀ i j, Integrable (fun ω => z i ω * conj (z j ω)) μ)
    (a : ι → ℂ) :
    Integrable (fun ω => Complex.normSq (∑ i, z i ω * a i)) μ := by
  have hsum : Integrable (fun ω =>
      ∑ i, ∑ j, (z i ω * conj (z j ω)) * (a i * conj (a j))) μ :=
    integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hz i j).mul_const _
  have hcomplex : Integrable
      (fun ω => (Complex.normSq (∑ i, z i ω * a i) : ℂ)) μ :=
    hsum.congr (Filter.Eventually.of_forall fun ω =>
      (normSq_sum_expand (fun i => z i ω) a).symm)
  convert hcomplex.re using 1

/-- Diagonal complex covariance gives an exact scalar second-moment identity.
The covariance parameter is unrestricted; the diagonal covariance assumption
itself forces each variance to be nonnegative. This is the scalar calculation
underlying `eq:compression-block-second-moment` in Theorem 5.2. -/
theorem integral_normSq_sum_eq_sum [DecidableEq ι]
    (z : ι → Ω → ℂ) (v : ι → ℝ)
    (hz : ∀ i j, Integrable (fun ω => z i ω * conj (z j ω)) μ)
    (hcov : ∀ i j, (∫ ω, z i ω * conj (z j ω) ∂μ) =
      if i = j then (v i : ℂ) else 0)
    (a : ι → ℂ) :
    (∫ ω, Complex.normSq (∑ i, z i ω * a i) ∂μ) =
      ∑ i, v i * Complex.normSq (a i) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  calc
    (∫ ω, (Complex.normSq (∑ i, z i ω * a i) : ℂ) ∂μ) =
        ∫ ω, ∑ i, ∑ j, (z i ω * conj (z j ω)) * (a i * conj (a j)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        normSq_sum_expand (fun i => z i ω) a)
    _ = ∑ i, ∑ j, ∫ ω,
        (z i ω * conj (z j ω)) * (a i * conj (a j)) ∂μ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        exact integral_finsetSum _ fun j _ => (hz i j).mul_const _
      · intro i _
        exact integrable_finsetSum _ fun j _ => (hz i j).mul_const _
    _ = ∑ i, (v i : ℂ) * (Complex.normSq (a i) : ℂ) := by
      simp_rw [integral_mul_const, hcov]
      simp [ite_mul, Complex.mul_conj]

private lemma frobenius_norm_sq_eq_sum_normSq
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = ∑ r, ∑ c, Complex.normSq (A r c) := by
  simp only [Matrix.frobenius_norm_def, Real.rpow_two, ← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt (by positivity)]
  simp only [Complex.normSq_eq_norm_sq]

/-- Pairwise coefficient integrability suffices for integrability of the
Hilbert–Schmidt square of a finite rectangular matrix combination. -/
theorem integrable_frobenius_norm_sq_sum
    {m n : Type*} [Fintype m] [Fintype n]
    (z : ι → Ω → ℂ)
    (hz : ∀ i j, Integrable (fun ω => z i ω * conj (z j ω)) μ)
    (A : ι → Matrix m n ℂ) :
    Integrable (fun ω => ‖∑ i, z i ω • A i‖ ^ 2) μ := by
  have hentry (r : m) (c : n) : Integrable
      (fun ω => Complex.normSq (∑ i, z i ω * A i r c)) μ :=
    integrable_normSq_sum z hz (fun i => A i r c)
  have hsum : Integrable
      (fun ω => ∑ r, ∑ c, Complex.normSq (∑ i, z i ω * A i r c)) μ :=
    integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun c _ => hentry r c
  convert hsum using 1
  funext ω
  simp only [frobenius_norm_sq_eq_sum_normSq, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]

/-- Diagonal coefficient covariance gives the exact Hilbert–Schmidt second
moment of a finite linear combination of arbitrary rectangular matrices.

This is the dimension-independent algebraic step of Theorem 5.2,
`eq:compression-block-second-moment`. Its coefficient hypotheses must be
proved for the sampled source family before applying it to that theorem. -/
theorem integral_frobenius_norm_sq_sum_eq_sum
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq ι]
    (z : ι → Ω → ℂ) (v : ι → ℝ)
    (hz : ∀ i j, Integrable (fun ω => z i ω * conj (z j ω)) μ)
    (hcov : ∀ i j, (∫ ω, z i ω * conj (z j ω) ∂μ) =
      if i = j then (v i : ℂ) else 0)
    (A : ι → Matrix m n ℂ) :
    (∫ ω, ‖∑ i, z i ω • A i‖ ^ 2 ∂μ) = ∑ i, v i * ‖A i‖ ^ 2 := by
  have hentry (r : m) (c : n) : Integrable
      (fun ω => Complex.normSq (∑ i, z i ω * A i r c)) μ :=
    integrable_normSq_sum z hz (fun i => A i r c)
  simp only [frobenius_norm_sq_eq_sum_normSq, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  calc
    (∫ ω, ∑ r, ∑ c, Complex.normSq (∑ i, z i ω * A i r c) ∂μ) =
        ∑ r, ∑ c, ∫ ω, Complex.normSq (∑ i, z i ω * A i r c) ∂μ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro r _
        exact integral_finsetSum _ fun c _ => hentry r c
      · intro r _
        exact integrable_finsetSum _ fun c _ => hentry r c
    _ = ∑ r, ∑ c, ∑ i, v i * Complex.normSq (A i r c) := by
      simp_rw [integral_normSq_sum_eq_sum z v hz hcov]
    _ = ∑ i, v i * ∑ r, ∑ c, Complex.normSq (A i r c) := by
      simp_rw [Finset.mul_sum]
      calc
        (∑ r, ∑ c, ∑ i, v i * Complex.normSq (A i r c)) =
            ∑ r, ∑ i, ∑ c, v i * Complex.normSq (A i r c) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_comm]
        _ = ∑ i, ∑ r, ∑ c, v i * Complex.normSq (A i r c) := by
          rw [Finset.sum_comm]

/-- The expected Hilbert–Schmidt norm is at most the square root of the exact
diagonal-covariance second moment. Pair-product integrability also supplies
measurability of the norm through the square-root function, so no additional
coefficient measurability hypothesis is needed.

This is the Cauchy–Schwarz step in Theorem 5.2, lines 529–533. -/
theorem integral_frobenius_norm_sum_le_sqrt [IsProbabilityMeasure μ]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq ι]
    (z : ι → Ω → ℂ) (v : ι → ℝ)
    (hz : ∀ i j, Integrable (fun ω => z i ω * conj (z j ω)) μ)
    (hcov : ∀ i j, (∫ ω, z i ω * conj (z j ω) ∂μ) =
      if i = j then (v i : ℂ) else 0)
    (A : ι → Matrix m n ℂ) :
    (∫ ω, ‖∑ i, z i ω • A i‖ ∂μ) ≤ Real.sqrt (∑ i, v i * ‖A i‖ ^ 2) := by
  let f : Ω → ℝ := fun ω => ‖∑ i, z i ω • A i‖
  have hsquare : Integrable (fun ω => f ω ^ 2) μ :=
    integrable_frobenius_norm_sq_sum z hz A
  have hmeas : AEStronglyMeasurable f μ := by
    have h := Real.continuous_sqrt.comp_aestronglyMeasurable hsquare.aestronglyMeasurable
    simpa only [Function.comp_def, f, Real.sqrt_sq_eq_abs, abs_norm] using h
  have hLp : MemLp f 2 μ := (memLp_two_iff_integrable_sq hmeas).2 hsquare
  apply Real.le_sqrt_of_sq_le
  have hvar := variance_nonneg f μ
  rw [variance_eq_sub hLp] at hvar
  have hsecond := integral_frobenius_norm_sq_sum_eq_sum z v hz hcov A
  change (∫ ω, f ω ^ 2 ∂μ) = _ at hsecond
  rw [← hsecond]
  change (∫ ω, f ω ∂μ) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂μ
  exact sub_nonneg.mp hvar

end ProbabilityTheory
