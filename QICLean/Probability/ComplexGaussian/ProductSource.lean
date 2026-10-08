/-
Released under Apache 2.0 license as described in the file LICENSE.
Assisted-by: OpenAI Codex (GPT-6).
These constructions and proofs are independently written from the manuscript
and Mathlib; no upstream OpenAI Lean proof text is reused in this file.
The imported real Gaussian foundation's attribution is recorded in Basic.lean.
-/
import QICLean.Probability.ComplexGaussian.Covariance
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.Matrix.Normed

/-!
# Product-operator replacement of a Schmidt density source

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
`04-compression.tex:279–340`, equation `compression-random-source`.

The ket and bra Schmidt supports may have different dimensions. The two sampled
rectangular operators use the same circular complex Gaussian coordinates, with
complex conjugation in the second factor. Their Kronecker-product average has
the exact Schmidt outer product as its expectation. Its centered entries are
the previously constructed `densityCoefficient`, so their covariance and
integrability follow from the checked circular-complex Gaussian calculation.

This module concerns basis-coordinate source operators. It imposes no sampled
operator-norm bounds, physical circuit assumptions, or private-dimension bounds.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate Kronecker Matrix.Norms.Elementwise

namespace QICLean.ComplexGaussian

noncomputable section

variable {A C : Type*} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]

-- Specify the continuous enorm directly: the package limits pending synthesis depth to three.
local instance : ContinuousENorm (Matrix (A × A) (C × C) ℂ) :=
  SeminormedAddGroup.toContinuousENorm

/-- A Schmidt vector in its paired basis, with amplitudes `sqrt(lam a)`.
Source: `04-compression.tex:281–289`. -/
def schmidtVector (lam : A → ℝ) (p : A × A) : ℂ :=
  if p.1 = p.2 then (Real.sqrt (lam p.1) : ℂ) else 0

/-- The rectangular Schmidt ket/bra outer-product target.
Source: `eq:compression-random-source`, `04-compression.tex:281–305`. -/
def schmidtSource (lam : A → ℝ) (mu : C → ℝ) : Matrix (A × A) (C × C) ℂ :=
  Matrix.vecMulVec (schmidtVector lam) (fun q ↦ conj (schmidtVector mu q))

/-- The first sampled rectangular source operator `U_j`.
Source: `eq:compression-random-source`, `04-compression.tex:294–297`. -/
def sourceU (k : ℕ) (lam : A → ℝ) (mu : C → ℝ) (j : Fin k)
    (x : Sample (Fin k × (A × C))) : Matrix A C ℂ :=
  Matrix.of fun a c ↦ (((lam a * mu c) ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
    coordinate (j, (a, c)) x

/-- The second sampled rectangular source operator `V_j`, using the conjugate of the
same Gaussian family as `U_j`. Source: `04-compression.tex:297–300`. -/
def sourceV (k : ℕ) (lam : A → ℝ) (mu : C → ℝ) (j : Fin k)
    (x : Sample (Fin k × (A × C))) : Matrix A C ℂ :=
  Matrix.of fun b d ↦ (((lam b * mu d) ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
    conj (coordinate (j, (b, d)) x)

/-- The sampled product-operator replacement `Xhat = k⁻¹ sum_j U_j ⊗ V_j`.
Source: `eq:compression-random-source`, `04-compression.tex:300–305`. -/
def sampledSource (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (x : Sample (Fin k × (A × C))) : Matrix (A × A) (C × C) ℂ :=
  (k : ℂ)⁻¹ • ∑ j : Fin k, sourceU k lam mu j x ⊗ₖ sourceV k lam mu j x

/-- The actual centered sampled matrix, without positivity or Hermiticity assumptions.
Source: `eq:compression-random-source`, `04-compression.tex:302–305`. -/
def sourceCorrection (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (x : Sample (Fin k × (A × C))) : Matrix (A × A) (C × C) ℂ :=
  sampledSource k lam mu x - schmidtSource lam mu

omit [Fintype A] [Fintype C] in
theorem schmidtSource_apply (lam : A → ℝ) (mu : C → ℝ) (p : A × A) (q : C × C) :
    schmidtSource lam mu p q =
      if p.1 = p.2 ∧ q.1 = q.2 then
        ((Real.sqrt (lam p.1) * Real.sqrt (mu q.1) : ℝ) : ℂ) else 0 := by
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
    simp [schmidtSource, Matrix.vecMulVec_apply, schmidtVector, hp, hq]

omit [DecidableEq A] [DecidableEq C] in
theorem sampledSource_apply (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (x : Sample (Fin k × (A × C))) (p : A × A) (q : C × C) :
    sampledSource k lam mu x p q = (coefficientWeight lam mu (p, q) : ℂ) *
      ((k : ℂ)⁻¹ * ∑ j : Fin k, coordinate (j, (p.1, q.1)) x *
        conj (coordinate (j, (p.2, q.2)) x)) := by
  rw [coefficientWeight_eq_product_quarter lam mu hlam hmu]
  simp only [sampledSource, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Matrix.kroneckerMap_apply, sourceU, sourceV, Matrix.of_apply]
  rw [← mul_assoc, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

private theorem quarter_square (t : ℝ) (ht : 0 ≤ t) :
    t ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ) = Real.sqrt t := by
  rw [← pow_two, ← Real.rpow_mul_natCast ht, Real.sqrt_eq_rpow]
  norm_num

omit [Fintype A] [Fintype C] in
theorem weighted_delta_eq_schmidtSource (lam : A → ℝ) (mu : C → ℝ)
    (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c) (p : A × A) (q : C × C) :
    (coefficientWeight lam mu (p, q) : ℂ) * delta (p.1, q.1) (p.2, q.2) =
      schmidtSource lam mu p q := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  by_cases hab : a = b
  · subst b
    by_cases hcd : c = d
    · subst d
      rw [coefficientWeight_eq_product_quarter lam mu hlam hmu]
      simp only [delta, ite_true, mul_one]
      rw [quarter_square _ (mul_nonneg (hlam _) (hmu _)),
        Real.sqrt_mul (hlam _)]
      simp [schmidtSource_apply]
    · simp [delta, hcd, schmidtSource_apply]
  · simp [delta, hab, schmidtSource_apply]

theorem sampleAverage_eq_average_sub_delta {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 0 < k) (a b : ι) (x : Sample (Fin k × ι)) :
    sampleAverage k a b x = (k : ℂ)⁻¹ *
      ∑ j : Fin k, coordinate (j, a) x * conj (coordinate (j, b) x) - delta a b := by
  simp only [sampleAverage, centered, delta, Prod.mk.injEq, true_and]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hk)
  field_simp

/-- Each entry of the actual centered source replacement is precisely the Gaussian
coefficient whose diagonal covariance was proved earlier. Source:
`04-compression.tex:311–318`. -/
theorem sourceCorrection_apply (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (x : Sample (Fin k × (A × C))) (p : A × A) (q : C × C) :
    sourceCorrection k lam mu x p q = densityCoefficient k lam mu (p, q) x := by
  simp only [sourceCorrection, Matrix.sub_apply, sampledSource_apply k lam mu hlam hmu,
    densityCoefficient]
  rw [sampleAverage_eq_average_sub_delta k hk,
    ← weighted_delta_eq_schmidtSource lam mu hlam hmu p q]
  ring

theorem integrable_sourceCorrection_entry (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (p : A × A) (q : C × C) :
    Integrable (fun x ↦ sourceCorrection k lam mu x p q) (law (Fin k × (A × C))) := by
  simp_rw [sourceCorrection_apply k hk lam mu hlam hmu]
  exact (memLp_densityCoefficient k lam mu (p, q)).integrable (by norm_num)

/-- Pair integrability for entries of the actual source-correction matrix, rather than
an abstract family assumed to satisfy the desired covariance. -/
theorem integrable_sourceCorrection_entry_mul_conj (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (p r : A × A) (q t : C × C) :
    Integrable (fun x ↦ sourceCorrection k lam mu x p q *
      conj (sourceCorrection k lam mu x r t)) (law (Fin k × (A × C))) := by
  simp_rw [sourceCorrection_apply k hk lam mu hlam hmu]
  exact integrable_densityCoefficient_mul_conj k lam mu (p, q) (r, t)

/-- The covariance of the actual source-correction entries, including coincident indices
and zero Schmidt weights. Source: `eq:compression-gaussian-covariance`,
`04-compression.tex:311–328`. -/
theorem integral_sourceCorrection_entry_mul_conj (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (p r : A × A) (q t : C × C) :
    (∫ x, sourceCorrection k lam mu x p q * conj (sourceCorrection k lam mu x r t)
      ∂law (Fin k × (A × C))) =
      if (p, q) = (r, t) then (k : ℂ)⁻¹ *
        (Real.sqrt ((lam p.1 * lam p.2) * (mu q.1 * mu q.2)) : ℂ) else 0 := by
  simp_rw [sourceCorrection_apply k hk lam mu hlam hmu]
  exact integral_densityCoefficient_mul_conj k hk lam mu hlam hmu (p, q) (r, t)

omit [DecidableEq A] [DecidableEq C] in
theorem integrable_sampledSource_entry (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (p : A × A) (q : C × C) :
    Integrable (fun x ↦ sampledSource k lam mu x p q) (law (Fin k × (A × C))) := by
  classical
  have he (x : Sample (Fin k × (A × C))) : sampledSource k lam mu x p q =
      sourceCorrection k lam mu x p q + schmidtSource lam mu p q := by
    simp [sourceCorrection]
  simp_rw [he]
  exact (integrable_sourceCorrection_entry k hk lam mu hlam hmu p q).add (integrable_const _)

theorem integral_sampledSource_entry (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (p : A × A) (q : C × C) :
    (∫ x, sampledSource k lam mu x p q ∂law (Fin k × (A × C))) =
      schmidtSource lam mu p q := by
  have he (x : Sample (Fin k × (A × C))) : sampledSource k lam mu x p q =
      densityCoefficient k lam mu (p, q) x + schmidtSource lam mu p q := by
    rw [← sourceCorrection_apply k hk lam mu hlam hmu]
    simp [sourceCorrection]
  simp_rw [he]
  rw [integral_add ((memLp_densityCoefficient _ _ _ _).integrable (by norm_num))
    (integrable_const _), integral_densityCoefficient]
  simp

omit [DecidableEq A] [DecidableEq C] in
theorem integrable_sampledSource (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c) :
    Integrable (sampledSource k lam mu) (law (Fin k × (A × C))) := by
  have hpi : Integrable (fun x ↦ ((fun p q ↦ sampledSource k lam mu x p q) :
      (A × A) → (C × C) → ℂ)) (law (Fin k × (A × C))) := by
    apply Integrable.of_eval
    intro p
    apply Integrable.of_eval
    intro q
    exact integrable_sampledSource_entry k hk lam mu hlam hmu p q
  have hMatrix : AEStronglyMeasurable (sampledSource k lam mu)
      (law (Fin k × (A × C))) :=
    (show Continuous (Matrix.of (m := A × A) (n := C × C) (α := ℂ)) from
      continuous_id.matrixOf).comp_aestronglyMeasurable hpi.aestronglyMeasurable
  exact hpi.congr'_enorm hMatrix (Filter.Eventually.of_forall fun _ ↦ rfl)

theorem integrable_sourceCorrection (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c) :
    Integrable (sourceCorrection k lam mu) (law (Fin k × (A × C))) :=
  (integrable_sampledSource k hk lam mu hlam hmu).sub (integrable_const _)

/-- The actual product-operator replacement has the exact Schmidt outer product as its
expectation, with no sample norm bound or full-support hypothesis. Source:
`eq:compression-random-source`, `04-compression.tex:279–309`. -/
theorem integral_sampledSource (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c) :
    (∫ x, sampledSource k lam mu x ∂law (Fin k × (A × C))) = schmidtSource lam mu := by
  ext p q
  change (∫ x, (fun p q ↦ sampledSource k lam mu x p q) ∂law (Fin k × (A × C))) p q = _
  have hr (p : A × A) : Integrable (fun x ↦ (fun q ↦ sampledSource k lam mu x p q))
      (law (Fin k × (A × C))) :=
    Integrable.of_eval fun q ↦ integrable_sampledSource_entry k hk lam mu hlam hmu p q
  rw [eval_integral hr,
    eval_integral (fun q ↦ integrable_sampledSource_entry k hk lam mu hlam hmu p q),
    integral_sampledSource_entry k hk lam mu hlam hmu]

theorem integral_sourceCorrection (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c) :
    (∫ x, sourceCorrection k lam mu x ∂law (Fin k × (A × C))) = 0 := by
  change (∫ x, sampledSource k lam mu x - schmidtSource lam mu
    ∂law (Fin k × (A × C))) = 0
  rw [integral_sub (integrable_sampledSource k hk lam mu hlam hmu)
    (integrable_const _), integral_sampledSource k hk lam mu hlam hmu]
  simp

end

end QICLean.ComplexGaussian
