/-
Released under Apache 2.0 license as described in the file LICENSE.
Assisted-by: OpenAI Codex (GPT-6).

The proofs in this file are original formalizations of the cited mathematical argument.
No OpenAI Lean proof text is copied or adapted here. The imported Gaussian construction has
its own explicit source and modification notices in Basic.lean and Covariance.lean.
-/
import QICLean.Probability.ComplexGaussian.Covariance
import QICLean.Probability.IndependentCovariance

/-!
# Gaussian covariance across fresh independent slots

The density-source coefficients at different corrected slots are constructed on independent
standard Gaussian factors. Their tensor product covariance is derived from the checked
Gaussian slot calculation and product-measure Fubini. The ket and bra Schmidt supports may
differ at every slot. Zero probabilities and empty slot lists are included.

The source is *Polynomial PEPS approximation of gapped square-grid ground states*, Theorem 5.2,
`eq:compression-product-covariance`, `04-compression.tex:390--407`, at OpenAI/math commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Normalized product probability lists are formed from
the two independent endpoint indices of each slot; an exact pure source's identification of
its endpoints is not imposed on these free indices. The result derives the covariance of the
constructed Gaussian coefficients, rather than assuming a desired covariance identity.

This file does not assert the distributed circuit reduction, rectangular trace-norm estimate,
or network-dimension conclusion of the full compression theorem.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace QICLean.ComplexGaussian

variable {S : Type*} [Fintype S] {A : S → Type*}

/-- The tensor probability of both independent endpoint indices at each slot.
Source: Theorem 5.2, product probability lists preceding
`eq:compression-product-covariance`, `04-compression.tex:390--407`. -/
def pairedProductProbability (lam : (s : S) → A s → ℝ)
    (i : (s : S) → A s × A s) : ℝ :=
  ∏ s, lam s (i s).1 * lam s (i s).2

/-- The tensor probability is nonnegative, including zero Schmidt probabilities.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--407`. -/
theorem pairedProductProbability_nonneg (lam : (s : S) → A s → ℝ)
    (hlam : ∀ s a, 0 ≤ lam s a) (i : (s : S) → A s × A s) :
    0 ≤ pairedProductProbability lam i :=
  Finset.prod_nonneg (fun s _ ↦ mul_nonneg (hlam s _) (hlam s _))

section Normalization

variable [∀ s, Fintype (A s)]

open Classical in
/-- Normalized Schmidt weights give normalized tensor probabilities on both endpoints.
Source: Theorem 5.2, product probability lists preceding
`eq:compression-product-covariance`, `04-compression.tex:390--407`. -/
theorem sum_pairedProductProbability_eq_one (lam : (s : S) → A s → ℝ)
    (hlam : ∀ s, ∑ a, lam s a = 1) :
    (∑ i : (s : S) → A s × A s, pairedProductProbability lam i) = 1 := by
  dsimp only [pairedProductProbability]
  apply IndependentCovariance.sum_product_weights_eq_one (I := fun s ↦ A s × A s)
    (fun s a ↦ lam s a.1 * lam s a.2)
  intro s
  rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum, hlam]
  norm_num

end Normalization

section Laws

variable {C : S → Type*} [∀ s, Fintype (A s)] [∀ s, Fintype (C s)]

/-- Actual product law of the fresh Gaussian samples at every corrected slot.
Source: Theorem 5.2, fresh slot samples and
`eq:compression-product-covariance`, `04-compression.tex:338--340,390--407`. -/
def independentDensityLaw (k : ℕ) (A C : S → Type*)
    [∀ s, Fintype (A s)] [∀ s, Fintype (C s)] :
    Measure ((s : S) → Sample (Fin k × (A s × C s))) :=
  Measure.pi (fun s ↦ law (Fin k × (A s × C s)))

/-- The independent Gaussian slot law is a probability measure.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--407`. -/
instance independentDensityLawIsProbabilityMeasure (k : ℕ) :
    IsProbabilityMeasure (independentDensityLaw k A C) :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.pi (fun s ↦ law (Fin k × (A s × C s)))))

variable [∀ s, DecidableEq (A s)] [∀ s, DecidableEq (C s)]

/-- Product of the actual centered, quarter-weighted Gaussian density-source coefficients.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--407`. -/
def independentDensityCoefficient (k : ℕ) (lam : (s : S) → A s → ℝ)
    (mu : (s : S) → C s → ℝ) (i : (s : S) → A s × A s) (l : (s : S) → C s × C s)
    (ω : (s : S) → Sample (Fin k × (A s × C s))) : ℂ :=
  ∏ s, densityCoefficient k (lam s) (mu s) (i s, l s) (ω s)

/-- The actual product coefficient is integrable for every finite sample count.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--407`. -/
theorem integrable_independentDensityCoefficient (k : ℕ)
    (lam : (s : S) → A s → ℝ) (mu : (s : S) → C s → ℝ)
    (i : (s : S) → A s × A s) (l : (s : S) → C s × C s) :
    Integrable (independentDensityCoefficient k lam mu i l) (independentDensityLaw k A C) :=
  Integrable.fintype_prod_dep (fun s ↦
    (memLp_densityCoefficient k (lam s) (mu s) (i s, l s)).integrable (by norm_num))

/-- Actual Gaussian tensor-coefficient conjugate products are integrable.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--407`.
No positivity or normalization condition on the weights is needed for integrability. -/
theorem integrable_independentDensityCoefficient_mul_conj (k : ℕ)
    (lam : (s : S) → A s → ℝ) (mu : (s : S) → C s → ℝ)
    (i i' : (s : S) → A s × A s) (l l' : (s : S) → C s × C s) :
    Integrable (fun ω ↦ independentDensityCoefficient k lam mu i l ω *
      star (independentDensityCoefficient k lam mu i' l' ω)) (independentDensityLaw k A C) := by
  apply IndependentCovariance.integrable_product_mul_conj
  intro s
  simpa only [Complex.star_def] using
    integrable_densityCoefficient_mul_conj k (lam s) (mu s) (i s, l s) (i' s, l' s)

open Classical in
/-- Exact covariance of the constructed Gaussian coefficients over the actual independent law.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--407`.
Individual and joint covariance identities are derived from the Gaussian law, not assumptions.
All finite heterogeneous supports and zero probabilities are allowed. Normalization is only
needed when interpreting the product weights as probability lists, not for this identity. -/
theorem integral_independentDensityCoefficient_mul_conj (k : ℕ) (hk : 0 < k)
    (lam : (s : S) → A s → ℝ) (mu : (s : S) → C s → ℝ)
    (hlam : ∀ s a, 0 ≤ lam s a) (hmu : ∀ s c, 0 ≤ mu s c)
    (i i' : (s : S) → A s × A s) (l l' : (s : S) → C s × C s) :
    (∫ ω, independentDensityCoefficient k lam mu i l ω *
      star (independentDensityCoefficient k lam mu i' l' ω) ∂independentDensityLaw k A C) =
      if i = i' ∧ l = l' then
        (((k : ℝ) ^ (-(Fintype.card S : ℝ)) *
          Real.sqrt (pairedProductProbability lam i * pairedProductProbability mu l) : ℝ) : ℂ)
      else 0 := by
  have hcov (s : S) (a a' : A s × A s) (b b' : C s × C s) :
      (∫ x, densityCoefficient k (lam s) (mu s) (a, b) x *
        star (densityCoefficient k (lam s) (mu s) (a', b') x)
        ∂law (Fin k × (A s × C s))) = if a = a' ∧ b = b' then
          (((k : ℝ)⁻¹ * Real.sqrt
            ((lam s a.1 * lam s a.2) * (mu s b.1 * mu s b.2)) : ℝ) : ℂ) else 0 := by
    simpa only [Complex.star_def, Prod.mk.injEq, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_natCast] using
      integral_densityCoefficient_mul_conj k hk (lam s) (mu s) (hlam s) (hmu s) (a, b) (a', b')
  have htotal := IndependentCovariance.tensor_covariance_weighted
    (fun s ↦ law (Fin k × (A s × C s)))
    (fun s a b ↦ densityCoefficient k (lam s) (mu s) (a, b)) k
    (fun s a ↦ lam s a.1 * lam s a.2) (fun s b ↦ mu s b.1 * mu s b.2)
    (fun s a ↦ mul_nonneg (hlam s _) (hlam s _))
    (fun s b ↦ mul_nonneg (hmu s _) (hmu s _))
    (fun s a b a' b' ↦ by
      by_cases h : a = a' ∧ b = b'
      · simpa only [ite_eq_left h] using hcov s a a' b b'
      · simpa only [ite_eq_right h] using hcov s a a' b b') i i' l l'
  by_cases h : i = i' ∧ l = l'
  · simpa only [ite_eq_left h, independentDensityCoefficient, independentDensityLaw,
      pairedProductProbability, IndependentCovariance.tensorCoefficient] using htotal
  · simpa only [ite_eq_right h, independentDensityCoefficient, independentDensityLaw,
      pairedProductProbability, IndependentCovariance.tensorCoefficient] using htotal

/-- Nonempty correction-slot products remain centered under the actual independent law.
Source: Theorem 5.2, centered coefficients and fresh slots,
`eq:compression-product-covariance`, `04-compression.tex:338--340,390--407`. -/
theorem integral_independentDensityCoefficient_eq_zero [Nonempty S] (k : ℕ)
    (lam : (s : S) → A s → ℝ) (mu : (s : S) → C s → ℝ)
    (i : (s : S) → A s × A s) (l : (s : S) → C s × C s) :
    (∫ ω, independentDensityCoefficient k lam mu i l ω ∂independentDensityLaw k A C) = 0 := by
  dsimp only [independentDensityCoefficient, independentDensityLaw]
  rw [integral_fintype_prod_eq_prod]
  simp only [integral_densityCoefficient, Finset.prod_const, Finset.card_univ]
  exact zero_pow (Fintype.card_ne_zero)

end Laws

end QICLean.ComplexGaussian
