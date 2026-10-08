/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex
-/
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Covariance of products over independent source slots

On an actual finite product measure, the covariance of products of complex slot coefficients
is the product of their individual covariances. Integrability is derived from the slot-wise
integrability hypotheses. Diagonal slot covariance gives diagonal covariance on the full
tensor multiindices, with the product probability weights and the expected inverse-power
sample scaling. The index types and sample spaces may differ from slot to slot.

The source is *Polynomial PEPS approximation of gapped square-grid ground states*, Theorem 5.2,
`eq:compression-product-covariance`, `04-compression.tex:390--403`, at OpenAI/math commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The slot-wise Gaussian covariance and its integrability
are inputs from `eq:compression-slot-variance`; they are not assumed at the product level.
No cross-branch independence is imposed: the product space represents fresh independent slots
for one fixed deterministic branch choice. Empty slot types give the scalar covariance one.

The Lean proofs are newly written from the mathematical argument and Mathlib. No OpenAI Lean
source is copied or adapted. This file proves the product-independence step, not the Gaussian
slot calculation or the full distributed density-compression theorem.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace IndependentCovariance

variable {S : Type*} [Fintype S] {Ω : S → Type*} [∀ s, MeasurableSpace (Ω s)]
    (μ : (s : S) → Measure (Ω s))

section SigmaFinite

variable [∀ s, SigmaFinite (μ s)]

/-- Covariance factorization on the actual heterogeneous product measure.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--403`.
Here independence is implemented by the product measure, not by assuming the desired joint
covariance identity. -/
theorem integral_product_mul_conj (f g : (s : S) → Ω s → ℂ) :
    (∫ ω, (∏ s, f s (ω s)) * star (∏ s, g s (ω s)) ∂Measure.pi μ) =
      ∏ s, ∫ x, f s x * star (g s x) ∂μ s := by
  simp_rw [star_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun s x ↦ f s x * star (g s x))

/-- Pair integrability also passes from the individual slots to the product coefficients.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--403`. -/
theorem integrable_product_mul_conj (f g : (s : S) → Ω s → ℂ)
    (hf : ∀ s, Integrable (fun x ↦ f s x * star (g s x)) (μ s)) :
    Integrable (fun ω ↦ (∏ s, f s (ω s)) * star (∏ s, g s (ω s))) (Measure.pi μ) := by
  simpa only [star_prod, ← Finset.prod_mul_distrib] using Integrable.fintype_prod_dep hf

variable {I L : S → Type*}

/-- The coefficient on the full ket and bra tensor multiindices for a fixed branch choice.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--403`. -/
def tensorCoefficient (c : (s : S) → I s → L s → Ω s → ℂ)
    (i : (s : S) → I s) (l : (s : S) → L s) (ω : (s : S) → Ω s) : ℂ :=
  ∏ s, c s (i s) (l s) (ω s)

/-- The actual tensor coefficients have integrable conjugate products.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--403`. -/
theorem integrable_tensorCoefficient_mul_conj
    (c : (s : S) → I s → L s → Ω s → ℂ)
    (hc : ∀ s a b a' b', Integrable
      (fun x ↦ c s a b x * star (c s a' b' x)) (μ s))
    (i i' : (s : S) → I s) (l l' : (s : S) → L s) :
    Integrable (fun ω ↦ tensorCoefficient c i l ω * star (tensorCoefficient c i' l' ω))
      (Measure.pi μ) :=
  integrable_product_mul_conj μ _ _ (fun s ↦ hc s _ _ _ _)

open Classical in
/-- Diagonal slot covariances become diagonal on the full ket and bra multiindices.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--403`.
The input identifies individual slot covariances; the joint covariance is derived by Fubini. -/
theorem tensor_covariance_of_diagonal
    (c : (s : S) → I s → L s → Ω s → ℂ)
    (variance : (s : S) → I s → L s → ℂ)
    (hcov : ∀ s a b a' b',
      (∫ x, c s a b x * star (c s a' b' x) ∂μ s) =
        if a = a' ∧ b = b' then variance s a b else 0)
    (i i' : (s : S) → I s) (l l' : (s : S) → L s) :
    (∫ ω, tensorCoefficient c i l ω * star (tensorCoefficient c i' l' ω)
      ∂Measure.pi μ) = if i = i' ∧ l = l' then ∏ s, variance s (i s) (l s) else 0 := by
  classical
  dsimp only [tensorCoefficient]
  rw [integral_product_mul_conj]
  simp_rw [hcov]
  rw [Fintype.prod_ite_zero]
  have hdiag : (∀ s, i s = i' s ∧ l s = l' s) ↔ i = i' ∧ l = l' := by
    constructor
    · intro h
      exact ⟨funext (fun s ↦ (h s).1), funext (fun s ↦ (h s).2)⟩
    · rintro ⟨rfl, rfl⟩
      simp
  simp only [hdiag]

/-- Product square-root slot weights are the square root of the two tensor weights.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--403`.
Weights may vanish; no support rank or dimension enters this identity. -/
theorem product_weighted_sqrt (κ : ℝ) (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s) :
    (∏ s, (κ * Real.sqrt (p s * q s) : ℝ)) =
      κ ^ Fintype.card S * Real.sqrt ((∏ s, p s) * ∏ s, q s) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  rw [← Real.sqrt_prod Finset.univ (fun s _ ↦ mul_nonneg (hp s) (hq s)),
    Finset.prod_mul_distrib]

end SigmaFinite

variable {I L : S → Type*}

section Probability

variable [∀ s, IsProbabilityMeasure (μ s)]

open Classical in
/-- The source's full tensor covariance on fresh independent probability-space slots.
Source: Theorem 5.2, `eq:compression-product-covariance`, `04-compression.tex:390--403`.
Ket and bra indices are separate and may have unrelated dimensions. The per-slot covariance
is supplied by the Gaussian coefficient calculation; the `k⁻ˢ` factor and full-index deltas
are derived here. Empty slot types give covariance one. -/
theorem tensor_covariance_weighted
    (c : (s : S) → I s → L s → Ω s → ℂ) (k : ℕ)
    (p : (s : S) → I s → ℝ) (q : (s : S) → L s → ℝ)
    (hp : ∀ s a, 0 ≤ p s a) (hq : ∀ s b, 0 ≤ q s b)
    (hcov : ∀ s a b a' b',
      (∫ x, c s a b x * star (c s a' b' x) ∂μ s) =
        if a = a' ∧ b = b' then
          (((k : ℝ)⁻¹ * Real.sqrt (p s a * q s b) : ℝ) : ℂ) else 0)
    (i i' : (s : S) → I s) (l l' : (s : S) → L s) :
    (∫ ω, tensorCoefficient c i l ω * star (tensorCoefficient c i' l' ω)
      ∂Measure.pi μ) = if i = i' ∧ l = l' then
        (((k : ℝ) ^ (-(Fintype.card S : ℝ)) *
          Real.sqrt ((∏ s, p s (i s)) * ∏ s, q s (l s)) : ℝ) : ℂ) else 0 := by
  classical
  rw [tensor_covariance_of_diagonal μ c _ hcov]
  split_ifs
  · rw [← Complex.ofReal_prod]
    congr 1
    rw [product_weighted_sqrt _ _ _ (fun s ↦ hp s _) (fun s ↦ hq s _),
      Real.rpow_neg (Nat.cast_nonneg k), Real.rpow_natCast, inv_pow]
  · rfl

end Probability

section ProbabilityWeights

variable [∀ s, Fintype (I s)]

open Classical in
/-- Normalized slot weights give a normalized probability list on the full tensor multiindex.
Source: Theorem 5.2, product probability lists preceding
`eq:compression-product-covariance`, `04-compression.tex:390--403`. -/
theorem sum_product_weights_eq_one (p : (s : S) → I s → ℝ)
    (hp : ∀ s, ∑ a, p s a = 1) :
    (∑ i : (s : S) → I s, ∏ s, p s (i s)) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [hp, Finset.prod_const_one]

end ProbabilityWeights

end IndependentCovariance
