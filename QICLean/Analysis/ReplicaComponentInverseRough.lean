/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaComponentInverseGoodExpectation
import QICLean.Analysis.ReplicaGoodConfigurationExpectation
import QICLean.Analysis.ReplicaGoodPhysicalExponential

/-!
# The rough inverse estimate on each actual excitation component

The inverse metric is evaluated on the component defined by the original
excitation projection. The good-copy expectation equals the trace against
its actual reduced density. Removing the physical deficit there and using
the two merge moments gives the rough estimate, with all polynomial and
binomial factors explicit. No component normalization is necessary.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 441–576, `comparator:component-inverse`,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaComponentInverseRough_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual inverse squared band metric obeys the rough component
estimate under the original symmetry and two auxiliary label conditions.
The polynomial constant is chosen before the copy number and vector.
Source: `07-comparators.tex`, lines 441–576, `comparator:component-inverse`.
-/
theorem exists_replicaExcitationComponent_inverse_rough_le
    {t : ℝ} (ht : 0 < t) (htsmall : 4 * t ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (B : Finset (Fin k))
      (Ω : ι 0 × (ι 1 × ι 2) → ℂ), ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k)))
      (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
        ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ),
      (∀ σ : Equiv.Perm (Fin k),
        (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
          (permOp (copyPerm (ι 3) k) σ ⊗ₖ
            permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u) →
      (((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
          (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        (labelProj (copyPerm (ι 3) k) ellC ⊗ₖ
          (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ))) *ᵥ u = u) →
      (((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
          (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        ((1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ
          labelProj (copyPerm (ι 4) k) ellR)) *ᵥ u = u) →
      let m := Bᶜ.card
      let w := (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
          ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
      let f := w ∘ fiveFactorCopiesEquiv ι k
      let W := replicaMetric ι t k
      let b := Real.log ellC.dim + Real.log ellR.dim -
        (B.card : ℝ) * (Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))) -
          2 * Real.log (k.choose B.card)
      let q := ((((m + 1) ^ ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2) : ℕ) : ℝ) +
        (((m + 1) ^ ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2) : ℕ) : ℝ)) / 2
      (star f ⬝ᵥ ((((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)⁻¹ *ᵥ f)).re ≤
        (((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ (2 * t) *
          Real.exp (-(2 * t) * b) * q) * ‖WithLp.toLp 2 w‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_replicaExcitationComponent_inverse_le_good_expectation ι ht
  refine ⟨C, hC, ?_⟩
  intro k B Ω hΩ ellC ellR u hu huC huR m w f W b q
  have h := hbound k B Ω ellC ellR u hu huC huR
  dsimp only at h
  rw [replicaExcitationComponent_exp_good_without_auxiliary_eq_trace
    ι Ω k B u (2 * t)] at h
  have hm := replicaGoodConfigurationMarginal_exp_merge_sub_physical_le
    ι Ω hΩ k B u hu (show 0 ≤ 2 * t by positivity)
      (show 2 * (2 * t) ≤ 1 by linarith only [htsmall])
  have hp : 0 ≤ ((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ (2 * t) *
      Real.exp (-(2 * t) * b) := by positivity
  simpa only [mul_assoc] using h.trans (mul_le_mul_of_nonneg_left hm hp)

end Matrix
