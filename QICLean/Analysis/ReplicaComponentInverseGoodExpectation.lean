/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaBadCopyExponential
import QICLean.Analysis.ReplicaJointAuxiliaryExponential
import QICLean.Representation.ReplicaGroupedInverse

/-!
# The inverse metric on an actual excitation component

The whole-space inverse bound, the good/bad subgroup comparison, the
derived bad-copy symmetry and the two original auxiliary label conditions
give one estimate on the actual excitation component. Its remaining
exponential contains only good-copy labels, with both auxiliary entropy
terms removed. The scalar retains the two original labels, both auxiliary
dimensions, and all three binomial corrections.

The polynomial constant is chosen for the fixed five-factor system and
the positive parameter before the number of copies, excitation subset,
labels or original vector. No normalization of the ground vector or of
an excitation component is used in this step.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 441–508, `comparator:whole-inverse`,
`comparator:good-auxiliary`, and `comparator:merge-decomposition`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaComponentInverseGoodExpectation_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The inverse squared replica metric on each actual excitation component
is bounded by its good-copy exponential after joint auxiliary removal.
The only support and symmetry premises concern the original vector.
Source: `07-comparators.tex`, lines 441–508. -/
theorem exists_replicaExcitationComponent_inverse_le_good_expectation
    {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (B : Finset (Fin k))
      (Ω : ι 0 × (ι 1 × ι 2) → ℂ)
      (ellC ellR : IrrepLabel (Equiv.Perm (Fin k)))
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
      let e := replicaGoodBadSplit B
      let w := (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
          ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
      let f := w ∘ fiveFactorCopiesEquiv ι k
      let W := replicaMetric ι t k
      let Lg := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₁ e))
      let b := Real.log ellC.dim + Real.log ellR.dim -
        (B.card : ℝ) * (Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))) -
          2 * Real.log (k.choose B.card)
      (star f ⬝ᵥ ((((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)⁻¹ *ᵥ f)).re ≤
        (((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ (2 * t) *
          Real.exp (-(2 * t) * b)) *
            (star f ⬝ᵥ (NormedSpace.exp ((-(2 * t)) •
              (Lg {0, 3} + Lg {2, 4} - Lg {1} - (Lg {3} + Lg {4}))) *ᵥ f)).re := by
  obtain ⟨C, hC, hwhole⟩ := exists_replicaMetric_inv_square_le_grouped_exp ι ht
  refine ⟨C, hC, ?_⟩
  intro k B Ω ellC ellR u hu huC huR e w f W Lg b
  let p := ((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ (2 * t)
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have ha : 0 ≤ 2 * t := by positivity
  have hmatrix := hwhole Bᶜ.card B.card k e {0, 3} {1} {2, 4}
    (by decide) (by decide) (by decide)
  have hq := re_dotProduct_mulVec_le_of_le hmatrix f
  simp only [smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul] at hq
  have hbad := replicaExcitationComponent_exp_grouped_le_good ι Ω k B u hu ha
  have haux := replicaExcitationComponent_exp_good_le_without_auxiliary
    ι Ω k B ellC ellR u huC huR ha
  have h := hq.trans ((mul_le_mul_of_nonneg_left hbad hp).trans
    (mul_le_mul_of_nonneg_left haux hp))
  simpa only [p, mul_assoc] using h

end Matrix
