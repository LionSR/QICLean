/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaComponentInverseGoodExpectation
import QICLean.Analysis.ReplicaGoodConfigurationExpectation
import QICLean.Analysis.ReplicaGoodConfigurationSharpMoment

/-!
# The sharp inverse estimate on each actual excitation component

The inverse metric on an actual excitation component is compared with the
exponential trace in its actual good-copy density. The signed one-copy
moment bounds for the original three physical marginals and the two merge
moments yield the sharp estimate. The component mass, auxiliary label
terms, binomial corrections and polynomial losses remain explicit.

The polynomial constant is chosen before the copy number, excitation
subset, state, auxiliary labels, vector and one-copy moment parameters.
The regional one-copy moment bounds are hypotheses; their geometric
uniformization is a separate step. A vanishing component is included.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 441--560, `comparator:component-inverse`
and `comparator:signed-label-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaComponentInverseSharp_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual inverse squared band metric satisfies the conditional
sharp component estimate for the original three physical marginals.
The same original symmetry and two auxiliary labels are retained, and
all scalar factors multiply the mass of the literal excitation component.
Source: `07-comparators.tex`, lines 441--560, `comparator:component-inverse`.
-/
theorem exists_replicaExcitationComponent_inverse_sharp_le
    {t : ℝ} (ht : 0 < t) :
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
      ∀ (K r : ℝ),
      (∀ j : Fin 3, ∀ v : ℝ, |v| ≤ r →
        Real.log (Entropy.surprisalMoment
          (posSemidef_physicalSingletonDensity ι Ω j).isHermitian.eigenvalues v) ≤
        v * vonNeumannEntropy (physicalSingletonDensity ι Ω j)
          (posSemidef_physicalSingletonDensity ι Ω j).isHermitian + K * v ^ 2) →
      20 * t ≤ r → 20 * t ≤ 1 →
      let m := Bᶜ.card
      let w := (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
          ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
      let f := w ∘ fiveFactorCopiesEquiv ι k
      let W := replicaMetric ι t k
      let b := Real.log ellC.dim + Real.log ellR.dim -
        (B.card : ℝ) * (Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))) -
          2 * Real.log (k.choose B.card)
      let S := fun j => vonNeumannEntropy (physicalSingletonDensity ι Ω j)
        (posSemidef_physicalSingletonDensity ι Ω j).isHermitian
      let d := fun j : Fin 5 => Fintype.card (ι j)
      let Λ := ((((d 0 * d 3) ^ 2 : ℕ) : ℝ) + (((d 2 * d 4) ^ 2 : ℕ) : ℝ) +
        ((d 0 ^ 2 : ℕ) : ℝ) / 2 + ((d 2 ^ 2 : ℕ) : ℝ) / 2) / 5
      let L := -(m : ℝ) * (2 * t) * (S 0 + S 2 - S 1) +
        25 * (m : ℝ) * K * (2 * t) ^ 2 + Λ * Real.log ((m : ℝ) + 1)
      (star f ⬝ᵥ ((((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)⁻¹ *ᵥ f)).re ≤
        (((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ (2 * t) *
          Real.exp (-(2 * t) * b) * Real.exp L) * ‖WithLp.toLp 2 w‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_replicaExcitationComponent_inverse_le_good_expectation ι ht
  refine ⟨C, hC, ?_⟩
  intro k B Ω hΩ ellC ellR u hu huC huR K r hmoment htr htone m w f W b S d Λ L
  have h := hbound k B Ω ellC ellR u hu huC huR
  dsimp only at h
  rw [replicaExcitationComponent_exp_good_without_auxiliary_eq_trace
    ι Ω k B u (2 * t)] at h
  have hm := replicaGoodConfigurationMarginal_exp_merge_sub_physical_sharp_le
    ι Ω k B u hΩ hu hmoment (show 0 ≤ 2 * t by positivity)
      (show 10 * (2 * t) ≤ r by linarith only [htr])
      (show 10 * (2 * t) ≤ 1 by linarith only [htone])
  let p := ((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ (2 * t) *
    Real.exp (-(2 * t) * b)
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  calc
    _ ≤ p * (‖WithLp.toLp 2 w‖ ^ 2 * Real.exp L) :=
      h.trans (mul_le_mul_of_nonneg_left hm hp)
    _ = (p * Real.exp L) * ‖WithLp.toLp 2 w‖ ^ 2 := by ring

end Matrix
