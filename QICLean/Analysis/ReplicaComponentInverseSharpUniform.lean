/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaComponentInverseSharp
import QICLean.Analysis.ReplicaComponentUniformRate
import QICLean.Analysis.PhysicalSingletonEntropy

/-!
# A sharp component rate uniform over the excitation subset

A bound on the sum of the two original auxiliary label logarithms and
an upper bound on the number of excited copies give a common rate for
all actual excitation components. The physical entropy difference is
nonnegative by purity and subadditivity of the original unit state.
The auxiliary logarithmic dimensions are nonnegative because their
coordinate spaces are nonempty.

All three binomial corrections and the good-copy polynomial loss are
retained explicitly in the uniform rate. The constant is chosen before
the copy number, state, auxiliary labels, vector, moment data and cutoff.
The common lower bound for the original label logarithms is a hypothesis;
its selected-label asymptotics are a separate step.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550--590, `comparator:component-inverse`
and `comparator:inverse-compression`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaComponentInverseSharpUniform_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The sharp inverse estimate is uniform over every actual excitation
subset below the prescribed fraction. The original singleton moment
bounds, vector symmetry and auxiliary label conditions are retained.
Only the summed logarithmic lower bound on the two original labels is
supplied; all physical sign conditions follow from the original data.
Source: `07-comparators.tex`, lines 550--590. -/
theorem exists_replicaExcitationComponent_inverse_sharp_uniform_le
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
      20 * t ≤ r → 20 * t ≤ 1 → 0 ≤ K →
      ∀ (τ S ε : ℝ), 0 ≤ τ → τ ≤ 1 / 2 → (B.card : ℝ) ≤ τ * k →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let w := (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
          ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
      let f := w ∘ fiveFactorCopiesEquiv ι k
      let W := replicaMetric ι t k
      let Sj := fun j => vonNeumannEntropy (physicalSingletonDensity ι Ω j)
        (posSemidef_physicalSingletonDensity ι Ω j).isHermitian
      let g := Sj 0 + Sj 2 - Sj 1
      let d := Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))
      let D := fun j : Fin 5 => Fintype.card (ι j)
      let Λ := ((((D 0 * D 3) ^ 2 : ℕ) : ℝ) + (((D 2 * D 4) ^ 2 : ℕ) : ℝ) +
        ((D 0 ^ 2 : ℕ) : ℝ) / 2 + ((D 2 ^ 2 : ℕ) : ℝ) / 2) / 5
      (star f ⬝ᵥ ((((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)⁻¹ *ᵥ f)).re ≤
        (((k : ℝ) + 2) ^ (C + Λ) * Real.exp
          (-(k : ℝ) * (2 * t) *
            (2 * S + (1 - τ) * g - τ * d - 3 * Real.binEntropy τ) +
            (2 * t) * ε + 25 * (k : ℝ) * K * (2 * t) ^ 2)) *
              ‖WithLp.toLp 2 w‖ ^ 2 := by
  obtain ⟨C, hC, hsharp⟩ := exists_replicaExcitationComponent_inverse_sharp_le ι ht
  refine ⟨C, hC, ?_⟩
  intro k B Ω hΩ ellC ellR u hu huC huR K r hmoment htr htone hK
    τ S ε hτ hτhalf hB hlabel w f W Sj g d D Λ
  have hg : 0 ≤ g := physicalSingletonEntropy_outer_sub_middle_nonneg ι Ω hΩ
  have hdim (j : Fin 5) : 0 ≤ Real.log (Fintype.card (ι j)) :=
    Real.log_natCast_nonneg _
  have hd : 0 ≤ d := add_nonneg (hdim 3) (hdim 4)
  have hΛ : 0 ≤ Λ := by dsimp only [Λ]; positivity
  have hBk : B.card ≤ k := by
    simpa only [Fintype.card_fin] using B.card_le_univ
  have hm : Bᶜ.card = k - B.card := by
    simp only [Finset.card_compl, Fintype.card_fin]
  have hfactor := Real.replica_component_prefactor_le_uniform hBk hτ hτhalf hB
    (show 0 ≤ 2 * t by positivity) hd hg hK hΛ C S ε
    (Real.log ellC.dim + Real.log ellR.dim) hlabel
  have h := hsharp k B Ω hΩ ellC ellR u hu huC huR K r hmoment htr htone
  dsimp only at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖WithLp.toLp 2 w‖)
  simpa only [← hm] using hfactor

end Matrix
