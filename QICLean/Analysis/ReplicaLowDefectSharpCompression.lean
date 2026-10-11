/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaComponentInverseSharpUniform
import QICLean.Analysis.ReplicaLowDefectProjection
import QICLean.Analysis.ProjectionQuadraticBound
import QICLean.Representation.ReplicaDisjointMetricPositivity

/-!
# Sharp inverse compression on the actual low-defect sector

The low-defect projection includes simultaneous copy symmetry and the two
original auxiliary labels. Every vector in its range therefore satisfies
the uniform sharp excitation-component bound. Counting the retained
excitation subsets gives the compressed operator inequality for the
actual inverse squared metric, in the literal physical and auxiliary
coordinates.

Positivity of the inverse metric follows from the pairwise disjoint
subsystems. The projection, its range conditions and every component
estimate are derived; no vector, commutation with the metric, or supplied
component estimate occurs in the final hypotheses.

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

local instance replicaLowDefectSharpCompression_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual inverse squared metric has the sharp operator upper bound
on the original symmetric, fixed-label low-defect sector. The constant
precedes all state, label, copy, moment and cutoff data. The one-copy
moment bounds and the summed lower bound on the original label logarithms
remain explicit. Source: `07-comparators.tex`, lines 550--590,
`comparator:inverse-compression`. -/
theorem exists_replicaLowDefectProjection_inverse_sharp_compression_le
    {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ)
      (Ω : ι 0 × (ι 1 × ι 2) → ℂ), ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (K r : ℝ),
      (∀ j : Fin 3, ∀ v : ℝ, |v| ≤ r →
        Real.log (Entropy.surprisalMoment
          (posSemidef_physicalSingletonDensity ι Ω j).isHermitian.eigenvalues v) ≤
        v * vonNeumannEntropy (physicalSingletonDensity ι Ω j)
          (posSemidef_physicalSingletonDensity ι Ω j).isHermitian + K * v ^ 2) →
      20 * t ≤ r → 20 * t ≤ 1 → 0 ≤ K →
      ∀ (τ S ε : ℝ), 0 ≤ τ → τ ≤ 1 / 2 →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let P := replicaLowDefectProjection (C := ι 3) (R := ι 4) Ω k ellC ellR τ
      let W := replicaMetric ι t k
      let A := ((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2
      let η := fiveFactorCopiesEquiv ι k
      let Sj := fun j => vonNeumannEntropy (physicalSingletonDensity ι Ω j)
        (posSemidef_physicalSingletonDensity ι Ω j).isHermitian
      let g := Sj 0 + Sj 2 - Sj 1
      let d := Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))
      let D := fun j : Fin 5 => Fintype.card (ι j)
      let Λ := ((((D 0 * D 3) ^ 2 : ℕ) : ℝ) + (((D 2 * D 4) ^ 2 : ℕ) : ℝ) +
        ((D 0 ^ 2 : ℕ) : ℝ) / 2 + ((D 2 ^ 2 : ℕ) : ℝ) / 2) / 5
      let c := ((k : ℝ) + 2) ^ (C + Λ) * Real.exp
        (-(k : ℝ) * (2 * t) *
          (2 * S + (1 - τ) * g - τ * d - 3 * Real.binEntropy τ) +
          (2 * t) * ε + 25 * (k : ℝ) * K * (2 * t) ^ 2)
      P * (A⁻¹).submatrix η.symm η.symm * P ≤
        (((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) * c) • P := by
  obtain ⟨C, hC, hcomponent⟩ :=
    exists_replicaExcitationComponent_inverse_sharp_uniform_le ι ht
  refine ⟨C, hC, ?_⟩
  intro k Ω hΩ ellC ellR K r hmoment htr htone hK τ S ε hτ hτhalf hlabel
    P W A η Sj g d D Λ c
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hA : A.PosDef := posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq ι ht.le k
    (by decide) (by decide) (by decide)
  have hH : ((A⁻¹).submatrix η.symm η.symm).PosSemidef :=
    hA.inv.posSemidef.submatrix η.symm
  refine replicaLowDefectProjection_compression_le_of_component_bounds
    Ω hΩ k ellC ellR hτ hτhalf hc hH ?_
  intro u hu huC huR B hB w
  have h := hcomponent k B Ω hΩ ellC ellR u hu huC huR K r hmoment htr htone hK
    τ S ε hτ hτhalf hB hlabel
  change (star w ⬝ᵥ ((A⁻¹).submatrix η.symm η.symm *ᵥ w)).re ≤
    c * ‖WithLp.toLp 2 w‖ ^ 2
  rw [star_dotProduct_submatrix_equiv]
  exact h

end Matrix
