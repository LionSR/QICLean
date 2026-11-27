/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.Configuration.GoodConfigurationExpectation
import QICLean.ManyBody.Replica.Configuration.GoodConfigurationSharpMoment
import QICLean.ManyBody.Replica.Configuration.BadCopyExponential
import QICLean.ManyBody.Replica.Configuration.JointAuxiliaryExponential
import QICLean.ManyBody.Replica.Metric.GroupedInverse
import QICLean.Analysis.Real.ExcitationSubsetCounts
import QICLean.ManyBody.Replica.Configuration.PhysicalSingletonEntropy
import QICLean.Representation.Replica.LowDefectProjection
import QICLean.Analysis.Order.ProjectionQuadraticBound
import QICLean.ManyBody.Replica.Metric.DisjointMetricPositivity

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

## Main results

* `Matrix.replicaComponentInverseGoodExpectation_decidableEqConfig`,
  `Matrix.exists_replicaExcitationComponent_inverse_le_good_expectation`: the inverse metric on an
  actual excitation component.
* `Matrix.replicaComponentInverseSharpUniform_decidableEqConfig`,
  `Matrix.exists_replicaExcitationComponent_inverse_sharp_uniform_le`: A sharp component rate
  uniform over the excitation subset.
* `Matrix.replicaLowDefectSharpCompression_decidableEqConfig`,
  `Matrix.exists_replicaLowDefectProjection_inverse_sharp_compression_le`: sharp inverse compression
  on the actual low-defect sector.
-/

section ComponentInverseGoodExpectation

/-!
## The inverse metric on an actual excitation component

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

end

end ComponentInverseGoodExpectation

section ComponentInverseSharp

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

end

end ComponentInverseSharp

section ComponentInverseSharpUniform

/-!
## A sharp component rate uniform over the excitation subset

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

end

end ComponentInverseSharpUniform

section LowDefectSharpCompression

/-!
## Sharp inverse compression on the actual low-defect sector

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

end

end LowDefectSharpCompression
