/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationMergeTransport
import QICLean.Analysis.ReplicaTwoMergeMoment

/-!
# Merge moments in the actual five-factor good density

The two merge deficits on the good five-factor configuration space have
exactly the same exponential expectation as their paired-copy operators
in the actual common good-pair marginal. Applying the paired moment
estimate gives its arithmetic-mean polynomial bound, with the squared
norm of the same excitation component. No normalization of that component
or of either marginal is required.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`07-comparators.tex`, lines 520–555, `comparator:merge-moments` and
`comparator:component-inverse`. The estimate below is the arithmetic-mean
consequence for the two merges, not the complete inverse-filter estimate.
-/

noncomputable section
open Matrix TensorPower PermutationRepresentation
open scoped BigOperators Kronecker Matrix.Norms.Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
variable (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
  ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)

local instance goodConfigurationMergeMoment_decidableEqConfig :
    DecidableEq (Config Bᶜ.card ι) := Fintype.decidablePiFintype

/-- The paired merge exponential has the same trace pairing in the full
good-copy density and its actual common good-pair marginal. No symmetry
or normalization is needed for this identity, and the parameter is any
real number. Source: `07-comparators.tex`, lines 520–549. -/
theorem trace_replicaGoodConfigurationMarginal_exp_sum_mergeDeficit (a : ℝ) :
    let m := Bᶜ.card
    let F := fun S ↦ labelEntropy (subsystemPerm m ι S)
    let DC := pairMergeDeficit (ι 0) (ι 3) m ⊗ₖ
      (1 : Matrix ((Fin m → ι 2) × (Fin m → ι 4))
        ((Fin m → ι 2) × (Fin m → ι 4)) ℂ)
    let DR := (1 : Matrix ((Fin m → ι 0) × (Fin m → ι 3))
      ((Fin m → ι 0) × (Fin m → ι 3)) ℂ) ⊗ₖ pairMergeDeficit (ι 2) (ι 4) m
    (replicaGoodConfigurationMarginal ι Ω k B u * NormedSpace.exp ((a : ℂ) •
      ((F {0} + F {3} - F {0, 3}) + (F {2} + F {4} - F {2, 4})))).trace =
      (replicaGoodPairMarginal Ω k B u *
        NormedSpace.exp ((a : ℂ) • (DC + DR))).trace := by
  intro m F DC DR
  have h := trace_replicaGoodConfigurationMarginal_pairMiddle_mul ι Ω k B u
    (NormedSpace.exp ((a : ℂ) • (DC + DR)))
  rw [← fiveFactorPairMiddle_exp_sum_mergeDeficit ι m a,
    submatrix_mul_equiv, trace_submatrix_equiv] at h
  exact h

/-- The two actual five-factor merge deficits satisfy the paired
arithmetic-mean moment bound. The original vector is fixed by the
simultaneous copy action, the one-copy physical vector has norm one,
and the only restriction on the exponential parameter is `2 * a ≤ 1`.
The mass is the norm squared of the original excitation component.
Source: `07-comparators.tex`, lines 520–555. -/
theorem replicaGoodConfigurationMarginal_exp_sum_mergeDeficit_le
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
        (permOp (copyPerm (ι 3) k) σ ⊗ₖ
          permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u)
    (a : ℝ) (ha : 2 * a ≤ 1) :
    let m := Bᶜ.card
    let F := fun S ↦ labelEntropy (subsystemPerm m ι S)
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (replicaGoodConfigurationMarginal ι Ω k B u * NormedSpace.exp ((a : ℂ) •
      ((F {0} + F {3} - F {0, 3}) + (F {2} + F {4} - F {2, 4})))).trace.re ≤
      ((((m + 1) ^ ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2) : ℕ) : ℝ) +
        (((m + 1) ^ ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2) : ℕ) : ℝ)) / 2 *
          ‖WithLp.toLp 2 w‖ ^ 2 := by
  intro m F w
  rw [trace_replicaGoodConfigurationMarginal_exp_sum_mergeDeficit]
  exact replicaGoodPairMarginal_exp_sum_mergeDeficit_le Ω hΩ k B u hu a ha

end Matrix
