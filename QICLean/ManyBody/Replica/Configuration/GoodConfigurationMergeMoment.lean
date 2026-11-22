/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.Configuration.GoodConfigurationMergeTransport
import QICLean.ManyBody.Replica.Configuration.TwoMergeMoment

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

section ReplicaGoodConfigurationIndividualMergeMoment

/-!
# The two individual merge moments of the actual good density

Each original five-factor merge deficit has the same exponential trace
as its actual paired-copy deficit. Thus each retains its own polynomial
moment bound at every real parameter at most one. The component mass is
unchanged in both estimates.

Source: September 24, 2026 area-law manuscript, `07-comparators.tex`,
lines 524–560, `comparator:merge-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix TensorPower PermutationRepresentation
open scoped BigOperators Kronecker Matrix.Norms.Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
variable (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
  ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)

local instance goodIndividualMerge_decidableEqConfig :
    DecidableEq (Config Bᶜ.card ι) := Fintype.decidablePiFintype

local instance goodIndividualMerge_decidableEqCopies (j : Fin 5) :
    DecidableEq (Fin Bᶜ.card → ι j) := Fintype.decidablePiFintype

local instance goodIndividualMerge_decidableEqPair (i j : Fin 5) :
    DecidableEq ((Fin Bᶜ.card → ι i) × (Fin Bᶜ.card → ι j)) := inferInstance

local instance goodIndividualMerge_decidableEqPairMiddle :
    DecidableEq ((((Fin Bᶜ.card → ι 0) × (Fin Bᶜ.card → ι 3)) ×
      ((Fin Bᶜ.card → ι 2) × (Fin Bᶜ.card → ι 4))) ×
        (Fin Bᶜ.card → ι 1)) := inferInstance

private theorem trace_pairMiddle_exp_of_reindex
    (A : Matrix (Config Bᶜ.card ι) (Config Bᶜ.card ι) ℂ)
    (H : Matrix (((Fin Bᶜ.card → ι 0) × (Fin Bᶜ.card → ι 3)) ×
        ((Fin Bᶜ.card → ι 2) × (Fin Bᶜ.card → ι 4)))
      (((Fin Bᶜ.card → ι 0) × (Fin Bᶜ.card → ι 3)) ×
        ((Fin Bᶜ.card → ι 2) × (Fin Bᶜ.card → ι 4))) ℂ)
    (hA : A.submatrix (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm
        (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm =
      H ⊗ₖ (1 : Matrix (Fin Bᶜ.card → ι 1) (Fin Bᶜ.card → ι 1) ℂ)) (a : ℝ) :
    (replicaGoodConfigurationMarginal ι Ω k B u *
      NormedSpace.exp ((a : ℂ) • A)).trace =
      (replicaGoodPairMarginal Ω k B u * NormedSpace.exp ((a : ℂ) • H)).trace := by
  have he : (NormedSpace.exp ((a : ℂ) • A)).submatrix
      (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm
      (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm =
        NormedSpace.exp ((a : ℂ) • H) ⊗ₖ
          (1 : Matrix (Fin Bᶜ.card → ι 1) (Fin Bᶜ.card → ι 1) ℂ) := by
    rw [← reindex_apply, reindex_exp, reindex_apply, submatrix_smul,
      Pi.smul_apply, Pi.smul_apply, hA,
      ← smul_kronecker,
      exp_kronecker_one (n := Fin Bᶜ.card → ι 1) ((a : ℂ) • H)]
  have h := trace_replicaGoodConfigurationMarginal_pairMiddle_mul ι Ω k B u
    (NormedSpace.exp ((a : ℂ) • H))
  rw [← he, submatrix_mul_equiv, trace_submatrix_equiv] at h
  exact h

/-- Each of the two actual merge exponentials satisfies its own moment
bound on the full good-copy density. The original simultaneous symmetry
and one-copy normalization suffice; the component may vanish.
Source: `07-comparators.tex`, lines 524–560. -/
theorem replicaGoodConfigurationMarginal_exp_mergeDeficits_le
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
        (permOp (copyPerm (ι 3) k) σ ⊗ₖ permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u)
    (a : ℝ) (ha : a ≤ 1) :
    let m := Bᶜ.card
    let F := fun S ↦ labelEntropy (subsystemPerm m ι S)
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (replicaGoodConfigurationMarginal ι Ω k B u *
      NormedSpace.exp ((a : ℂ) • (F {0} + F {3} - F {0, 3}))).trace.re ≤
      (((m + 1) ^ ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2) : ℕ) : ℝ) *
        ‖WithLp.toLp 2 w‖ ^ 2 ∧
    (replicaGoodConfigurationMarginal ι Ω k B u *
      NormedSpace.exp ((a : ℂ) • (F {2} + F {4} - F {2, 4}))).trace.re ≤
      (((m + 1) ^ ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2) : ℕ) : ℝ) *
        ‖WithLp.toLp 2 w‖ ^ 2 := by
  intro m F w
  obtain ⟨hC, hR⟩ := fiveFactorPairMiddle_mergeDeficits ι m
  have hm := replicaGoodPairMarginal_exp_mergeDeficits_le Ω hΩ k B u hu a ha
  constructor
  · rw [trace_pairMiddle_exp_of_reindex ι Ω k B u _ _ hC a]
    exact hm.1
  · rw [trace_pairMiddle_exp_of_reindex ι Ω k B u _ _ hR a]
    exact hm.2

end Matrix
end

end ReplicaGoodConfigurationIndividualMergeMoment
