/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationMergeMoment

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
  classical
  have he : (NormedSpace.exp ((a : ℂ) • A)).submatrix
      (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm
      (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm =
        NormedSpace.exp ((a : ℂ) • H) ⊗ₖ
          (1 : Matrix (Fin Bᶜ.card → ι 1) (Fin Bᶜ.card → ι 1) ℂ) := by
    rw [← reindex_apply, reindex_exp, reindex_apply, submatrix_smul, hA,
      ← smul_kronecker, exp_kronecker_one]
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
