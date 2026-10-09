/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralExponentialDrop
import QICLean.Analysis.ReplicaGoodConfigurationMergeMoment
import QICLean.Representation.CompatiblePhysicalLabel

/-!
# Removing the physical deficit on the actual good density

The actual good density is supported on the physical symmetric subspace.
The nonnegative spectral projection of the physical merge deficit contains
this subspace and commutes with both physical/auxiliary merge deficits.
It therefore supplies an invariant support on which the negative physical
exponential can be removed. Combining this comparison with the actual
two-merge moment gives the rough good-copy estimate.

The individual merges need not preserve the physical symmetric subspace.
The proof instead uses the compatible spectral projection whose invariance
follows from the actual nested and disjoint permutation actions.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 501–555, `comparator:merge-decomposition`
and `comparator:merge-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
variable (k : ℕ) (B : Finset (Fin k))
variable (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
  ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)

local instance replicaGoodPhysicalExponential_decidableEqConfig :
    DecidableEq (Config Bᶜ.card ι) := Fintype.decidablePiFintype

include hΩ

/-- On the actual five-factor good density, the negative physical deficit
exponential may be removed while retaining both actual merge deficits.
Only the one-copy vector is normalized. Source: `07-comparators.tex`,
lines 501–555. -/
theorem trace_replicaGoodConfigurationMarginal_exp_merge_sub_physical_le
    {a : ℝ} (ha : 0 ≤ a) :
    let F := fun S => labelEntropy (subsystemPerm Bᶜ.card ι S)
    let D := (F {0} + F {3} - F {0, 3}) + (F {2} + F {4} - F {2, 4})
    let G := physicalMergeDeficit ι Bᶜ.card
    let ρ := replicaGoodConfigurationMarginal ι Ω k B u
    (ρ * NormedSpace.exp ((a : ℂ) • (D - G))).trace.re ≤
      (ρ * NormedSpace.exp ((a : ℂ) • D)).trace.re := by
  intro F D G ρ
  have hG : G.IsHermitian :=
    ((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
      (isHermitian_labelObservable _ _)
  have hD : D.IsHermitian :=
    (((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
      (isHermitian_labelObservable _ _)).add
        (((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
          (isHermitian_labelObservable _ _))
  let P := spectralProjectionGE G 0
  have hPρ : P * ρ = ρ := by
    have hs := symProj_mul_replicaGoodConfigurationMarginal ι Ω hΩ k B u
    calc
      P * ρ = P * (symProj (subsystemPerm Bᶜ.card ι {0, 1, 2}) * ρ) := by rw [hs]
      _ = ρ := by
        rw [← mul_assoc, spectralProjectionGE_physicalMergeDeficit_mul_symProj, hs]
  have hcomm (f : ℝ → ℝ) : Commute (cfc f G) D := by
    obtain ⟨hC, hR⟩ := commute_cfc_physicalMergeDeficit_mergeDeficits ι Bᶜ.card f
    exact hC.add_right hR
  have hDG : Commute D G := by
    simpa only [cfc_id' ℝ G hG.isSelfAdjoint] using (hcomm id).symm
  exact PosSemidef.re_trace_mul_exp_smul_sub_le_of_spectralProjectionGE_mul
    (posSemidef_replicaGoodConfigurationMarginal ι Ω k B u) hG hD hDG.symm ha hPρ

/-- The complete good-copy exponential has the same polynomial upper bound
as the paired merge moment. The original vector is simultaneously symmetric
and the one-copy ground vector is unit; its excitation component may vanish.
Source: `07-comparators.tex`, lines 501–555. -/
theorem replicaGoodConfigurationMarginal_exp_merge_sub_physical_le
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
        (permOp (copyPerm (ι 3) k) σ ⊗ₖ
          permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u)
    {a : ℝ} (ha : 0 ≤ a) (ha' : 2 * a ≤ 1) :
    let m := Bᶜ.card
    let F := fun S => labelEntropy (subsystemPerm m ι S)
    let D := (F {0} + F {3} - F {0, 3}) + (F {2} + F {4} - F {2, 4})
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (replicaGoodConfigurationMarginal ι Ω k B u *
      NormedSpace.exp ((a : ℂ) • (D - physicalMergeDeficit ι m))).trace.re ≤
      ((((m + 1) ^ ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2) : ℕ) : ℝ) +
        (((m + 1) ^ ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2) : ℕ) : ℝ)) / 2 *
          ‖WithLp.toLp 2 w‖ ^ 2 := by
  intro m F D w
  exact (trace_replicaGoodConfigurationMarginal_exp_merge_sub_physical_le
    ι Ω hΩ k B u ha).trans
      (replicaGoodConfigurationMarginal_exp_sum_mergeDeficit_le ι Ω k B u hΩ hu a ha')

end Matrix
