/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationReduction
import QICLean.Analysis.SpectralExponentialDrop

/-!
# A rough exponential estimate for an excitation component

The density retains all five factors on every good copy of the same
excitation component. Its physical symmetric support gives support on the
closed nonnegative spectral subspace of the physical deficit. The two actual
merge deficits commute with that deficit, so the supported trace inequality
removes it from the exponent. The actual sum-merge moment then bounds the
remaining trace by an arithmetic-mean polynomial times the component mass.

No full-space positivity of the physical deficit, normalization of the
component, or supplied support or moment identity is assumed. Zero components,
zero copies and an empty set of good copies are included. This is an auxiliary
exponential estimate before the inverse metric and the good auxiliary scalar
factor are introduced; it does not assert the full inverse comparison.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 513–555, `comparator:merge-decomposition`,
`comparator:merge-moments` and `comparator:component-inverse`, at source commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.Operator

namespace Matrix

/-- The actual full good-copy density has a rough exponential bound with
the squared norm of the same excitation component retained literally. -/
theorem replicaGoodConfigurationMarginal_exp_mergeDeficits_sub_physicalMergeDeficit_le
    (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
        (permOp (copyPerm (ι 3) k) σ ⊗ₖ permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u)
    (a : ℝ) (ha : 0 ≤ a) (ha2 : 2 * a ≤ 1) :
    let m := Bᶜ.card
    let ρ := replicaGoodConfigurationMarginal ι Ω k B u
    let DC := labelEntropy (subsystemPerm m ι {0}) +
      labelEntropy (subsystemPerm m ι {3}) - labelEntropy (subsystemPerm m ι {0, 3})
    let DR := labelEntropy (subsystemPerm m ι {2}) +
      labelEntropy (subsystemPerm m ι {4}) - labelEntropy (subsystemPerm m ι {2, 4})
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (ρ * NormedSpace.exp ((a : ℂ) •
      (DC + DR - physicalMergeDeficit ι m))).trace.re ≤
      ((((m + 1) ^ ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2) : ℕ) : ℝ) +
        (((m + 1) ^ ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2) : ℕ) : ℝ)) / 2 *
          ‖WithLp.toLp 2 w‖ ^ 2 := by
  classical
  intro m ρ DC DR w
  have hρ : ρ.PosSemidef :=
    (posSemidef_vecMulVec_self_star (R := ℂ) _).partialTraceRight
  have hF (A : Finset (Fin 5)) :
      (labelEntropy (subsystemPerm m ι A)).IsHermitian :=
    isHermitian_labelObservable _ _
  have hG : (physicalMergeDeficit ι m).IsHermitian :=
    ((hF {0}).add (hF {2})).sub (hF {1})
  have hDC : DC.IsHermitian := ((hF {0}).add (hF {3})).sub (hF {0, 3})
  have hDR : DR.IsHermitian := ((hF {2}).add (hF {4})).sub (hF {2, 4})
  have hc := commute_cfc_physicalMergeDeficit_mergeDeficits ι m (id : ℝ → ℝ)
  rw [cfc_id ℝ (physicalMergeDeficit ι m) hG.isSelfAdjoint] at hc
  have hGH : Commute (physicalMergeDeficit ι m) (DC + DR) :=
    hc.1.add_right hc.2
  have hs : spectralProjectionGE (physicalMergeDeficit ι m) 0 * ρ = ρ :=
    spectralProjectionGE_physicalMergeDeficit_mul_replicaGoodConfigurationMarginal
      ι Ω hΩ k B u
  calc
    _ ≤ (ρ * NormedSpace.exp ((a : ℂ) • (DC + DR))).trace.re :=
      hρ.re_trace_mul_exp_smul_sub_le_of_spectralProjectionGE_mul
        hG (hDC.add hDR) hGH ha hs
    _ ≤ _ := replicaGoodConfigurationMarginal_exp_sum_mergeDeficit_le
      ι Ω hΩ k B u hu a ha2

end Matrix
