/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationProduct
import QICLean.Analysis.KroneckerExponential
import QICLean.Algebra.TensorPowerPartialTrace
import QICLean.Representation.LabelProjectors
import QICLean.Representation.TensorPowerAction

/-!
# Regional moments in the actual good-copy density

Choose any bipartite decomposition of the original physical space. After
collecting the good copies of the first factor, its expectation in the
actual five-factor density is the expectation in the tensor power of the
original regional marginal, multiplied by the mass of the excitation
component. In particular, both signs of the exponential label observable
are included without a nonzero-component assumption.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550–560, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
open TensorPower PermutationRepresentation

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
variable (k : ℕ) (B : Finset (Fin k))
variable (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
  ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
variable {Q T : Type*} [Fintype Q] [DecidableEq Q] [Fintype T] [DecidableEq T]

include hΩ

/-- Every actual regional observable is evaluated in the tensor power of
the original one-copy marginal. The displayed equivalence is the chosen
bipartite decomposition itself; no transport identity is assumed.
Source: `07-comparators.tex`, lines 550–560. -/
theorem trace_replicaGoodConfigurationMarginal_regional_mul
    (e : (ι 0 × (ι 1 × ι 2)) ≃ Q × T)
    (H : Matrix (Fin Bᶜ.card → Q) (Fin Bᶜ.card → Q) ℂ) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    let c := copiesProductEquiv e Bᶜ.card
    let Hphysical := (H ⊗ₖ
      (1 : Matrix (Fin Bᶜ.card → T) (Fin Bᶜ.card → T) ℂ)).submatrix c c
    (((replicaGoodConfigurationMarginal ι Ω k B u).submatrix
      (fiveFactorCopiesEquiv ι Bᶜ.card).symm (fiveFactorCopiesEquiv ι Bᶜ.card).symm) *
      (Hphysical ⊗ₖ (1 : Matrix ((Fin Bᶜ.card → ι 3) × (Fin Bᶜ.card → ι 4))
        ((Fin Bᶜ.card → ι 3) × (Fin Bᶜ.card → ι 4)) ℂ))).trace =
      (‖WithLp.toLp 2 w‖ ^ 2 : ℂ) *
        (finKronecker (fun _ : Fin Bᶜ.card =>
          partialTraceRight ((vecMulVec Ω (star Ω)).submatrix e.symm e.symm)) * H).trace := by
  intro w c Hphysical
  rw [trace_replicaGoodConfigurationMarginal_physical_mul ι Ω hΩ k B u]
  congr 1
  let ρ := finKronecker (fun _ : Fin Bᶜ.card => vecMulVec Ω (star Ω))
  calc
    (ρ * Hphysical).trace =
        ((ρ * Hphysical).submatrix c.symm c.symm).trace :=
      (trace_submatrix_equiv c.symm (ρ * Hphysical)).symm
    _ = ((ρ.submatrix c.symm c.symm) *
        (H ⊗ₖ (1 : Matrix (Fin Bᶜ.card → T) (Fin Bᶜ.card → T) ℂ))).trace := by
      rw [← submatrix_mul_equiv _ _ c.symm c.symm c.symm]
      simp only [Hphysical, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
    _ = _ := by
      rw [← trace_partialTraceRight_mul,
        partialTraceRight_finKronecker_reindex]

/-- The signed regional label moment of the same actual good-copy density
is the iid moment times the squared norm of the excitation component.
The exponent is an arbitrary real number. Source: `07-comparators.tex`,
lines 550–560. -/
theorem trace_replicaGoodConfigurationMarginal_regional_exp_labelEntropy
    (e : (ι 0 × (ι 1 × ι 2)) ≃ Q × T) (a : ℝ) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    let c := copiesProductEquiv e Bᶜ.card
    let E := NormedSpace.exp ((a : ℂ) • labelEntropy (copyPerm Q Bᶜ.card))
    let Ephysical := (E ⊗ₖ
      (1 : Matrix (Fin Bᶜ.card → T) (Fin Bᶜ.card → T) ℂ)).submatrix c c
    (((replicaGoodConfigurationMarginal ι Ω k B u).submatrix
      (fiveFactorCopiesEquiv ι Bᶜ.card).symm (fiveFactorCopiesEquiv ι Bᶜ.card).symm) *
      (Ephysical ⊗ₖ (1 : Matrix ((Fin Bᶜ.card → ι 3) × (Fin Bᶜ.card → ι 4))
        ((Fin Bᶜ.card → ι 3) × (Fin Bᶜ.card → ι 4)) ℂ))).trace =
      (‖WithLp.toLp 2 w‖ ^ 2 : ℂ) *
        (finKronecker (fun _ : Fin Bᶜ.card =>
          partialTraceRight ((vecMulVec Ω (star Ω)).submatrix e.symm e.symm)) * E).trace := by
  exact trace_replicaGoodConfigurationMarginal_regional_mul ι Ω hΩ k B u e _

end Matrix
