/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PhysicalSingletonDensity
import QICLean.Entropy.IidSchurExponentialMoments

/-!
# Signed physical moments of the actual good-copy density

The three one-copy marginals are the partial traces of the original pure
physical state in its specified singleton coordinates. An explicit
logarithmic surprisal bound on any such marginal gives both signs of the
actual singleton label moment, with precisely the mass of the original
excitation component. No component is normalized or reselected.

Source: September 24, 2026 area-law manuscript, `07-comparators.tex`,
lines 218–238 and 550–560, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker Matrix.Norms.Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (Ω : ι 0 × (ι 1 × ι 2) → ℂ)

variable (k : ℕ) (B : Finset (Fin k))
variable (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
  ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)

local instance goodSignedMoment_decidableEqConfig :
    DecidableEq (Config Bᶜ.card ι) := Fintype.decidablePiFintype

/-- A conditional one-copy surprisal bound gives both signed singleton
moments in the same actual good density. The negative sign has coefficient
`2 K` and its explicit Schur polynomial term. Source:
`07-comparators.tex`, lines 218–238 and 550–560. -/
theorem replicaGoodConfigurationMarginal_exp_signed_singleton_le
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (j : Fin 3) {K r : ℝ}
    (hmoment : ∀ v : ℝ, |v| ≤ r →
      Real.log (Entropy.surprisalMoment
        (posSemidef_physicalSingletonDensity ι Ω j).isHermitian.eigenvalues v) ≤
      v * vonNeumannEntropy (physicalSingletonDensity ι Ω j)
        (posSemidef_physicalSingletonDensity ι Ω j).isHermitian + K * v ^ 2)
    {a : ℝ} (ha : 0 ≤ a) (har : 2 * a ≤ r) (ha1 : 2 * a ≤ 1) :
    let m := Bᶜ.card
    let S := vonNeumannEntropy (physicalSingletonDensity ι Ω j)
      (posSemidef_physicalSingletonDensity ι Ω j).isHermitian
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    let F := labelEntropy (subsystemPerm m ι {j.castAdd 2})
    (replicaGoodConfigurationMarginal ι Ω k B u *
      NormedSpace.exp ((a : ℂ) • F)).trace.re ≤
      ‖WithLp.toLp 2 w‖ ^ 2 * Real.exp (a * ((m : ℝ) * S) + (m : ℝ) * K * a ^ 2) ∧
    (replicaGoodConfigurationMarginal ι Ω k B u *
      NormedSpace.exp (((-a : ℝ) : ℂ) • F)).trace.re ≤
      ‖WithLp.toLp 2 w‖ ^ 2 * Real.exp ((-a) * ((m : ℝ) * S) +
        (2 * (m : ℝ) * K * a ^ 2 +
          ((Fintype.card (ι (j.castAdd 2)) ^ 2 : ℕ) : ℝ) / 2 * Real.log ((m : ℝ) + 1))) := by
  intro m S w F
  have hm := PosSemidef.re_trace_finKronecker_exp_signed_labelEntropy_le
    (posSemidef_physicalSingletonDensity ι Ω j)
      (trace_physicalSingletonDensity ι Ω hΩ j) hmoment m ha har ha1
  constructor
  · rw [trace_replicaGoodConfigurationMarginal_exp_singleton_labelEntropy
      ι Ω hΩ k B u j a]
    simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using
      mul_le_mul_of_nonneg_left hm.1 (sq_nonneg ‖WithLp.toLp 2 w‖)
  · rw [trace_replicaGoodConfigurationMarginal_exp_singleton_labelEntropy
      ι Ω hΩ k B u j (-a)]
    simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using
      mul_le_mul_of_nonneg_left hm.2 (sq_nonneg ‖WithLp.toLp 2 w‖)

end Matrix
