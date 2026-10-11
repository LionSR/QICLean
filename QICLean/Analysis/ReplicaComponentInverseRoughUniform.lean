/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaComponentInverseRough
import QICLean.Analysis.ReplicaComponentUniformRate

/-!
# A rough component rate uniform over the excitation subset

The arithmetic mean of the two merge-moment polynomial losses is bounded
by their larger degree. The summed original auxiliary label bound and
the upper bound on the number of bad copies then give one uniform rough
rate. All three binomial corrections are retained.

The original vector, auxiliary labels and actual excitation component
are unchanged. No one-copy moment hypothesis is required. The fixed
polynomial constant precedes the copy number, state, labels, vector and
cutoff parameters.

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

local instance replicaComponentInverseRoughUniform_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The rough inverse estimate is uniform over all actual excitation
subsets of size at most the prescribed fraction. The original symmetry
and two label equations are retained. The only scalar label assumption
is the summed lower bound for their original logarithmic dimensions;
there is no marginal moment hypothesis.
Source: `07-comparators.tex`, lines 550--590. -/
theorem exists_replicaExcitationComponent_inverse_rough_uniform_le
    {t : ℝ} (ht : 0 < t) (htsmall : 4 * t ≤ 1) :
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
      ∀ (τ S ε : ℝ), 0 ≤ τ → τ ≤ 1 / 2 → (B.card : ℝ) ≤ τ * k →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let w := (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
          ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
      let f := w ∘ fiveFactorCopiesEquiv ι k
      let W := replicaMetric ι t k
      let d := Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))
      let D := max ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2)
        ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2)
      (star f ⬝ᵥ ((((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)⁻¹ *ᵥ f)).re ≤
        (((k : ℝ) + 2) ^ (C + (D : ℝ)) * Real.exp
          (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) +
            (2 * t) * ε)) * ‖WithLp.toLp 2 w‖ ^ 2 := by
  obtain ⟨C, hC, hrough⟩ :=
    exists_replicaExcitationComponent_inverse_rough_le ι ht htsmall
  refine ⟨C, hC, ?_⟩
  intro k B Ω hΩ ellC ellR u hu huC huR τ S ε hτ hτhalf hB hlabel w f W d D
  let m := Bᶜ.card
  let nQ := (Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2
  let nV := (Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2
  let q := ((((m + 1) ^ nQ : ℕ) : ℝ) + (((m + 1) ^ nV : ℕ) : ℝ)) / 2
  let b := Real.log ellC.dim + Real.log ellR.dim - (B.card : ℝ) * d -
    2 * Real.log (k.choose B.card)
  let p := ((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ (2 * t) *
    Real.exp (-(2 * t) * b)
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hpoly : q ≤ Real.exp ((D : ℝ) * Real.log ((m : ℝ) + 1)) := by
    have hQ : ((m : ℝ) + 1) ^ nQ ≤ ((m : ℝ) + 1) ^ D :=
      pow_le_pow_right₀ (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
        (le_max_left nQ nV)
    have hV : ((m : ℝ) + 1) ^ nV ≤ ((m : ℝ) + 1) ^ D :=
      pow_le_pow_right₀ (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
        (le_max_right nQ nV)
    have hexp : ((m : ℝ) + 1) ^ D =
        Real.exp ((D : ℝ) * Real.log ((m : ℝ) + 1)) := by
      rw [← Real.rpow_natCast,
        Real.rpow_def_of_pos (by positivity : 0 < (m : ℝ) + 1)]
      congr 1
      ring
    rw [← hexp]
    dsimp only [q]
    push_cast
    linarith only [hQ, hV]
  have hdim (j : Fin 5) : 0 ≤ Real.log (Fintype.card (ι j)) :=
    Real.log_natCast_nonneg _
  have hd : 0 ≤ d := add_nonneg (hdim 3) (hdim 4)
  have hBk : B.card ≤ k := by
    simpa only [Fintype.card_fin] using B.card_le_univ
  have hm : m = k - B.card := by
    dsimp only [m]
    simp only [Finset.card_compl, Fintype.card_fin]
  have hfactor := Real.replica_component_prefactor_le_uniform
    (g := 0) (K := 0) (Λ := (D : ℝ)) hBk hτ hτhalf hB
    (show 0 ≤ 2 * t by positivity) hd le_rfl le_rfl (Nat.cast_nonneg D)
    C S ε (Real.log ellC.dim + Real.log ellR.dim) hlabel
  have hunif : p * Real.exp ((D : ℝ) * Real.log ((m : ℝ) + 1)) ≤
      ((k : ℝ) + 2) ^ (C + (D : ℝ)) * Real.exp
        (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) +
          (2 * t) * ε) := by
    simpa only [← hm, mul_zero, zero_mul, zero_add, add_zero] using hfactor
  have h := hrough k B Ω hΩ ellC ellR u hu huC huR
  change (star f ⬝ᵥ ((((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)⁻¹ *ᵥ f)).re ≤
    (p * q) * ‖WithLp.toLp 2 w‖ ^ 2 at h
  exact h.trans (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left hpoly hp).trans hunif) (sq_nonneg ‖WithLp.toLp 2 w‖))

end Matrix
