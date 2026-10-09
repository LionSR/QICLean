/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationIndividualMergeMoment
import QICLean.Analysis.ReplicaGoodConfigurationSignedMoments
import QICLean.Analysis.FiveMomentExponentialBound
import QICLean.Representation.PhysicalMergeHolder

/-!
# Conditional sharp moment of the actual good-copy density

The two actual merge moments and the three signed physical singleton
moments are taken in the same good-copy density. Five-factor trace
Hölder retains its component mass exactly once, including zero mass.
Every entropy and one-copy moment hypothesis belongs to the original
physical state. The geometric bound for those one-copy moments remains
an explicit separate input.

Source: September 24, 2026 area-law manuscript, `07-comparators.tex`,
lines 218–238 and 550–560, `comparator:signed-label-moments` and
`comparator:component-inverse`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix TensorPower PermutationRepresentation
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
variable (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
  ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)

local instance goodSharpMoment_decidableEqConfig :
    DecidableEq (Config Bᶜ.card ι) := Fintype.decidablePiFintype

/-- Five actual component moments yield the sharp good-density bound.
The original simultaneous copy symmetry and original marginal surprisal
bounds are explicit. The component may vanish. No marginal identity or
desired expectation bound is supplied as a premise.
Source: `07-comparators.tex`, lines 218–238 and 550–560. -/
theorem replicaGoodConfigurationMarginal_exp_merge_sub_physical_sharp_le
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
        (permOp (copyPerm (ι 3) k) σ ⊗ₖ permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u)
    {K r : ℝ}
    (hmoment : ∀ j : Fin 3, ∀ v : ℝ, |v| ≤ r →
      Real.log (Entropy.surprisalMoment
        (posSemidef_physicalSingletonDensity ι Ω j).isHermitian.eigenvalues v) ≤
      v * vonNeumannEntropy (physicalSingletonDensity ι Ω j)
        (posSemidef_physicalSingletonDensity ι Ω j).isHermitian + K * v ^ 2)
    {a : ℝ} (ha : 0 ≤ a) (har : 10 * a ≤ r) (ha1 : 10 * a ≤ 1) :
    let m := Bᶜ.card
    let F := fun S ↦ labelEntropy (subsystemPerm m ι S)
    let S := fun j ↦ vonNeumannEntropy (physicalSingletonDensity ι Ω j)
      (posSemidef_physicalSingletonDensity ι Ω j).isHermitian
    let d := fun j : Fin 5 ↦ Fintype.card (ι j)
    let Λ := ((((d 0 * d 3) ^ 2 : ℕ) : ℝ) + (((d 2 * d 4) ^ 2 : ℕ) : ℝ) +
      ((d 0 ^ 2 : ℕ) : ℝ) / 2 + ((d 2 ^ 2 : ℕ) : ℝ) / 2) / 5
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (replicaGoodConfigurationMarginal ι Ω k B u * NormedSpace.exp ((a : ℂ) •
      ((F {0} + F {3} - F {0, 3}) + (F {2} + F {4} - F {2, 4}) -
        physicalMergeDeficit ι m))).trace.re ≤
      ‖WithLp.toLp 2 w‖ ^ 2 * Real.exp
        (-(m : ℝ) * a * (S 0 + S 2 - S 1) + 25 * (m : ℝ) * K * a ^ 2 +
          Λ * Real.log ((m : ℝ) + 1)) := by
  classical
  intro m F S d Λ w
  let ρ := replicaGoodConfigurationMarginal ι Ω k B u
  let DC := F {0} + F {3} - F {0, 3}
  let DR := F {2} + F {4} - F {2, 4}
  let b := 5 * a
  let mass := ‖WithLp.toLp 2 w‖ ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbr : 2 * b ≤ r := by dsimp [b]; linarith
  have hb1 : 2 * b ≤ 1 := by dsimp [b]; linarith
  have hm := replicaGoodConfigurationMarginal_exp_mergeDeficits_le
    ι Ω k B u hΩ hu b (by linarith)
  have hQ := replicaGoodConfigurationMarginal_exp_signed_singleton_le
    ι Ω k B u hΩ 0 (hmoment 0) hb hbr hb1
  have hV := replicaGoodConfigurationMarginal_exp_signed_singleton_le
    ι Ω k B u hΩ 2 (hmoment 2) hb hbr hb1
  have hY := replicaGoodConfigurationMarginal_exp_signed_singleton_le
    ι Ω k B u hΩ 1 (hmoment 1) hb hbr hb1
  let M : Fin 5 → ℝ := ![
    (ρ * NormedSpace.exp ((b : ℂ) • DC)).trace.re,
    (ρ * NormedSpace.exp ((b : ℂ) • DR)).trace.re,
    (ρ * NormedSpace.exp (((-b : ℝ) : ℂ) • F {0})).trace.re,
    (ρ * NormedSpace.exp (((-b : ℝ) : ℂ) • F {2})).trace.re,
    (ρ * NormedSpace.exp ((b : ℂ) • F {1})).trace.re]
  let A : Fin 5 → ℝ := ![
    (((d 0 * d 3) ^ 2 : ℕ) : ℝ) * Real.log ((m : ℝ) + 1),
    (((d 2 * d 4) ^ 2 : ℕ) : ℝ) * Real.log ((m : ℝ) + 1),
    (-b) * ((m : ℝ) * S 0) + (2 * (m : ℝ) * K * b ^ 2 +
      ((d 0 ^ 2 : ℕ) : ℝ) / 2 * Real.log ((m : ℝ) + 1)),
    (-b) * ((m : ℝ) * S 2) + (2 * (m : ℝ) * K * b ^ 2 +
      ((d 2 ^ 2 : ℕ) : ℝ) / 2 * Real.log ((m : ℝ) + 1)),
    b * ((m : ℝ) * S 1) + (m : ℝ) * K * b ^ 2]
  have hpoly (n : ℕ) : (((m + 1) ^ n : ℕ) : ℝ) =
      Real.exp ((n : ℝ) * Real.log ((m : ℝ) + 1)) := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, ← Real.rpow_natCast,
      Real.rpow_def_of_pos (by positivity : 0 < (m : ℝ) + 1)]
    congr 1
    ring
  have hbound (i : Fin 5) : M i ≤ mass * Real.exp (A i) := by
    fin_cases i
    · simpa only [M, A, Matrix.cons_val_zero, hpoly, mul_comm] using hm.1
    · simpa only [M, A, Matrix.cons_val_succ, Matrix.cons_val_zero,
        hpoly, mul_comm] using hm.2
    · exact hQ.2
    · exact hV.2
    · exact hY.1
  have hρ : ρ.PosSemidef := posSemidef_replicaGoodConfigurationMarginal ι Ω k B u
  have hF (T : Finset (Fin 5)) : (F T).IsHermitian := isHermitian_labelObservable _ _
  have hn (H : Matrix (Config m ι) (Config m ι) ℂ) (hH : H.IsHermitian) (v : ℝ) :
      0 ≤ (ρ * NormedSpace.exp ((v : ℂ) • H)).trace.re :=
    hρ.re_trace_mul_exp_nonneg (hH.smul (show IsSelfAdjoint (v : ℂ) by
      simp [isSelfAdjoint_iff]))
  have hM (i : Fin 5) : 0 ≤ M i := by
    fin_cases i
    · exact hn DC (((hF {0}).add (hF {3})).sub (hF {0, 3})) b
    · exact hn DR (((hF {2}).add (hF {4})).sub (hF {2, 4})) b
    · exact hn (F {0}) (hF {0}) (-b)
    · exact hn (F {2}) (hF {2}) (-b)
    · exact hn (F {1}) (hF {1}) b
  have hholder := re_trace_mul_exp_mergeDeficits_sub_physicalMergeDeficit_le ι m hρ a
  have hprod := Real.prod_five_rpow_le_common_exp M A (sq_nonneg ‖WithLp.toLp 2 w‖) hM hbound
  have hfirst : (ρ * NormedSpace.exp ((a : ℂ) •
      (DC + DR - physicalMergeDeficit ι m))).trace.re ≤
        ∏ i, M i ^ (1 / 5 : ℝ) := by
    simpa [M, b, DC, DR, Fin.prod_univ_succ, neg_mul, mul_assoc] using hholder
  calc
    _ ≤ mass * Real.exp ((∑ i, A i) / 5) := hfirst.trans hprod
    _ = _ := by
      congr 1
      congr 1
      simp only [A, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.sum_univ_zero, add_zero, b, Λ]
      ring

end Matrix
