/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.ComplexGaussian.GlobalBranchLaw

/-! Boundary regressions for selected branches under one global Gaussian law. -/

open QICLean.ComplexGaussian MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator
attribute [local instance 10000] Classical.propDecidable

noncomputable section

abbrev Branches (p : Fin 2) := Fin (if p = 0 then 2 else 3)
abbrev Ket (_p : Fin 2) (_b : Branches _p) := Fin 2
abbrev Bra (_p : Fin 2) (_b : Branches _p) := Fin 3
abbrev Selected : Finset (Fin 2) := {0}

def selector (p : Selected) : Branches p := ⟨1, by split_ifs <;> norm_num⟩

local instance (S : Finset (Fin 2)) : DecidableEq S := Classical.decEq _

-- Five labelled Gaussian blocks, but one corrected position and inverse sample exponent one.
example (k : ℕ) (hk : 0 < k) :
    (∫ ω, selectedBranchDensityCoefficient k Selected selector
      (fun _ a ↦ if a = 0 then (1 : ℝ) else 0)
      (fun _ c ↦ if c = 0 then (1 : ℝ) else 0) (fun _ ↦ (0, 0)) (fun _ ↦ (0, 0)) ω *
      star (selectedBranchDensityCoefficient k Selected selector
        (fun _ a ↦ if a = 0 then (1 : ℝ) else 0)
        (fun _ c ↦ if c = 0 then (1 : ℝ) else 0) (fun _ ↦ (0, 0)) (fun _ ↦ (0, 0)) ω)
      ∂globalBranchLaw k Ket Bra) = ((k : ℝ)⁻¹ : ℂ) := by
  have h := integral_selectedBranchDensityCoefficient_mul_conj (A := Ket) (C := Bra)
    k hk Selected selector
    (fun _ a ↦ if a = 0 then (1 : ℝ) else 0)
    (fun _ c ↦ if c = 0 then (1 : ℝ) else 0)
    (by intros; split_ifs <;> norm_num) (by intros; split_ifs <;> norm_num)
    (fun _ ↦ (0, 0)) (fun _ ↦ (0, 0)) (fun _ ↦ (0, 0)) (fun _ ↦ (0, 0))
  simpa [Selected, pairedProductProbability, Real.rpow_neg (Nat.cast_nonneg k)] using h

-- Zero Schmidt weights give zero variance on the same nonempty global law.
example (k : ℕ) (hk : 0 < k) :
    (∫ ω, selectedBranchDensityCoefficient k Selected selector
      (fun _ a ↦ if a = 0 then (1 : ℝ) else 0)
      (fun _ c ↦ if c = 0 then (1 : ℝ) else 0) (fun _ ↦ (1, 0)) (fun _ ↦ (0, 0)) ω *
      star (selectedBranchDensityCoefficient k Selected selector
        (fun _ a ↦ if a = 0 then (1 : ℝ) else 0)
        (fun _ c ↦ if c = 0 then (1 : ℝ) else 0) (fun _ ↦ (1, 0)) (fun _ ↦ (0, 0)) ω)
      ∂globalBranchLaw k Ket Bra) = 0 := by
  have h := integral_selectedBranchDensityCoefficient_mul_conj (A := Ket) (C := Bra)
    k hk Selected selector
    (fun _ a ↦ if a = 0 then (1 : ℝ) else 0)
    (fun _ c ↦ if c = 0 then (1 : ℝ) else 0)
    (by intros; split_ifs <;> norm_num) (by intros; split_ifs <;> norm_num)
    (fun _ ↦ (1, 0)) (fun _ ↦ (1, 0)) (fun _ ↦ (0, 0)) (fun _ ↦ (0, 0))
  simpa [Selected, pairedProductProbability] using h

-- Global projection uses the chosen complex phase; the real coordinate is in another branch.
def phaseSamples : (p : Fin 2) → (b : Branches p) → Sample (Fin 1 × (Ket p b × Bra p b)) :=
  fun _ b ↦ WithLp.toLp 2 (fun q ↦ if b.val = 1 then
    (if q.2 = 1 then Real.sqrt 2 else 0) else (if q.2 = 0 then Real.sqrt 2 else 0))

example : coordinate (0, (0, 0))
    (selectedBranchSamples (A := Ket) (C := Bra) 1 Selected selector phaseSamples
      ⟨0, by simp [Selected]⟩) = Complex.I := by
  rw [coordinate_apply]
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp [selectedBranchSamples, selector, phaseSamples, hs]

example : coordinate (0, (0, 0)) (phaseSamples 0 ⟨0, by norm_num⟩) = 1 := by
  rw [coordinate_apply]
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp [phaseSamples, hs]

-- Empty selections still share the nontrivial global law; their coefficient and covariance are one.
def emptySelector (p : (∅ : Finset (Fin 2))) : Branches p :=
  False.elim (Finset.notMem_empty p.val p.property)

example (k : ℕ) (hk : 0 < k) :
    (∫ ω, selectedBranchDensityCoefficient k ∅ emptySelector
      (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ (0 : ℝ)) (fun _ ↦ (0, 0)) (fun _ ↦ (0, 0)) ω *
      star (selectedBranchDensityCoefficient k ∅ emptySelector
        (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ (0 : ℝ)) (fun _ ↦ (0, 0)) (fun _ ↦ (0, 0)) ω)
      ∂globalBranchLaw k Ket Bra) = 1 := by
  have h := integral_selectedBranchDensityCoefficient_mul_conj (A := Ket) (C := Bra)
    k hk ∅ emptySelector
    (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ (0 : ℝ)) (by intros; positivity) (by intros; positivity)
    (fun _ ↦ (0, 0)) (fun _ ↦ (0, 0)) (fun _ ↦ (0, 0)) (fun _ ↦ (0, 0))
  simpa [pairedProductProbability] using h

-- Empty corrected positions give the empty expansion term's bound one on this same law.
example (k : ℕ) (hk : 0 < k)
    (O : Matrix
      (((p : (∅ : Finset (Fin 2))) → Bra p (emptySelector p) × Bra p (emptySelector p)) × Fin 1)
      (((p : (∅ : Finset (Fin 2))) → Ket p (emptySelector p) × Ket p (emptySelector p)) × Fin 1) ℂ)
    (hO : ‖O‖ ≤ 1) :
    (∫ ω, Matrix.rectangularTraceNorm (ProbabilityTheory.weightedSourceError
      (fun _ : Fin 1 ↦ (1 : ℝ)) (fun _ : Fin 1 ↦ (1 : ℝ)) O
      (fun b ↦ selectedBranchDensityCoefficient k ∅ emptySelector
        (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ (0 : ℝ)) b.1 b.2 ω)) ∂globalBranchLaw k Ket Bra) ≤ 1 := by
  have h := integral_rectangularTraceNorm_selectedBranchSourceError_le (A := Ket) (C := Bra)
    k hk ∅ emptySelector
    (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ (0 : ℝ))
    (by intros; positivity) (by intros; positivity)
    (fun p ↦ False.elim (Finset.notMem_empty p.val p.property))
    (fun p ↦ False.elim (Finset.notMem_empty p.val p.property))
    (fun _ : Fin 1 ↦ (1 : ℝ)) (fun _ : Fin 1 ↦ (1 : ℝ)) O
    (by intros; positivity) (by intros; positivity) (by simp) (by simp) hO
  simpa using h

-- One corrected position with rectangular private spaces, zeros and a full-input contraction.
example (k : ℕ) (hk : 0 < k)
    (O : Matrix (((p : Selected) → Bra p (selector p) × Bra p (selector p)) × Fin 3)
      (((p : Selected) → Ket p (selector p) × Ket p (selector p)) × Fin 2) ℂ)
    (hO : ‖O‖ ≤ 1) :
    (∫ ω, Matrix.rectangularTraceNorm (ProbabilityTheory.weightedSourceError
      (fun t : Fin 2 ↦ if t = 0 then (1 : ℝ) else 0)
      (fun u : Fin 3 ↦ if u = 0 then (1 : ℝ) else 0) O
      (fun b ↦ selectedBranchDensityCoefficient k Selected selector
        (fun _ a ↦ if a = 0 then (1 : ℝ) else 0)
        (fun _ c ↦ if c = 0 then (1 : ℝ) else 0) b.1 b.2 ω)) ∂globalBranchLaw k Ket Bra) ≤
      (k : ℝ) ^ (-(1 : ℝ) / 2) := by
  have h := integral_rectangularTraceNorm_selectedBranchSourceError_le (A := Ket) (C := Bra)
    k hk Selected selector
    (fun _ a ↦ if a = 0 then (1 : ℝ) else 0)
    (fun _ c ↦ if c = 0 then (1 : ℝ) else 0)
    (by intros; split_ifs <;> norm_num) (by intros; split_ifs <;> norm_num)
    (by intro p; norm_num [Fin.sum_univ_succ])
    (by intro p; norm_num [Fin.sum_univ_succ])
    (fun t : Fin 2 ↦ if t = 0 then (1 : ℝ) else 0)
    (fun u : Fin 3 ↦ if u = 0 then (1 : ℝ) else 0) O
    (by intros; split_ifs <;> norm_num) (by intros; split_ifs <;> norm_num)
    (by norm_num [Fin.sum_univ_succ]) (by norm_num [Fin.sum_univ_succ]) hO
  simpa [Selected] using h
