/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.ComplexGaussian.IndependentSlots

/-! Actual independent Gaussian slot regressions for empty correction sets,
zero Schmidt weights and heterogeneous ket and bra supports. -/

open QICLean.ComplexGaussian MeasureTheory
open scoped BigOperators

-- Empty slots give scalar covariance one on the actual constructed law.
example (k : ℕ) (hk : 0 < k) (i i' : Fin 0 → Fin 2 × Fin 2)
    (l l' : Fin 0 → Fin 3 × Fin 3) :
    (∫ ω, independentDensityCoefficient k (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ (0 : ℝ)) i l ω *
      star (independentDensityCoefficient k (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ (0 : ℝ)) i' l' ω)
      ∂independentDensityLaw k (fun _ : Fin 0 ↦ Fin 2) (fun _ ↦ Fin 3)) = 1 := by
  have h := integral_independentDensityCoefficient_mul_conj k hk
    (fun (_ : Fin 0) (_ : Fin 2) ↦ (0 : ℝ))
    (fun (_ : Fin 0) (_ : Fin 3) ↦ (0 : ℝ))
    (by intros; positivity) (by intros; positivity) i i' l l'
  have hi : i = i' := funext (fun s ↦ Fin.elim0 s)
  have hl : l = l' := funext (fun s ↦ Fin.elim0 s)
  simpa [pairedProductProbability, hi, hl] using h

-- One corrected slot with zero Schmidt weights has zero actual covariance.
example (k : ℕ) (hk : 0 < k) (i i' : Fin 1 → Fin 2 × Fin 2)
    (l l' : Fin 1 → Fin 3 × Fin 3) :
    (∫ ω, independentDensityCoefficient k (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ (1 : ℝ)) i l ω *
      star (independentDensityCoefficient k (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ (1 : ℝ)) i' l' ω)
      ∂independentDensityLaw k (fun _ : Fin 1 ↦ Fin 2) (fun _ ↦ Fin 3)) = 0 := by
  have h := integral_independentDensityCoefficient_mul_conj k hk
    (fun (_ : Fin 1) (_ : Fin 2) ↦ (0 : ℝ))
    (fun (_ : Fin 1) (_ : Fin 3) ↦ (1 : ℝ))
    (by intros; positivity) (by intros; positivity) i i' l l'
  simpa [pairedProductProbability] using h

-- The two slots have respectively ket dimensions 2,3 and bra dimensions 5,4.
-- Actual pair integrability needs no common support dimensions or weight positivity.
example (k : ℕ)
    (i i' : (s : Fin 2) → Fin (s.val + 2) × Fin (s.val + 2))
    (l l' : (s : Fin 2) → Fin (5 - s.val) × Fin (5 - s.val)) :
    Integrable (fun ω ↦ independentDensityCoefficient k (fun _ _ ↦ (-1 : ℝ))
      (fun _ _ ↦ (0 : ℝ)) i l ω * star (independentDensityCoefficient k
        (fun _ _ ↦ (-1 : ℝ)) (fun _ _ ↦ (0 : ℝ)) i' l' ω))
      (independentDensityLaw k (fun s : Fin 2 ↦ Fin (s.val + 2))
        (fun s ↦ Fin (5 - s.val))) :=
  integrable_independentDensityCoefficient_mul_conj k _ _ i i' l l'
