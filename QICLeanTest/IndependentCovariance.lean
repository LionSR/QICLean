/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.IndependentCovariance

/-! Product-measure covariance regressions for empty and rectangular index
families and zero weights. -/

open IndependentCovariance MeasureTheory
open scoped BigOperators

-- Empty slots have scalar covariance one, even with vacuous coefficient data.
example (f g : Fin 0 → Unit → ℂ) :
    (∫ ω, (∏ s, f s (ω s)) * star (∏ s, g s (ω s))
      ∂Measure.pi (fun _ : Fin 0 ↦ Measure.dirac ())) = 1 := by
  rw [integral_product_mul_conj]
  simp

-- Distinct ket and bra dimensions and zero probabilities are permitted.
example (k : ℕ) (i i' : Fin 1 → Fin 2) (l l' : Fin 1 → Fin 3) :
    (∫ ω, tensorCoefficient (fun (_ : Fin 1) (_ : Fin 2) (_ : Fin 3) (_ : Unit) ↦ 0) i l ω *
      star (tensorCoefficient (fun (_ : Fin 1) (_ : Fin 2) (_ : Fin 3) (_ : Unit) ↦ 0) i' l' ω)
      ∂Measure.pi (fun _ : Fin 1 ↦ Measure.dirac ())) = 0 := by
  have h := tensor_covariance_weighted (fun _ : Fin 1 ↦ Measure.dirac ())
    (fun (_ : Fin 1) (_ : Fin 2) (_ : Fin 3) (_ : Unit) ↦ (0 : ℂ)) k
    (fun (_ : Fin 1) (_ : Fin 2) ↦ (0 : ℝ))
    (fun (_ : Fin 1) (_ : Fin 3) ↦ (1 : ℝ))
    (by intros; positivity) (by intros; positivity) (by intros; simp) i i' l l'
  simpa using h

-- The empty tensor probability list is normalized independently of local weights.
example : (∑ _i : Fin 0 → Fin 2, ∏ _s : Fin 0, (0 : ℝ)) = 1 := by
  exact sum_product_weights_eq_one (fun (_ : Fin 0) (_ : Fin 2) ↦ (0 : ℝ))
    (fun s ↦ Fin.elim0 s)
