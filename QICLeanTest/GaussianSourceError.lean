/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.ComplexGaussian.SourceError

/-! Edge-case regressions for GaussianSourceError in the compression proof. -/

open QICLean.ComplexGaussian MeasureTheory

attribute [local instance 10000] Classical.propDecidable
open scoped BigOperators Matrix Matrix.Norms.L2Operator

abbrev SingleIndex := Fin 1 → Fin 1 × Fin 1

-- A nonzero complex-phase contraction, one actual Gaussian slot, no moment hypotheses.
example (k : ℕ) (hk : 0 < k)
    (hO : ‖Complex.I • (1 : Matrix (SingleIndex × Fin 1) (SingleIndex × Fin 1) ℂ)‖ ≤ 1) :
    (∫ ω, Matrix.rectangularTraceNorm
      (ProbabilityTheory.weightedSourceError (fun _ : Fin 1 ↦ (1 : ℝ))
        (fun _ : Fin 1 ↦ (1 : ℝ))
        (Complex.I • (1 : Matrix (SingleIndex × Fin 1) (SingleIndex × Fin 1) ℂ))
        (fun b ↦ independentDensityCoefficient k (fun (_ : Fin 1) (_ : Fin 1) ↦ (1 : ℝ))
          (fun _ _ ↦ (1 : ℝ)) b.1 b.2 ω))
      ∂independentDensityLaw k (fun _ : Fin 1 ↦ Fin 1) (fun _ ↦ Fin 1)) ≤
      (k : ℝ) ^ (-(1 : ℝ) / 2) := by
  have h := integral_rectangularTraceNorm_gaussianSourceError_le k hk
    (fun (_ : Fin 1) (_ : Fin 1) ↦ (1 : ℝ))
    (fun (_ : Fin 1) (_ : Fin 1) ↦ (1 : ℝ))
    (by intros; positivity) (by intros; positivity)
    (by intro s; simp) (by intro s; simp)
    (fun _ : Fin 1 ↦ (1 : ℝ)) (fun _ : Fin 1 ↦ (1 : ℝ))
    (Complex.I • (1 : Matrix (SingleIndex × Fin 1) (SingleIndex × Fin 1) ℂ))
    (by intros; positivity) (by intros; positivity) (by simp) (by simp) hO
  simpa only [Fintype.card_fin, Nat.cast_one] using h

-- Empty slots give the empty expansion term, with bound one (not zero correction).
example (k : ℕ) (hk : 0 < k)
    (O : Matrix (((Fin 0 → Fin 3 × Fin 3) × Fin 1))
      (((Fin 0 → Fin 2 × Fin 2) × Fin 1)) ℂ) (hO : ‖O‖ ≤ 1) :
    (∫ ω, Matrix.rectangularTraceNorm
      (ProbabilityTheory.weightedSourceError (fun _ : Fin 1 ↦ (1 : ℝ))
        (fun _ : Fin 1 ↦ (1 : ℝ)) O
        (fun b ↦ independentDensityCoefficient k
          (fun (_ : Fin 0) (_ : Fin 2) ↦ (0 : ℝ))
          (fun (_ : Fin 0) (_ : Fin 3) ↦ (0 : ℝ)) b.1 b.2 ω))
      ∂independentDensityLaw k (fun _ : Fin 0 ↦ Fin 2) (fun _ ↦ Fin 3)) ≤ 1 := by
  have h := integral_rectangularTraceNorm_gaussianSourceError_le k hk
    (fun (_ : Fin 0) (_ : Fin 2) ↦ (0 : ℝ))
    (fun (_ : Fin 0) (_ : Fin 3) ↦ (0 : ℝ))
    (by intros; positivity) (by intros; positivity)
    (fun s ↦ Fin.elim0 s) (fun s ↦ Fin.elim0 s)
    (fun _ : Fin 1 ↦ (1 : ℝ)) (fun _ : Fin 1 ↦ (1 : ℝ)) O
    (by intros; positivity) (by intros; positivity) (by simp) (by simp) hO
  simpa using h

-- Rectangular private spaces and ket/bra Schmidt supports include zero probabilities.
example (k : ℕ) :
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm
      (ProbabilityTheory.weightedSourceError
        (fun t : Fin 2 ↦ if t = 0 then (1 : ℝ) else 0)
        (fun u : Fin 3 ↦ if u = 0 then (1 : ℝ) else 0)
        (0 : Matrix (((Fin 1 → Fin 3 × Fin 3) × Fin 3))
          (((Fin 1 → Fin 2 × Fin 2) × Fin 2)) ℂ)
        (fun b ↦ independentDensityCoefficient k
          (fun (_ : Fin 1) (a : Fin 2) ↦ if a = 0 then (1 : ℝ) else 0)
          (fun (_ : Fin 1) (c : Fin 3) ↦ if c = 0 then (1 : ℝ) else 0) b.1 b.2 ω)))
      (independentDensityLaw k (fun _ : Fin 1 ↦ Fin 2) (fun _ ↦ Fin 3)) := by
  apply integrable_rectangularTraceNorm_gaussianSourceError
  · intro t; split_ifs <;> norm_num
  · intro u; split_ifs <;> norm_num
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]
