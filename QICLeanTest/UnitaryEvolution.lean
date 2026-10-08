/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.UnitaryEvolution
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Consumers of the unitary-evolution laws, using explicit solutions. -/

open scoped Matrix Matrix.Norms.L2Operator
open NormedSpace MatrixEvolution

namespace UnitaryEvolutionTest

variable {n : Type*} [Fintype n] [DecidableEq n]

-- The zero generator yields the constant identity path, whose unitarity follows
-- from its derivative and initial value.
example (t : ℝ) : (1 : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ := by
  apply mem_unitaryGroup_of_hasDerivAt
    (G := fun _ => 0) (U := fun _ => 1) (fun _ => Matrix.isHermitian_zero) rfl
    (fun s => ?_) t
  simpa using hasDerivAt_const s (1 : Matrix n n ℂ)

private noncomputable def sinusoidalFlow (K : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  exp (Real.sin t • (Complex.I • K))

private theorem sinusoidalFlow_deriv (K : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (sinusoidalFlow K)
      ((Complex.I • (Real.cos t • K)) * sinusoidalFlow K t) t := by
  convert! (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Complex.I • K)
    (Real.sin t)).scomp t (Real.hasDerivAt_sin t) using 1
  simp only [sinusoidalFlow, smul_mul_assoc,
    smul_comm (Real.cos t) Complex.I (K * exp (Real.sin t • (Complex.I • K)))]

-- A genuinely time-dependent scalar coefficient, with the evolution supplied
-- explicitly and its unitary law obtained only from the ODE theorem.
example (K : Matrix n n ℂ) (hK : K.IsHermitian) (t : ℝ) :
    sinusoidalFlow K t ∈ Matrix.unitaryGroup n ℂ := by
  apply mem_unitaryGroup_of_hasDerivAt
    (G := fun s => Real.cos s • K)
    (fun s => hK.smul (IsSelfAdjoint.all (Real.cos s)))
    (by simp [sinusoidalFlow]) (sinusoidalFlow_deriv K) t

-- The comparison estimate is applied at a concrete negative time. Its second
-- solution is the constant identity, and no unitary hypothesis is supplied.
example (K : Matrix n n ℂ) (hK : K.IsHermitian) :
    ‖sinusoidalFlow K (-2) - 1‖ ≤ ‖K‖ * 2 := by
  have hbound (s : ℝ) : ‖Real.cos s • K - (0 : Matrix n n ℂ)‖ ≤ ‖K‖ := by
    calc
      ‖Real.cos s • K - (0 : Matrix n n ℂ)‖ = |Real.cos s| * ‖K‖ := by
        simp only [sub_zero, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖K‖ := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one s) (norm_nonneg K)
      _ = ‖K‖ := one_mul _
  have h := norm_sub_le_of_generator_bound
    (G := fun s => Real.cos s • K) (H := fun _ => 0)
    (U := sinusoidalFlow K) (V := fun _ => 1)
    (Real.continuous_cos.smul continuous_const) continuous_const
    (fun s => hK.smul (IsSelfAdjoint.all (Real.cos s))) (fun _ => Matrix.isHermitian_zero)
    (by simp [sinusoidalFlow]) rfl (sinusoidalFlow_deriv K)
    (fun s => by simpa using hasDerivAt_const s (1 : Matrix n n ℂ))
    (-2) ‖K‖ (fun s _ => hbound s)
  simpa using h

-- The exact same API remains available on the zero-dimensional Hilbert space.
example (t : ℝ) : (1 : Matrix (Fin 0) (Fin 0) ℂ) ∈ Matrix.unitaryGroup (Fin 0) ℂ := by
  apply mem_unitaryGroup_of_hasDerivAt
    (G := fun _ => 0) (U := fun _ => 1) (fun _ => Matrix.isHermitian_zero) rfl
    (fun s => ?_) t
  simpa using hasDerivAt_const s (1 : Matrix (Fin 0) (Fin 0) ℂ)

-- The norm comparison, not just unitarity, supports empty index types.
example (t : ℝ) : ‖(1 : Matrix (Fin 0) (Fin 0) ℂ) - 1‖ ≤ (0 : ℝ) * |t| := by
  apply norm_sub_le_of_generator_bound
    (G := fun _ => 0) (H := fun _ => 0) (U := fun _ => 1) (V := fun _ => 1)
    continuous_const continuous_const
    (fun _ => Matrix.isHermitian_zero) (fun _ => Matrix.isHermitian_zero) rfl rfl
    (fun s => by simpa using hasDerivAt_const s (1 : Matrix (Fin 0) (Fin 0) ℂ))
    (fun s => by simpa using hasDerivAt_const s (1 : Matrix (Fin 0) (Fin 0) ℂ)) t 0
  intro s hs
  simp

end UnitaryEvolutionTest
