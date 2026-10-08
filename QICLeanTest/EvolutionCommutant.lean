/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.UnitaryEvolution
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Consumers of conservation and commutation for matrix evolutions. -/

open scoped Matrix Matrix.Norms.L2Operator NNReal
open NormedSpace MatrixEvolution

namespace EvolutionCommutantTest

variable {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable def sinusoidalFlow (K : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  exp (Real.sin t • (Complex.I • K))

private theorem sinusoidalFlow_deriv (K : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (sinusoidalFlow K)
      ((Complex.I • (Real.cos t • K)) * sinusoidalFlow K t) t := by
  convert! (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Complex.I • K)
    (Real.sin t)).scomp t (Real.hasDerivAt_sin t) using 1
  simp only [sinusoidalFlow, smul_mul_assoc,
    smul_comm (Real.cos t) Complex.I (K * exp (Real.sin t • (Complex.I • K)))]

-- At the initial time, arbitrary noncommuting matrices retain the full
-- commutator. This fixes the sign before conservation makes it vanish.
example (K C : Matrix n n ℂ) (hK : K.IsHermitian) :
    HasDerivAt (fun s => star (sinusoidalFlow K s) * C * sinusoidalFlow K s)
      (Complex.I • (C * K - K * C)) 0 := by
  simpa [sinusoidalFlow] using hasDerivAt_star_mul_const_mul C
    (G := fun s => Real.cos s • K)
    (fun s => hK.smul (IsSelfAdjoint.all (Real.cos s))) (sinusoidalFlow_deriv K) 0

-- The fixed matrix has no Hermiticity or unitarity hypothesis. The generator
-- varies with time, and conservation is tested at a concrete negative time.
example (K C : Matrix n n ℂ) (hK : K.IsHermitian) (hC : Commute C K) :
    star (sinusoidalFlow K (-2)) * C * sinusoidalFlow K (-2) = C := by
  exact star_mul_const_mul_eq_of_commute C
    (G := fun s => Real.cos s • K)
    (fun s => hK.smul (IsSelfAdjoint.all (Real.cos s)))
    (by simp [sinusoidalFlow]) (sinusoidalFlow_deriv K)
    (fun s => hC.smul_right (Real.cos s)) (-2)

-- Commutation with an actual solution is deduced from its differential
-- equation, with no supplied conservation or unitary conclusion.
example (K C : Matrix n n ℂ) (hK : K.IsHermitian) (hC : Commute C K) (t : ℝ) :
    Commute C (sinusoidalFlow K t) := by
  exact commute_of_commute_generator C
    (G := fun s => Real.cos s • K)
    (fun s => hK.smul (IsSelfAdjoint.all (Real.cos s)))
    (by simp [sinusoidalFlow]) (sinusoidalFlow_deriv K)
    (fun s => hC.smul_right (Real.cos s)) t

-- In particular the fixed matrix can be a nonzero nilpotent matrix, which
-- is neither Hermitian nor unitary.
example : Commute (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)
    (sinusoidalFlow 1 (-2)) := by
  apply commute_of_commute_generator
    (G := fun s => Real.cos s • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    _ (fun s => Matrix.isHermitian_one.smul (IsSelfAdjoint.all (Real.cos s)))
    (by simp [sinusoidalFlow]) (sinusoidalFlow_deriv 1) (fun s => ?_) (-2)
  exact (Commute.one_right _).smul_right (Real.cos s)

-- Conservation and commutation apply to the solution constructed by the
-- global existence theorem; there is no assumed solution in the input.
example (G : ℝ → Matrix n n ℂ) (hGc : ContDiff ℝ 1 G)
    (hG : ∀ t, (G t).IsHermitian) (M : ℝ≥0) (hbound : ∀ t, ‖G t‖ ≤ M)
    (C : Matrix n n ℂ) (hC : ∀ t, Commute C (G t)) :
    ∃ U : ℝ → Matrix n n ℂ, U 0 = 1 ∧
      (∀ t, HasDerivAt U ((Complex.I • G t) * U t) t) ∧
      (∀ t, star (U t) * C * U t = C) ∧ (∀ t, Commute C (U t)) := by
  obtain ⟨U, hU0, hU, _, _⟩ := exists_unique_unitary_solution G hGc hG M hbound
  exact ⟨U, hU0, hU, star_mul_const_mul_eq_of_commute C hG hU0 hU hC,
    commute_of_commute_generator C hG hU0 hU hC⟩

-- Both conclusions retain their full statements for an empty matrix index
-- type and every signed time.
example (C : Matrix (Fin 0) (Fin 0) ℂ) (t : ℝ) :
    star (1 : Matrix (Fin 0) (Fin 0) ℂ) * C * 1 = C ∧ Commute C 1 := by
  have hG : ∀ s : ℝ, (0 : Matrix (Fin 0) (Fin 0) ℂ).IsHermitian :=
    fun _ => Matrix.isHermitian_zero
  have hU : ∀ s : ℝ, HasDerivAt (fun _ : ℝ => (1 : Matrix (Fin 0) (Fin 0) ℂ))
      ((Complex.I • (0 : Matrix (Fin 0) (Fin 0) ℂ)) * 1) s :=
    fun s => by simpa using hasDerivAt_const s (1 : Matrix (Fin 0) (Fin 0) ℂ)
  have hC : ∀ s : ℝ, Commute C (0 : Matrix (Fin 0) (Fin 0) ℂ) :=
    fun _ => Commute.zero_right C
  exact ⟨star_mul_const_mul_eq_of_commute C hG rfl hU hC t,
    commute_of_commute_generator C hG rfl hU hC t⟩

end EvolutionCommutantTest
