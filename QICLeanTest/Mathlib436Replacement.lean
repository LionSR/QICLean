/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixUnitaryBetween
import QICLean.Analysis.SpectralRadiusPowerDecay
import QICLean.Channel.OrderedCP

/-! # Boundary cases and axiom checks for Mathlib 4.36 proof replacements -/

open scoped Matrix NNReal ENNReal

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.IsIsometry.isUnitaryBetween_of_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsIsometry.isUnitaryBetween_of_card_eq

/-- info:
'geometric_bound_of_spectralRadius_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms geometric_bound_of_spectralRadius_lt

/-- info:
'stinespringW_mulVec_surjective_of_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stinespringW_mulVec_surjective_of_minimal

-- Empty coordinate spaces require no nonemptiness premise.
example (A : Matrix (Fin 0) (Fin 0) ℂ) : A.IsUnitaryBetween := by
  have hA : A.IsIsometry := Subsingleton.elim _ _
  exact hA.isUnitaryBetween_of_card_eq A rfl

-- Minimality is still meaningful when the ancilla dimension is zero.
example {d d' : ℕ}
    {T : Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (V : Matrix (Fin d' × Fin 0) (Fin d) ℂ)
    (hV : ∀ A : Matrix (Fin d') (Fin d') ℂ,
      T A = Vᴴ * stinespringPi (r := 0) A * V)
    (hmin : 0 = Channel.choiRank T) :
    Function.Surjective (stinespringW V).mulVec :=
  stinespringW_mulVec_surjective_of_minimal V hV hmin

-- The geometric estimate covers the zeroth power, not just an eventual tail.
example {A : Type*} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℂ A]
    (a : A) (rate : ℝ≥0) (ha : spectralRadius ℂ a < (rate : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧ ‖a ^ 0‖ ≤ C * (rate : ℝ) ^ 0 := by
  obtain ⟨C, hC, hbound⟩ := geometric_bound_of_spectralRadius_lt a rate ha
  exact ⟨C, hC, hbound 0⟩

-- The algebra need not be nontrivial or carry a norm-one instance.
example {A : Type*} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℂ A]
    [Subsingleton A] (a : A) (rate : ℝ≥0)
    (ha : spectralRadius ℂ a < (rate : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * (rate : ℝ) ^ n :=
  geometric_bound_of_spectralRadius_lt a rate ha
