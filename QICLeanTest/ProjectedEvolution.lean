/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProjectedEvolution

/-! Consumers of the projected-generator existence theorem. -/

open scoped Matrix Matrix.Norms.L2Operator ContDiff
open MatrixEvolution

namespace ProjectedEvolutionTest

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Smoothness requires no Hermiticity, continuity, or contraction hypothesis.
example (P : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (H B : Matrix n n ℂ) :
    ContDiff ℝ ∞ (projectedGenerator P H B) :=
  contDiff_projectedGenerator P H B ∞

-- An unprojected interaction-picture observable has an actual unitary flow;
-- no commutativity of the two arbitrary Hermitian matrices is supplied.
example (H B : Matrix n n ℂ) (hH : H.IsHermitian) (hB : B.IsHermitian) :
    ∃ U : ℝ → Matrix n n ℂ, U 0 = 1 ∧
      (∀ t, HasDerivAt U
        ((Complex.I • (Matrix.hermitianUnitaryPath H t * B *
          Matrix.hermitianUnitaryPath H (-t))) * U t) t) ∧
      (∀ t, U t ∈ Matrix.unitaryGroup n ℂ) := by
  obtain ⟨U, hU0, hU, hunit, _⟩ := exists_unique_projected_unitary_solution
    (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (fun _ hA ↦ hA) (fun _ ↦ le_rfl) hH hB
  exact ⟨U, hU0, hU, hunit⟩

-- With the identity projection, the constructed comparison flow agrees
-- exactly, including its phase, with the explicit product at every signed
-- time. No commutation assumption is imposed on the two Hamiltonians.
example (H' H : Matrix n n ℂ) (hH' : H'.IsHermitian) (hH : H.IsHermitian) :
    ∃ U : ℝ → Matrix n n ℂ, U 0 = 1 ∧
      (∀ t, HasDerivAt U
        ((Complex.I • (Matrix.hermitianUnitaryPath H' t * (H' - H) *
          Matrix.hermitianUnitaryPath H' (-t))) * U t) t) ∧
      (∀ t, U t ∈ Matrix.unitaryGroup n ℂ) ∧
      ∀ t : ℝ, U t = Matrix.hermitianUnitaryPath H' t * Matrix.hermitianUnitaryPath H (-t) := by
  obtain ⟨U, hU0, hU, hunit, _, hcompare⟩ := exists_unique_projected_unitary_solution_compare
    (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (fun _ hA ↦ hA) (fun _ ↦ le_rfl) hH' hH
  refine ⟨U, hU0, hU, hunit, fun t ↦ ?_⟩
  have hle := hcompare t 0 (fun s _ ↦ by simp [projectedGenerator])
  have hzero :
      ‖Matrix.hermitianUnitaryPath H' t * Matrix.hermitianUnitaryPath H (-t) - U t‖ = 0 :=
    le_antisymm (by simpa only [zero_mul] using hle) (norm_nonneg _)
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

-- The explicit product's initial derivative fixes the sign of H' - H
-- without any Hermiticity or commutativity hypothesis.
example (H' H : Matrix n n ℂ) :
    HasDerivAt
      (fun s ↦ Matrix.hermitianUnitaryPath H' s * Matrix.hermitianUnitaryPath H (-s))
      (Complex.I • (H' - H)) 0 := by
  simpa using hasDerivAt_hermitianUnitaryPath_mul_neg H' H 0

-- The zero map's constructed evolution is the constant identity. This uses
-- the uniqueness conclusion with an independently specified solution.
example (H B : Matrix n n ℂ) (hH : H.IsHermitian) (hB : B.IsHermitian) :
    ∃ U : ℝ → Matrix n n ℂ, U = (fun _ ↦ 1) ∧
      (∀ t, HasDerivAt U 0 t) ∧ (∀ t, U t ∈ Matrix.unitaryGroup n ℂ) := by
  obtain ⟨U, _hU0, hU, hunit, huniq⟩ := exists_unique_projected_unitary_solution
    (0 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (fun _ _ ↦ Matrix.isHermitian_zero)
    (fun A ↦ by simp) hH hB
  have heq : (fun _ : ℝ ↦ (1 : Matrix n n ℂ)) = U :=
    huniq _ rfl (fun t ↦ by
      simpa [projectedGenerator] using hasDerivAt_const t (1 : Matrix n n ℂ))
  exact ⟨U, heq.symm, fun t ↦ by simpa [projectedGenerator] using hU t, hunit⟩

-- The norm bound is valid at negative times, without assuming B Hermitian.
example (P : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (hP : ∀ A, ‖P A‖ ≤ ‖A‖)
    (H B : Matrix n n ℂ) (hH : H.IsHermitian) :
    ‖projectedGenerator P H B (-2)‖ ≤ ‖B‖ :=
  norm_projectedGenerator_le P hP hH B (-2)

-- Empty index types need no artificial Nonempty or Nontrivial assumptions.
example (P : Matrix (Fin 0) (Fin 0) ℂ →ₗ[ℂ] Matrix (Fin 0) (Fin 0) ℂ)
    (H B : Matrix (Fin 0) (Fin 0) ℂ) :
    ∃ U : ℝ → Matrix (Fin 0) (Fin 0) ℂ, U 0 = 1 ∧
      (∀ t, HasDerivAt U ((Complex.I • projectedGenerator P H B t) * U t) t) ∧
      (∀ t, U t ∈ Matrix.unitaryGroup (Fin 0) ℂ) := by
  have hherm (A : Matrix (Fin 0) (Fin 0) ℂ) : A.IsHermitian := Subsingleton.elim _ _
  obtain ⟨U, hU0, hU, hunit, _⟩ := exists_unique_projected_unitary_solution P
    (fun A _ ↦ hherm (P A))
    (fun A ↦ le_of_eq (congrArg norm (Subsingleton.elim (P A) A)))
    (hherm H) (hherm B)
  exact ⟨U, hU0, hU, hunit⟩

end ProjectedEvolutionTest

set_option linter.hashCommand false

/--
info: 'MatrixEvolution.exists_unique_projected_unitary_solution' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MatrixEvolution.exists_unique_projected_unitary_solution
