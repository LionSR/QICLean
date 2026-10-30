/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.SchwarzCovariance
import QICLeanTest.IrreducibleSchwarzNonTP

/-! Apply Proposition 6.7 to a concrete irreducible positive unital Schwarz
map that is not trace preserving, including nonzero eigenvectors at zero. -/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix IrreducibleSchwarzNonTP

namespace SchwarzCovarianceNonTP

-- This uses the existing proved counterexample, with no new state assumption.
example : ¬ IsTracePreservingMap T ∧
    ∃ m : ℕ, ∃ _hm : 0 < m,
      let γ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑m)
      m ≤ 4 ∧
      ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
        (∀ X : Mat, T ((U : Mat)ᴴ * X * (U : Mat)) =
          (U : Mat)ᴴ * T X * (U : Mat)) ∧
        (∀ μ : ℂ, ∀ X : Mat, T X = μ • X →
          T ((U : Mat)ᴴ * X) = (star γ * μ) • ((U : Mat)ᴴ * X) ∧
          T (X * (U : Mat)) = (γ * μ) • (X * (U : Mat))) := by
  obtain ⟨m, hm, hbound, _, U, _, _, hCov, hShift⟩ :=
    SchwarzMap.wolf_proposition_6_7 T positive unital schwarz irreducible
  exact ⟨not_tracePreserving, m, hm, by simpa using hbound, U, hCov, hShift⟩

-- A zero eigenvalue is allowed: the matrix unit is nonzero and both
-- transported vectors remain nonzero. No division by μ is legitimate here.
example :
    Module.End.HasEigenvector T 0
      (((1 : Matrix.unitaryGroup (Fin 2) ℂ) : Mat)ᴴ * !![0, 1; 0, 0]) ∧
    Module.End.HasEigenvector T 0
      (!![0, 1; 0, 0] * ((1 : Matrix.unitaryGroup (Fin 2) ℂ) : Mat)) := by
  have hX : Module.End.HasEigenvector T 0 (!![0, 1; 0, 0] : Mat) := by
    refine Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · simp [T]
    · intro h
      have h01 := congrFun (congrFun h 0) 1
      norm_num at h01
  simpa using SchwarzMap.hasEigenvector_shifts_of_peripheral_unitary
    T positive unital schwarz (γ := 1) (by simp) 1 (by simpa using unital) hX

end SchwarzCovarianceNonTP
