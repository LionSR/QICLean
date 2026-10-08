/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RectangularTraceNormAlgebra

/-! Edge-case regressions for RectangularTraceNormAlgebra in the compression proof. -/

open scoped Matrix Matrix.Norms.L2Operator Kronecker

-- A complex unit phase is preserved on an unequal rectangular matrix.
example (A : Matrix (Fin 2) (Fin 3) ℂ) :
    Matrix.rectangularTraceNorm (Complex.I • A) = Matrix.rectangularTraceNorm A := by
  simp

-- An off-diagonal affected matrix unit has arbitrary complex exterior input.
example (A : Matrix (Fin 3) (Fin 2) ℂ) :
    Matrix.rectangularTraceNorm
      ((Matrix.single (0 : Fin 2) (1 : Fin 2) 1) ⊗ₖ A) =
      Matrix.rectangularTraceNorm A := by
  exact Matrix.rectangularTraceNorm_single_kronecker _ _ A

-- Branches use different basis injections and arbitrary complex coefficients.
example (c : Fin 2 → ℂ) (A : Fin 2 → Matrix (Fin 3) (Fin 2) ℂ) :
    Matrix.rectangularTraceNorm
      (∑ i, c i • ((Matrix.single i (3 : Fin 4) 1) ⊗ₖ A i)) ≤
      ∑ i, ‖c i‖ * Matrix.rectangularTraceNorm (A i) := by
  refine (Matrix.rectangularTraceNorm_sum_smul_le Finset.univ c
    (fun i ↦ (Matrix.single i (3 : Fin 4) 1) ⊗ₖ A i)).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun r ↦ ‖c i‖ * r)
    (Matrix.rectangularTraceNorm_single_kronecker i (3 : Fin 4) (A i))

-- Empty corrected branch families have exactly zero total norm.
example (A : Fin 0 → Matrix (Fin 2) (Fin 3) ℂ) :
    Matrix.rectangularTraceNorm (∑ i, A i) = 0 := by
  simp

-- Empty private domains stay valid under adjoint and physical reinsertion.
example (A : Matrix (Fin 3) (Fin 0) ℂ) :
    Matrix.rectangularTraceNorm Aᴴ = Matrix.rectangularTraceNorm A ∧
      Matrix.rectangularTraceNorm
        ((Matrix.single (1 : Fin 2) (2 : Fin 3) 1) ⊗ₖ A) =
        Matrix.rectangularTraceNorm A := by
  exact ⟨Matrix.rectangularTraceNorm_conjTranspose A,
    Matrix.rectangularTraceNorm_single_kronecker _ _ A⟩
