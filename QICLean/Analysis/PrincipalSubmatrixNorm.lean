/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors, QICLean contributors
-/
import QICLean.Analysis.MatrixFramePerturbation

/-!
# The operator norm of a principal submatrix

Restricting the rows and columns of a complex matrix along the same injective
index map is contractive for the Hilbert-space operator norm. The result is
independent of Jordan forms, positivity and spectral assumptions. Empty row
and column index spaces are included.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

/-- Restriction to an injectively indexed principal submatrix is contractive. -/
theorem l2_opNorm_principal_submatrix_le {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix n n ℂ) (e : m → n) (he : Function.Injective e) :
    ‖A.submatrix e e‖ ≤ ‖A‖ := by
  let V : Matrix n m ℂ := (1 : Matrix n n ℂ).submatrix id e
  have hV : Vᴴ * V = 1 := by
    calc
      Vᴴ * V = V.submatrix e id := by
        simpa [V, conjTranspose_submatrix] using one_submatrix_mul e (Equiv.refl n) V
      _ = 1 := by simpa [V, submatrix_submatrix] using submatrix_one (α := ℂ) e he
  have hn : ‖V‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hV
  have hcompress : Vᴴ * A * V = A.submatrix e e := by
    calc
      Vᴴ * A * V = A.submatrix e id * V := by
        congr 1
        simpa [V, conjTranspose_submatrix] using one_submatrix_mul e (Equiv.refl n) A
      _ = A.submatrix e e := by
        simpa [V, submatrix_submatrix] using
          mul_submatrix_one (Equiv.refl n) e (A.submatrix e id)
  rw [← hcompress]
  calc
    ‖Vᴴ * A * V‖ ≤ ‖Vᴴ‖ * ‖A‖ * ‖V‖ :=
      (l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖A‖ * 1 := by rw [l2_opNorm_conjTranspose]; gcongr
    _ = ‖A‖ := by ring

end Matrix
