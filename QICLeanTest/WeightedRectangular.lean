/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.WeightedRectangular
import QICLean.Channel.RectangularTraceNormContraction

/-! Regressions for unequal dimensions, zero weights, and arbitrary rectangular
exterior inputs in Theorem 5.2 of the polynomial-PEPS paper. -/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix

namespace WeightedRectangularTest

-- The independent lists have different dimensions and contain zeros; neither
-- weight has full support, and the tested matrix is unrestricted.
example (W : Matrix (Fin 3) (Fin 2) ℂ) :
    rectangularTraceNorm (halfWeighted ![1, 0, 0] ![0, 1] W) ≤
      Real.sqrt (frobeniusNormSq (quarterWeighted ![1, 0, 0] ![0, 1] W)) := by
  apply rectangularTraceNorm_halfWeighted_le
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]

-- An empty domain is a legitimate rectangular nuclear-norm input.
example (A : Matrix (Fin 3) (Fin 0) ℂ) : rectangularTraceNorm A = 0 := by
  rw [rectangularTraceNorm_eq_sum_fin]
  simp

-- Generic quantum states require only semidefiniteness, including singular
-- states, with independent rectangular dimensions.
example (R : Matrix (Fin 3) (Fin 3) ℂ) (S : Matrix (Fin 2) (Fin 2) ℂ)
    (O : Matrix (Fin 2) (Fin 3) ℂ) (hR : R.PosSemidef) (hS : S.PosSemidef)
    (hRtr : R.trace.re = 1) (hStr : S.trace.re = 1) (hO : ‖O‖ ≤ 1) :
    frobeniusNormSq (S ^ (1 / 4 : ℝ) * O * R ^ (1 / 4 : ℝ)) ≤ 1 :=
  frobeniusNormSq_rpow_quarter_mul_le_one S R O hS hR hStr hRtr hO

-- The input has unequal ket/bra dimensions, and the exterior maps are
-- independent. No Hermiticity or positivity condition is available on Z.
example (Z : Matrix (Fin 1) (Fin 3) ℂ)
    (K : Matrix (Fin 2 × Fin 4) (Fin 1) ℂ)
    (L : Matrix (Fin 2 × Fin 4) (Fin 3) ℂ) (hK : ‖K‖ ≤ 1) (hL : ‖L‖ ≤ 1) :
    rectangularTraceNorm (partialTraceRight (K * Z * Lᴴ)) ≤ rectangularTraceNorm Z :=
  rectangularTraceNorm_partialTraceRight_mul_conjTranspose_le Z K L hK hL

-- The coefficient is unchanged by ordinary full transpose, including its
-- complex phase; the operation is not an adjoint.
example (W : Matrix (Fin 3) (Fin 2) ℂ) (p : Fin 3 → ℝ) (q : Fin 2 → ℝ) :
    frobeniusNormSq (quarterWeighted q p (Complex.I • W)ᵀ) =
      frobeniusNormSq (quarterWeighted p q (Complex.I • W)) :=
  frobeniusNormSq_quarterWeighted_transpose p q (Complex.I • W)

end WeightedRectangularTest
