/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SubnormalizedPureStateError

/-! Edge-case regressions for SubnormalizedPureStateError in the compression proof. -/

open scoped Matrix Matrix.Norms.L2Operator

-- Independent ket/bra dimensions, with no normalization assumptions.
example (u : EuclideanSpace ℂ (Fin 2)) (v : EuclideanSpace ℂ (Fin 3)) :
    Matrix.rectangularTraceNorm (Matrix.euclideanOuterProduct u v) ≤ ‖u‖ * ‖v‖ := by
  exact Matrix.rectangularTraceNorm_euclideanOuterProduct_le u v

-- A zero bra needs no nonzero support assumption and has exactly zero norm.
example (u : EuclideanSpace ℂ (Fin 2)) :
    Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct u (0 : EuclideanSpace ℂ (Fin 3))) = 0 := by
  apply le_antisymm
  · simpa using Matrix.rectangularTraceNorm_euclideanOuterProduct_le u
      (0 : EuclideanSpace ℂ (Fin 3))
  · exact Matrix.rectangularTraceNorm_nonneg _

-- The generic rectangular result bridges to QICLean's actual square trace norm.
example (v w : EuclideanSpace ℂ (Fin 3)) :
    Matrix.traceNorm
      (Matrix.euclideanOuterProduct v v - Matrix.euclideanOuterProduct w w) ≤
      (‖v‖ + ‖w‖) * ‖v - w‖ := by
  exact Matrix.rectangularTraceNorm_pure_density_sub_le v w

-- A genuinely subnormalized vector, with the comparison vector zero.
example : Matrix.rectangularTraceNorm
    (Matrix.euclideanOuterProduct
      (EuclideanSpace.single (0 : Fin 2) (1 / 2 : ℂ))
      (EuclideanSpace.single (0 : Fin 2) (1 / 2 : ℂ)) -
      Matrix.euclideanOuterProduct (0 : EuclideanSpace ℂ (Fin 2)) 0) ≤
    2 * ‖EuclideanSpace.single (0 : Fin 2) (1 / 2 : ℂ)‖ := by
  simpa using Matrix.rectangularTraceNorm_pure_density_sub_le_two
    (EuclideanSpace.single (0 : Fin 2) (1 / 2 : ℂ))
    (0 : EuclideanSpace ℂ (Fin 2)) (by norm_num) (by simp)

-- An empty retained output is allowed before and after discard.
example (v w : EuclideanSpace ℂ (Fin 0 × Fin 3)) :
    Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct v v) -
        Matrix.partialTraceRight (Matrix.euclideanOuterProduct w w)) ≤
      (‖v‖ + ‖w‖) * ‖v - w‖ := by
  exact Matrix.rectangularTraceNorm_partialTraceRight_pure_density_sub_le v w

-- An empty discarded register does not require positive register dimension.
example (v w : EuclideanSpace ℂ (Fin 2 × Fin 0)) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct v v) -
        Matrix.partialTraceRight (Matrix.euclideanOuterProduct w w)) ≤ 2 * ‖v - w‖ := by
  exact Matrix.rectangularTraceNorm_partialTraceRight_pure_density_sub_le_two v w hv hw
