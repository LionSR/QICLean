/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OptimizedPureStateTraceError
import QICLean.Analysis.PureStateTraceDistance
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Imported tests for optimized pure-state error

The examples use nonunit vectors with a complex phase, orthogonal vectors,
and squared fidelity exactly one half. They distinguish the full nuclear
norm from half trace distance and include zero and nonreal coefficients.
-/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped Matrix InnerProductSpace

/-- info:
'Matrix.re_trace_abs_vecMulVec_sub_smul_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.re_trace_abs_vecMulVec_sub_smul_eq

/-- info:
'Matrix.rectangularTraceNorm_eq_re_trace_abs' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.rectangularTraceNorm_eq_re_trace_abs

/-- info:
'Matrix.rectangularTraceNorm_euclideanOuterProduct_self' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.rectangularTraceNorm_euclideanOuterProduct_self

/-- info:
'Matrix.rectangularTraceNorm_vecMulVec_sub_smul_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.rectangularTraceNorm_vecMulVec_sub_smul_eq

/-- info:
'Matrix.isLeast_optimizedPureTraceError' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.isLeast_optimizedPureTraceError

/-- info:
'Matrix.traceDistance_vecMulVec_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.traceDistance_vecMulVec_eq

namespace Matrix

private def ket (i : Fin 2) : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 i 1

private theorem norm_ket (i : Fin 2) : ‖ket i‖ = 1 := by
  simp [ket]

private theorem ket_ne_zero (i : Fin 2) : ket i ≠ 0 :=
  norm_ne_zero_iff.mp (by simp [norm_ket])

private theorem inner_ket_zero_one : ⟪ket 0, ket 1⟫_ℂ = 0 := by
  norm_num [ket, PiLp.inner_apply, Fin.sum_univ_two]

private def scaledTarget : EuclideanSpace ℂ (Fin 2) := (2 : ℂ) • ket 0

private def phasedApproximant : EuclideanSpace ℂ (Fin 2) := (3 * Complex.I) • ket 0

-- The norms are two and three; their common line has squared fidelity one.
example :
    IsLeast {r : ℝ | ∃ z : ℂ,
      rectangularTraceNorm (euclideanOuterProduct scaledTarget scaledTarget -
        z • euclideanOuterProduct phasedApproximant phasedApproximant) /
          rectangularTraceNorm (euclideanOuterProduct scaledTarget scaledTarget) = r} 0 := by
  convert isLeast_optimizedPureTraceError scaledTarget phasedApproximant
      (smul_ne_zero (by norm_num) (ket_ne_zero 0))
      (smul_ne_zero (by simp) (ket_ne_zero 0)) using 1 <;>
    norm_num [scaledTarget, phasedApproximant, Real.optimizedPureTraceError,
      inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K,
      norm_smul, norm_mul, norm_ket]

-- Orthogonal unit states have full error two and half trace distance one.
example :
    rectangularTraceNorm (euclideanOuterProduct (ket 0) (ket 0) -
      euclideanOuterProduct (ket 1) (ket 1)) = 2 ∧
      traceDistance (euclideanOuterProduct (ket 0) (ket 0))
        (euclideanOuterProduct (ket 1) (ket 1)) = 1 := by
  constructor
  · convert rectangularTraceNorm_vecMulVec_sub_smul_eq (ket 0) (ket 1)
      (norm_ket 0) (norm_ket 1) 1 (by norm_num) using 1 <;>
      norm_num [euclideanOuterProduct, inner_ket_zero_one]
  · simpa [euclideanOuterProduct, inner_ket_zero_one] using
      traceDistance_vecMulVec_eq (norm_ket 0) (norm_ket 1)

private theorem orthogonal_minimum :
    IsLeast {r : ℝ | ∃ z : ℂ,
      rectangularTraceNorm (euclideanOuterProduct (ket 0) (ket 0) -
        z • euclideanOuterProduct (ket 1) (ket 1)) /
          rectangularTraceNorm (euclideanOuterProduct (ket 0) (ket 0)) = r} 1 := by
  simpa [Real.optimizedPureTraceError, inner_ket_zero_one] using
    isLeast_optimizedPureTraceError (ket 0) (ket 1) (ket_ne_zero 0) (ket_ne_zero 1)

-- The saturated minimum permits the zero approximant.
example :
    rectangularTraceNorm (euclideanOuterProduct (ket 0) (ket 0) -
      (0 : ℂ) • euclideanOuterProduct (ket 1) (ket 1)) /
        rectangularTraceNorm (euclideanOuterProduct (ket 0) (ket 0)) = 1 := by
  have hden : rectangularTraceNorm (euclideanOuterProduct (ket 0) (ket 0)) = 1 := by
    simpa [norm_ket] using rectangularTraceNorm_euclideanOuterProduct_self (ket 0)
  simp [hden]

-- The lower bound is applied to an actual nonreal density coefficient.
example :
    1 ≤ rectangularTraceNorm (euclideanOuterProduct (ket 0) (ket 0) -
      Complex.I • euclideanOuterProduct (ket 1) (ket 1)) /
        rectangularTraceNorm (euclideanOuterProduct (ket 0) (ket 0)) :=
  orthogonal_minimum.2 ⟨Complex.I, rfl⟩

-- The nonunit vector |0⟩+|1⟩ lies exactly on the fidelity-one-half boundary.
example :
    IsLeast {r : ℝ | ∃ z : ℂ,
      rectangularTraceNorm (euclideanOuterProduct (ket 0) (ket 0) -
        z • euclideanOuterProduct (ket 0 + ket 1) (ket 0 + ket 1)) /
          rectangularTraceNorm (euclideanOuterProduct (ket 0) (ket 0)) = r} 1 := by
  have hnorm : ‖ket 0 + ket 1‖ ^ 2 = 2 := by
    simpa [norm_ket, pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (𝕜 := ℂ) (ket 0) (ket 1) inner_ket_zero_one
  have hne : ket 0 + ket 1 ≠ 0 := by
    intro h
    norm_num [h] at hnorm
  convert isLeast_optimizedPureTraceError (ket 0) (ket 0 + ket 1) (ket_ne_zero 0) hne
    using 1 <;>
    norm_num [Real.optimizedPureTraceError, inner_add_right,
      inner_self_eq_norm_sq_to_K, norm_ket, inner_ket_zero_one, hnorm]

end Matrix
