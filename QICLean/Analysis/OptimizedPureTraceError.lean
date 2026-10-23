/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Notation.Lemmas
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Scalar amplification of optimized pure-state error

For squared fidelity `f ∈ [0, 1]`, consider the scalar error
`T(f) = 2 √(f (1 - f))` when `f ≥ 1/2`, and `T(f) = 1` otherwise.
The power `f ^ K` describes the squared fidelity of `K` identical copies.
This module proves scalar inequalities only; it does not identify the function
with a matrix optimization problem or prove optimality of product approximants.

## References

Schuch, Wolf, Verstraete and Cirac, arXiv:0705.0292v2, `paper_v2.tex`,
lines 160–173 (the optimized error following `eq:before-trig`) and 472–479
(the tensor-power amplification and its application). The source's formula
`sin (2θ)` is restricted there to `0 ≤ θ ≤ π/4`.
-/

namespace Real

/-- Scalar optimized full trace-norm error as a function of squared fidelity.
On `f ≥ 1/2` this is the formula following `eq:before-trig` in SWVC,
arXiv:0705.0292v2, `paper_v2.tex`, lines 160–173. The other branch has value one.
This definition does not assert the matrix minimization identity. -/
noncomputable def optimizedPureTraceError (f : ℝ) : ℝ :=
  if 1 / 2 ≤ f then 2 * sqrt (f * (1 - f)) else 1

/-- The scalar optimized error is nonnegative. -/
theorem optimizedPureTraceError_nonneg (f : ℝ) : 0 ≤ optimizedPureTraceError f :=
  ite_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _)) (by norm_num)

/-- The square of the scalar error on the high-fidelity branch of SWVC,
arXiv:0705.0292v2, `paper_v2.tex`, lines 160–173. -/
theorem optimizedPureTraceError_sq {f : ℝ} (hf : 1 / 2 ≤ f) (hf₁ : f ≤ 1) :
    optimizedPureTraceError f ^ 2 = 4 * f * (1 - f) := by
  norm_num only [optimizedPureTraceError, hf, ↓reduceIte, mul_pow,
    sq_sqrt (mul_nonneg (by linarith : 0 ≤ f) (sub_nonneg.mpr hf₁)), mul_assoc]

/-- Error below one excludes the saturated branch. -/
theorem half_le_of_optimizedPureTraceError_lt_one {f : ℝ}
    (h : optimizedPureTraceError f < 1) : 1 / 2 ≤ f := by
  grind [optimizedPureTraceError]

private theorem mul_pow_mul_one_sub_le {f : ℝ} (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) (K : ℕ) :
    (K : ℝ) * f ^ K * (1 - f) ≤ 1 - f ^ K := by
  rw [← geom_sum_mul_neg f K]
  refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr hf₁)
  simpa using Finset.sum_le_sum (s := Finset.range K)
    (fun i hi ↦ pow_le_pow_of_le_one hf₀ hf₁ (Nat.le_of_lt (Finset.mem_range.mp hi)))

private theorem mul_variance_le_pow_variance {f : ℝ} (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1)
    (K : ℕ) (hpow : 1 / 2 ≤ f ^ K) :
    (K : ℝ) * f * (1 - f) ≤ 4 * f ^ K * (1 - f ^ K) := by
  have hgeom := mul_pow_mul_one_sub_le hf₀ hf₁ K
  have hquad : f ≤ 4 * (f ^ K) ^ 2 := by nlinarith [sq_nonneg (f ^ K - 1 / 2)]
  nlinarith [mul_le_mul_of_nonneg_left hgeom (by positivity : 0 ≤ 4 * f ^ K),
    mul_le_mul_of_nonneg_right hquad
      (mul_nonneg (Nat.cast_nonneg K) (sub_nonneg.mpr hf₁))]

/-- A scalar strengthening of the tensor-power estimate in SWVC,
arXiv:0705.0292v2, `paper_v2.tex`, lines 472–479. Product error below one
implies amplification by `√(K/4)`, without a separate single-copy smallness assumption. -/
theorem sqrt_mul_optimizedPureTraceError_le_pow_of_lt_one {f : ℝ}
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) {K : ℕ} (hK : 1 ≤ K)
    (hsmall : optimizedPureTraceError (f ^ K) < 1) :
    sqrt ((K : ℝ) / 4) * optimizedPureTraceError f ≤ optimizedPureTraceError (f ^ K) := by
  have hpow := half_le_of_optimizedPureTraceError_lt_one hsmall
  have hf : 1 / 2 ≤ f := hpow.trans (pow_le_of_le_one hf₀ hf₁ (by omega))
  apply (sq_le_sq₀ (mul_nonneg (sqrt_nonneg _) (optimizedPureTraceError_nonneg _))
    (optimizedPureTraceError_nonneg _)).mp
  rw [mul_pow, sq_sqrt (by positivity), optimizedPureTraceError_sq hf hf₁,
    optimizedPureTraceError_sq hpow (pow_le_one₀ hf₀ hf₁)]
  nlinarith [mul_variance_le_pow_variance hf₀ hf₁ K hpow]

/-- Scalar form of the tensor-power estimate in SWVC, arXiv:0705.0292v2,
`paper_v2.tex`, lines 472–474. This includes the saturated branch of the
optimized error; no high-fidelity hypothesis is imposed. -/
theorem sqrt_mul_optimizedPureTraceError_le_pow_of_sq_le {f : ℝ}
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) {K : ℕ} (hK : 1 ≤ K)
    (hsmall : optimizedPureTraceError f ^ 2 ≤ 2 / (K : ℝ)) :
    sqrt ((K : ℝ) / 8) * optimizedPureTraceError f ≤ optimizedPureTraceError (f ^ K) := by
  by_cases hp : optimizedPureTraceError (f ^ K) < 1
  · exact (mul_le_mul_of_nonneg_right (sqrt_le_sqrt (by
      nlinarith [Nat.cast_nonneg (α := ℝ) K]))
      (optimizedPureTraceError_nonneg f)).trans
        (sqrt_mul_optimizedPureTraceError_le_pow_of_lt_one hf₀ hf₁ hK hp)
  · have hs := (le_div_iff₀ (show (0 : ℝ) < K from by exact_mod_cast hK)).mp hsmall
    refine le_trans ?_ (le_of_not_gt hp)
    apply (sq_le_sq₀ (mul_nonneg (sqrt_nonneg _) (optimizedPureTraceError_nonneg _))
      zero_le_one).mp
    rw [mul_pow, sq_sqrt (by positivity)]
    nlinarith

end Real
