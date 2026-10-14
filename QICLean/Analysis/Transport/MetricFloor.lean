/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.ProjectionCfcUpperBound
import QICLean.Analysis.ProjectionQuadraticBound
import QICLean.Analysis.Transport.NormDerivative

/-!
# Filtered-norm bounds from scalar metric floors

A positive scalar lower bound for a metric controls the squared norm of the
vector obtained by applying its negative quarter power. A polynomial
lower bound therefore gives a logarithmic upper bound for every prevector
of norm at most one. The real logarithm has its assigned value zero at
zero; this convention is relevant only to the zero prevector.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 603--621, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix.Transport
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive scalar metric floor bounds the squared filtered norm.
Auxiliary norm estimate for OpenAI, `07-comparators.tex`, lines 603--621. -/
theorem filteredNormSq_le_of_scalar_floor {M : Matrix ι ι ℂ} (hM : M.PosDef)
    {b : ℝ} (hb : 0 < b) (hfloor : b • (1 : Matrix ι ι ℂ) ≤ M) (pre : ι → ℂ) :
    filteredNormSq M pre ≤ b ^ (-(1 / 2) : ℝ) *
      ‖(EuclideanSpace.equiv ι ℂ).symm pre‖ ^ 2 := by
  classical
  have hnorm : (star pre ⬝ᵥ pre).re = ‖(EuclideanSpace.equiv ι ℂ).symm pre‖ ^ 2 :=
    re_star_dotProduct_self_eq_norm_sq pre
  simpa only [filteredNormSq_eq hM, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, Complex.smul_re, smul_eq_mul, hnorm] using
    Matrix.re_dotProduct_mulVec_le_of_le
      (hM.rpow_le_smul_one_of_scalar_floor hb (by norm_num : (-(1 / 2) : ℝ) ≤ 0) hfloor)
      pre


/-- A polynomial scalar metric floor gives a logarithmic filtered-norm bound
for every prevector of norm at most one, including the zero prevector.
Auxiliary logarithmic estimate for OpenAI, `07-comparators.tex`, lines 603--621. -/
theorem log_filteredNormSq_le_of_rpow_floor {M : Matrix ι ι ℂ} (hM : M.PosDef)
    {C x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hfloor : x ^ (-C) • (1 : Matrix ι ι ℂ) ≤ M) (pre : ι → ℂ)
    (hpre : ‖(EuclideanSpace.equiv ι ℂ).symm pre‖ ≤ 1) :
    Real.log (filteredNormSq M pre) ≤ (C / 2) * Real.log x := by
  classical
  by_cases hzero : pre = 0
  · simpa only [hzero, filteredNormSq, filteredRaw, Matrix.mulVec_zero,
      dotProduct_zero, Complex.zero_re, Real.log_zero] using
      mul_nonneg (div_nonneg hC (by norm_num : 0 ≤ (2 : ℝ))) (Real.log_nonneg hx)
  · have hscalar : (x ^ (-C)) ^ (-(1 / 2) : ℝ) = x ^ (C / 2) := by
      rw [← Real.rpow_mul (le_trans zero_le_one hx)]
      congr 1
      ring
    have hpreSq : ‖(EuclideanSpace.equiv ι ℂ).symm pre‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg ((EuclideanSpace.equiv ι ℂ).symm pre)]
    have hbound : filteredNormSq M pre ≤ x ^ (C / 2) := by
      simpa only [hscalar, mul_one] using
        (filteredNormSq_le_of_scalar_floor hM
          (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) (-C)) hfloor pre).trans
          (mul_le_mul_of_nonneg_left hpreSq (Real.rpow_nonneg
            (Real.rpow_nonneg (le_trans zero_le_one hx) (-C)) (-(1 / 2) : ℝ)))
    simpa only [Real.log_rpow (zero_lt_one.trans_le hx)] using
      Real.log_le_log (filteredNormSq_pos hM hzero) hbound


end Matrix.Transport
