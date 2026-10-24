/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OptimizedPureTraceError

/-!
# Missing fidelity mass from small optimized pure-state error

On the unsaturated branch of the optimized error, the missing squared-fidelity
mass is at most half the full trace error. This is a scalar consequence of the
formula following `eq:before-trig` in Schuch–Wolf–Verstraete–Cirac,
arXiv:0705.0292v2, `paper_v2.tex`, lines 160–173. The statement does not identify
the scalar function with a matrix minimization problem.
-/

namespace Real

/-- A full optimized error strictly below one bounds the missing squared-fidelity
mass by half the error. The small-error hypothesis itself forces `f ≥ 1/2`, so
no separate lower bound on `f` is needed. Source: SWVC08, arXiv:0705.0292v2,
`paper_v2.tex`, lines 160–173. -/
theorem one_sub_le_half_error_of_optimizedPureTraceError_le {f δ : ℝ} (hf : f ≤ 1) (hδ : δ < 1)
    (he : optimizedPureTraceError f ≤ δ) : 1 - f ≤ δ / 2 := by
  have hh := half_le_of_optimizedPureTraceError_lt_one (he.trans_lt hδ)
  have hs := optimizedPureTraceError_sq hh hf
  have hn := optimizedPureTraceError_nonneg f
  have hm := mul_nonneg (sub_nonneg.mpr hf) (show 0 ≤ 2 * f - 1 by linarith)
  nlinarith

end Real
