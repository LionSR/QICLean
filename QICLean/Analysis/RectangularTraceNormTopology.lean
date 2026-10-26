/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RectangularTraceNorm
import Mathlib.Topology.Order.OrderClosed

/-!
# Closed trace-norm sublevel sets

Contraction duality expresses a trace-norm sublevel set as an intersection of closed
sublevel sets of continuous trace pairings. This applies to arbitrary rectangular complex
matrices, including empty coordinate spaces.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Every sublevel set of the rectangular trace norm is closed. -/
theorem isClosed_setOf_rectangularTraceNorm_le (c : ℝ) :
    IsClosed {A : Matrix m n ℂ | rectangularTraceNorm A ≤ c} := by
  have heq : {A : Matrix m n ℂ | rectangularTraceNorm A ≤ c} =
      ⋂ U : Matrix m n ℂ, ⋂ _ : ‖U‖ ≤ 1, {A | ‖(Aᴴ * U).trace‖ ≤ c} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hA U hU
      exact (norm_trace_conjTranspose_mul_le_rectangularTraceNorm A U hU).trans hA
    · exact rectangularTraceNorm_le_of_forall_contraction A c
  rw [heq]
  exact isClosed_iInter fun U ↦ isClosed_iInter fun _ ↦
    isClosed_le
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_trace.norm)
      continuous_const

end Matrix
