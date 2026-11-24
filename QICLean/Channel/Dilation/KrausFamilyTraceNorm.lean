/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausMap.KrausFamily
import QICLean.Analysis.Isometry.FramePerturbation
import QICLean.Analysis.TraceNorm.RectangularTraceNormContraction
import QICLean.Channel.Dilation.Stinespring

/-!
# Trace-norm contraction of trace-preserving Kraus families

A trace-preserving finite Kraus family `K` from `α` to `β` contracts the trace norm of every
matrix, Hermitian or not, on any finite index types. The Stinespring matrix
`B = stinespringVGen K.op`, with `B (b, i) a = (K.op i) b a`, is a contraction, since
`Bᴴ B = ∑ᵢ Kᵢᴴ Kᵢ = 1`, and the map of `K` is `X ↦ Tr_K (B X Bᴴ)`; the partial trace of such
a compression contracts the trace norm.

## Main results

* `KrausFamily.IsTP.rectangularTraceNorm_map_le` — `‖K.map X‖₁ ≤ ‖X‖₁`.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace KrausFamily

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A trace-preserving finite Kraus family contracts the trace norm of every matrix. -/
theorem IsTP.rectangularTraceNorm_map_le {K : KrausFamily α β} (hK : K.IsTP)
    (X : Matrix α α ℂ) : rectangularTraceNorm (K.map X) ≤ rectangularTraceNorm X := by
  classical
  have hB : ‖stinespringVGen K.op‖ ≤ 1 :=
    l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one
      ((stinespringVGen_conjTranspose_mul K).trans hK)
  rw [map_eq_partialTraceRight]
  exact rectangularTraceNorm_partialTraceRight_mul_conjTranspose_le X _ _ hB hB

end KrausFamily
