/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausFamily
import QICLean.Channel.RectangularTraceNormContraction

/-!
# Trace-norm contraction of trace-preserving Kraus families

A trace-preserving finite Kraus family `K` from `α` to `β` contracts the trace norm of every
matrix, Hermitian or not, on any finite index types. Stacking the operators gives the
contraction `B` with `B (b, i) a = (K.op i) b a`, since `Bᴴ B = ∑ᵢ Kᵢᴴ Kᵢ = 1`, and the map of
`K` is `X ↦ Tr_K (B X Bᴴ)`; the partial trace of such a compression contracts the trace norm.

## Main results

* `KrausFamily.IsTP.rectangularTraceNorm_map_le` — `‖K.map X‖₁ ≤ ‖X‖₁`.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace KrausFamily

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The operators of a family stacked into one matrix. -/
private def stack (K : KrausFamily α β) : Matrix (β × K.Index) α ℂ :=
  Matrix.of fun p a ↦ K.op p.2 p.1 a

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
private theorem stack_conjTranspose_mul (K : KrausFamily α β) :
    (stack K)ᴴ * stack K = K.effect := by
  ext a a'
  simp [stack, effect, mul_apply, Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_comm (γ := β)]

omit [DecidableEq α] [Fintype β] [DecidableEq β] in
private theorem map_eq_partialTraceRight (K : KrausFamily α β) (X : Matrix α α ℂ) :
    K.map X = partialTraceRight (stack K * X * (stack K)ᴴ) := by
  classical
  ext b b'
  simp [map_apply, stack, mul_apply, Matrix.sum_apply]

/-- A trace-preserving finite Kraus family contracts the trace norm of every matrix. -/
theorem IsTP.rectangularTraceNorm_map_le {K : KrausFamily α β} (hK : K.IsTP)
    (X : Matrix α α ℂ) : rectangularTraceNorm (K.map X) ≤ rectangularTraceNorm X := by
  classical
  have hB : ‖stack K‖ ≤ 1 := by
    have h := l2_opNorm_conjTranspose_mul_self (stack K)
    rw [stack_conjTranspose_mul, hK] at h
    have h1 : ‖(1 : Matrix α α ℂ)‖ ≤ 1 := by
      rcases isEmpty_or_nonempty α with _ | _
      · simp [Subsingleton.elim (1 : Matrix α α ℂ) 0]
      · exact (CStarRing.norm_one (E := Matrix α α ℂ)).le
    nlinarith [norm_nonneg (stack K)]
  rw [map_eq_partialTraceRight]
  exact rectangularTraceNorm_partialTraceRight_mul_conjTranspose_le X (stack K) (stack K) hB hB

end KrausFamily
