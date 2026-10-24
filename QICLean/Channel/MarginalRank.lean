/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.MarginalSupportAbsorption
import QICLean.Algebra.MatrixRankKronecker

/-!
# Rank of a positive operator and its marginals

The rank of a bipartite positive semidefinite operator is at most the product
of the ranks of its two marginals. This follows from containment of its support
in the tensor product of the marginal supports. No normalization or nonempty
index type is required.
-/

open scoped Kronecker ComplexOrder

namespace Matrix

/-- The rank of a positive semidefinite bipartite operator is bounded by the
product of the ranks of its marginals, including zero-dimensional factors. -/
theorem PosSemidef.rank_le_rank_partialTraceRight_mul_rank_partialTraceLeft
    {L R : Type*} [Fintype L] [Fintype R]
    {ρ : Matrix (L × R) (L × R) ℂ} (hρ : ρ.PosSemidef) :
    ρ.rank ≤ (Matrix.partialTraceRight ρ).rank * (Matrix.partialTraceLeft ρ).rank := by
  classical
  let ω := Matrix.partialTraceRight ρ ⊗ₖ Matrix.partialTraceLeft ρ
  have hk : LinearMap.ker ω.mulVecLin ≤
      LinearMap.ker ρ.mulVecLin := by
    intro v hv
    exact hρ.productMarginals_kernel_le v hv
  have hd := Submodule.finrank_mono hk
  have hρdim := ρ.mulVecLin.finrank_range_add_finrank_ker
  have hωdim := ω.mulVecLin.finrank_range_add_finrank_ker
  rw [← rank_kronecker]
  change Module.finrank ℂ (LinearMap.range ρ.mulVecLin) ≤
    Module.finrank ℂ (LinearMap.range ω.mulVecLin)
  omega

end Matrix
