/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.MaximalOverlap
import QICLean.Entropy.Bipartite

/-!
# Equality of the marginal ranks of a pure state

The two marginal matrices of a bipartite pure state have the same rank.
No normalization or nonempty index assumptions are needed. This is the
Schmidt-rank identity used for the interior-block rank bound in SWVC08,
arXiv:0705.0292v2, lines 269–270 and 333–345.
-/

open scoped ComplexOrder

namespace Matrix

/-- Both marginals of a bipartite pure state have the same rank. -/
theorem rank_partialTraceRight_vecMulVec_eq_rank_partialTraceLeft
    {L R : Type*} [Fintype L] [Fintype R] (ψ : L × R → ℂ) :
    (partialTraceRight (vecMulVec ψ (star ψ))).rank =
      (partialTraceLeft (vecMulVec ψ (star ψ))).rank := by
  classical
  rw [partialTraceRight_vecMulVec_eq, Entropy.partialTraceLeft_vecMulVec_eq_map_conj]
  change (schmidtCoeffMatrix ψ * (schmidtCoeffMatrix ψ)ᴴ).rank =
    (((schmidtCoeffMatrix ψ)ᴴ * schmidtCoeffMatrix ψ)ᴴᵀ).rank
  simp only [rank_transpose, rank_conjTranspose, rank_self_mul_conjTranspose,
    rank_conjTranspose_mul_self]

end Matrix
