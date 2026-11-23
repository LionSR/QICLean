/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Rank-one matrices acting on Euclidean space

The rank-one matrix `|Ω⟩⟨Ω| = vecMulVec Ω (star Ω)` acts on Euclidean space by
`ψ ↦ ⟨Ω, ψ⟩ Ω`.

## Main results

* `Matrix.toEuclideanLin_vecMulVec_star_self_apply`: `|Ω⟩⟨Ω| ψ = ⟨Ω, ψ⟩ Ω`.
-/

open scoped InnerProductSpace

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank-one matrix `|Ω⟩⟨Ω|` acts by `ψ ↦ ⟨Ω, ψ⟩ Ω`. -/
theorem toEuclideanLin_vecMulVec_star_self_apply (Ω ψ : EuclideanSpace ℂ n) :
    toEuclideanLin (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ψ = ⟪Ω, ψ⟫_ℂ • Ω := by
  rw [← InnerProductSpace.symm_toEuclideanLin_rankOne, LinearEquiv.apply_symm_apply]
  exact InnerProductSpace.rankOne_apply Ω Ω ψ

end Matrix
