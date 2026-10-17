/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Successive matrix actions

Applying the continuous linear maps of a matrix list from left to right gives
the product of the reversed list. The matrices need not commute or be invertible,
and both the list and the finite coordinate type may be empty.

The ascending application convention occurs in `output` in `openai/math`,
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean`, lines 166–169.
This proof is independently written; no upstream Lean proof text is reused.
-/

namespace Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- Successive applications in list order equal the action of the reverse
matrix product, including the empty list and an empty coordinate type. -/
theorem foldl_toEuclideanCLM_eq_reverse_prod (l : List (Matrix ι ι 𝕜))
    (Ω : EuclideanSpace 𝕜 ι) :
    (l.map (fun A ↦ toEuclideanCLM A)).foldl (fun ψ T ↦ T ψ) Ω =
      toEuclideanLin l.reverse.prod Ω := by
  rw [List.foldl_map]
  change l.foldl (fun ψ A ↦ toEuclideanLin A ψ) Ω = _
  induction l generalizing Ω with
  | nil => simp [toEuclideanLin]
  | cons A l ih =>
    simp [List.reverse_cons, List.prod_append, ih, toEuclideanLin, toLpLin_mul_same]

end Matrix
