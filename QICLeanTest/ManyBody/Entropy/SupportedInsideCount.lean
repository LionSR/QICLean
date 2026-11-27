/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Entropy.SupportedMarginalTails

/-! The matrix-unit count depends on the part of the designated support inside the cut. -/

open Entropy Matrix
open scoped Matrix.Norms.L2Operator

private def dims (v : Fin 2) : ℕ := if v = 0 then 2 else 3

example : Fintype.card (ManyBody.InnerConfig dims {0} Finset.univ) = 2 := by decide

example : supportDim dims Finset.univ = 6 := by decide

example : Fintype.card (ManyBody.InnerConfig dims ∅ Finset.univ) = 1 := by decide

example : Fintype.card (ManyBody.InnerConfig (fun _ : Fin 1 ↦ 0) Finset.univ Finset.univ) = 0 := by
  decide

example : Fintype.card (ManyBody.InnerConfig (fun _ : Fin 0 ↦ 0) ∅ ∅) = 1 := by decide

-- A two-site interaction with local dimensions 2 and 3 needs four terms across this cut,
-- instead of the coarse full-support bound of thirty-six.
example {X : Matrix (∀ v, Fin (dims v)) (∀ v, Fin (dims v)) ℂ}
    (hX : ManyBody.IsSupportedOn X Finset.univ) (σ₀ : (∀ v, Fin (dims v))) {J : ℝ} (hJ : ‖X‖ ≤ J) :
    Matrix.HasProductDecomposition (ManyBody.cutOperator {0} X) J 4 := by
  have hcount : Fintype.card (ManyBody.InnerConfig dims {0} Finset.univ) ^ 2 = 4 := by decide
  simpa only [hcount] using hX.hasProductDecomposition_inner (B := {0}) σ₀ hJ
