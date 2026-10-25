/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OverlapTriangle
import QICLean.Entropy.FilterPrefix
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the overlap lemmas of Landau, Vazirani and Vidick. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``norm_inner_ge_mul_sub_sqrt, ``one_sub_two_mul_add_le_norm_inner,
    ``Entropy.norm_inner_ge_of_gap]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

-- A numerical instance: overlaps at least 9/10 with a common vector give overlap at least 1/2.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {v v' w : E}
    (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) (hw : ‖w‖ = 1)
    (h : 1 - 1 / 10 ≤ ‖inner ℂ v w‖) (h' : 1 - 1 / 10 ≤ ‖inner ℂ v' w‖) :
    1 / 2 ≤ ‖inner ℂ v v'‖ := by
  have := one_sub_two_mul_add_le_norm_inner hv hv' hw (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h h'
  linarith
