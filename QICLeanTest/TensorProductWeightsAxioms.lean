/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TensorProductWeights
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the weights of a vector of a tensor product. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``TensorProduct.innerSlice, ``TensorProduct.innerSlice_tmul,
    ``TensorProduct.sum_innerSlice_tmul, ``TensorProduct.norm_sq_sum_tmul,
    ``TensorProduct.innerSlice_mapL_one,
    ``Submodule.exists_weights_norm_sq_starProjection_tensorProd]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
