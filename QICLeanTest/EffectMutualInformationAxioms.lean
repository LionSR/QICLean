/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.EffectMutualInformation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom audit of the monotonicity of the binary relative entropy and of the bound
of the mutual information below by one effect operator. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``binaryRelativeEntropy_le_of_le_right,
    ``binaryRelativeEntropy_le_of_le_of_le,
    ``mulVec_eq_zero_of_kronecker_marginals_mulVec_eq_zero,
    ``binaryRelativeEntropy_le_mutualInformation]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
