/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.PosSemidefCommute
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for scalar floors of commuting matrix products. -/

namespace Matrix

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``smul_one_le_mul_of_commute, ``pow_smul_one_le_list_prod] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

end Matrix
