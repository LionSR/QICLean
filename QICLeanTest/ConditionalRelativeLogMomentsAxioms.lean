/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.ConditionalRelativeLogMoments
import Lean.Util.CollectAxioms

/-! # Logical dependencies of conditional logarithmic moments -/

run_cmd do
  let env ← Lean.getEnv
  let declarations : Array Lean.Name := #[
    `Entropy.conditional_relative_log_moments,
    `Entropy.conditional_relative_log_mgf_le,
    `Entropy.conditional_schatten_log_le
  ]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in declarations do
    match env.find? decl with
    | some (.thmInfo _) => pure ()
    | some _ => throwError "The intended declaration is not a theorem: {decl}"
    | none => throwError "The intended theorem is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Nonstandard logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
