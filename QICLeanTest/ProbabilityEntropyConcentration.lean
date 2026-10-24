/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProbabilityEntropyConcentration
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Empty-part and zero-tail tests for entropy concentration. -/

open Entropy

example {Z : Type*} [Fintype Z] [DecidableEq Z] (p : Z → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    probabilityEntropy p ≤ Real.log (Fintype.card Z) := by
  simpa [hsum] using probabilityEntropy_le_binary_partition p hp hsum ∅

example {Z : Type*} [Fintype Z] [DecidableEq Z] (p : Z → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    probabilityEntropy p ≤ Real.log (Fintype.card Z) := by
  simpa using probabilityEntropy_le_binary_partition p hp hsum Finset.univ

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Entropy.sum_negMulLog_le_mass_log_card,
      ``Entropy.probabilityEntropy_le_binary_partition,
      ``Entropy.probabilityEntropy_le_log_card_add_tail] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
