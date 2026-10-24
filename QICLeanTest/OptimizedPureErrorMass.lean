/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OptimizedPureErrorMass
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Endpoint and saturation tests for the missing-fidelity estimate. -/

example : 1 - (1 : ℝ) ≤ 0 / 2 := by
  apply Real.one_sub_le_half_error_of_optimizedPureTraceError_le (by norm_num)
    (by norm_num)
  norm_num [Real.optimizedPureTraceError]

example : Real.optimizedPureTraceError 0 = 1 ∧ ¬ (1 - (0 : ℝ) ≤ 1 / 2) := by
  norm_num [Real.optimizedPureTraceError]

run_cmd do
  let decl := ``Real.one_sub_le_half_error_of_optimizedPureTraceError_le
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
