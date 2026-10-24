/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OptimizedPureTraceError
import Mathlib.Tactic.NormNum.RealSqrt
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Endpoint, saturation, application, and standard-axiom checks for the scalar
optimized full trace-norm error. These tests assert no matrix optimization identity. -/

example : Real.optimizedPureTraceError 0 = 1 := by
  norm_num [Real.optimizedPureTraceError]

example : Real.optimizedPureTraceError (1 / 4) = 1 := by
  norm_num [Real.optimizedPureTraceError]

example : Real.optimizedPureTraceError (1 / 2) = 1 := by
  norm_num [Real.optimizedPureTraceError]

example : Real.optimizedPureTraceError 1 = 0 := by
  norm_num [Real.optimizedPureTraceError]

-- The source theorem also covers a saturated single-copy error when K = 2.
example : Real.sqrt ((2 : ℝ) / 8) * Real.optimizedPureTraceError (1 / 4) ≤
    Real.optimizedPureTraceError ((1 / 4) ^ (2 : ℕ)) :=
  Real.sqrt_mul_optimizedPureTraceError_le_pow_of_sq_le (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [Real.optimizedPureTraceError])

-- The intended small-product-error use requires no separate single-copy hypothesis.
example {f δ : ℝ} {K : ℕ} (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) (hK : 1 ≤ K)
    (hδ : δ < 1 / 8) (herr : Real.optimizedPureTraceError (f ^ K) ≤ δ) :
    Real.sqrt ((K : ℝ) / 4) * Real.optimizedPureTraceError f ≤ δ :=
  (Real.sqrt_mul_optimizedPureTraceError_le_pow_of_lt_one hf₀ hf₁ hK
    (herr.trans_lt (hδ.trans (by norm_num)))).trans herr

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Real.sqrt_mul_optimizedPureTraceError_le_pow_of_lt_one,
    ``Real.sqrt_mul_optimizedPureTraceError_le_pow_of_sq_le]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
