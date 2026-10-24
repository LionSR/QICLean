/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceExponentialPerturbation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the single-cluster bound of Hastings' cluster
expansion and the monotonicity of the trace of the exponential. -/

open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

-- Zero-dimensional partition functions vanish; the inverse convention keeps the bound valid.
example (β : ℝ) :
    ((NormedSpace.exp (-(β • (0 : Matrix (Fin 0) (Fin 0) ℂ)))).trace.re)⁻¹ *
      ‖((0 : Matrix (Fin 0) (Fin 0) ℂ) * NormedSpace.exp (-(β • 0))).trace‖ ≤ 0 := by
  simp

-- An empty perturbation set needs no nonnegative bound on the unused individual norms.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (O : Matrix ι ι ℂ) {β : ℝ} (hβ : 0 ≤ β) :
    ((NormedSpace.exp (-(β • H))).trace.re)⁻¹ *
      ‖(O * NormedSpace.exp (-(β • H))).trace‖ ≤ ‖O‖ := by
  simpa using Matrix.inv_mul_norm_trace_mul_exp_sub_sum_le hH
    (fun _ : Fin 0 ↦ (0 : Matrix ι ι ℂ)) ∅ (by simp) (J := -1) (by simp) O hβ

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``Matrix.IsHermitian.re_trace_exp_eq_sum,
    ``Matrix.IsHermitian.re_trace_exp_nonneg,
    ``Matrix.IsHermitian.re_trace_exp_le,
    ``Matrix.exp_add_smul_one,
    ``Matrix.IsHermitian.re_trace_exp_add_le,
    ``Matrix.norm_trace_mul_exp_sub_le,
    ``Matrix.inv_mul_norm_trace_mul_exp_sub_sum_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
