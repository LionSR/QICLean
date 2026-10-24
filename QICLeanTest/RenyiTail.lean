/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RenyiTail
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Boundary cases and standard-axiom audit for the Rényi spectral-tail bounds. -/

open scoped BigOperators ComplexOrder

-- The power form permits the zero family, although its logarithmic form does not.
example {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (0 : ℝ) ≤ ((1 - a) / 2) ^ ((1 - a) / a) := by
  simpa [Real.zero_rpow ha.ne'] using
    Entropy.ordered_tail_le_rpow (n := 3) (fun _ ↦ 0) (by simp)
      (fun _ _ _ ↦ le_rfl) (D := 2) (by decide) ha ha1

-- Rank zero and cutoff zero belong to the separate order-zero statement.
example :
    (∑ _i ∈ Finset.univ.filter (fun i : Fin 3 ↦ 0 ≤ i.val), (0 : ℝ)) = 0 := by
  exact Entropy.ordered_tail_eq_zero_of_card_support_le (fun _ : Fin 3 ↦ 0)
    (by simp) (fun _ _ _ ↦ le_rfl) (by simp)

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``Entropy.log_ordered_tail_le,
    ``Entropy.ordered_tail_le_rpow,
    ``Entropy.ordered_tail_eq_zero_of_card_support_le,
    ``Matrix.IsHermitian.trace_cfc_eq_sum_eigenvalues₀,
    ``Matrix.PosSemidef.log_eigenvalue_tail_le,
    ``Matrix.PosSemidef.eigenvalue_tail_le_rpow,
    ``Matrix.PosSemidef.eigenvalue_tail_eq_zero_of_rank_le]
  for decl in decls do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
