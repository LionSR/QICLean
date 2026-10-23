/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProductOverlapReplacement
import QICLean.Analysis.OptimizedPureTraceError
import QICLean.Entropy.RightLocalLift
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Zero-target, small-product-error, and standard-axiom regressions for product replacement. -/

open scoped Matrix

-- A zero target still gives unit factors in both supports, without nontriviality assumptions.
example {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (C : Matrix α β ℂ) (hC : ‖WithLp.toLp 2 (fun ij : α × β ↦ C ij.1 ij.2)‖ = 1) :
    ∃ (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β),
      ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      u ∈ LinearMap.range (Matrix.toEuclideanLin C) ∧
      v ∈ LinearMap.range (Matrix.toEuclideanLin Cᵀ) := by
  obtain ⟨u, v, hu, hv, huC, hvC, _⟩ := Matrix.exists_unit_product_overlap_ge C hC 0 0
  exact ⟨u, v, hu, hv, huC, hvC⟩

-- Unequal block fidelities suffice for the repeated-factor amplification argument.
example {K : ℕ} (hK : 1 ≤ K) (f : Fin K → ℝ)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ} (hδ : δ < 1 / 8)
    (herr : Real.optimizedPureTraceError (∏ j, f j) ≤ δ) :
    ∃ i, Real.sqrt ((K : ℝ) / 4) * Real.optimizedPureTraceError (f i) ≤ δ := by
  obtain ⟨i, hi⟩ := Real.exists_optimizedPureTraceError_pow_le_prod hK f hf
  exact ⟨i, (Real.sqrt_mul_optimizedPureTraceError_le_pow_of_lt_one
    (hf i).1 (hf i).2 hK ((hi.trans herr).trans_lt (hδ.trans (by norm_num)))).trans
      (hi.trans herr)⟩

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``TensorProduct.exists_unit_product_overlap_ge_of_subspaces,
    ``Matrix.exists_unit_product_overlap_ge, ``Real.optimizedPureTraceError_antitoneOn,
    ``Real.exists_optimizedPureTraceError_pow_le_prod, ``Entropy.isSupportedOn_rightCut]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
