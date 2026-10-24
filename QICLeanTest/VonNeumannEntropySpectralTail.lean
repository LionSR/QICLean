/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.VonNeumannEntropySpectralTail
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Zero-rank-budget and above-dimension tests for the spectral entropy bound. -/

open scoped ComplexOrder
example {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) :
    vonNeumannEntropy ρ hρ.isHermitian ≤ Real.log (Fintype.card ι) + Real.log 2 := by
  have ht : ∑ i ∈ Finset.Ico 0 (Fintype.card ι), hρ.isHermitian.descEigenvalue i ≤ 1 := by
    rw [Nat.Ico_zero_eq_range, hρ.isHermitian.sum_descEigenvalue_card,
      posSemidef_trace_one_eigenvalues_sum_one hρ hρ1]
  simpa using hρ.vonNeumannEntropy_le_log_rank_add_tail hρ1 ht

example {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) {D : ℕ} (hD : Fintype.card ι ≤ D) :
    vonNeumannEntropy ρ hρ.isHermitian ≤ Real.log D + Real.log 2 := by
  have ht : ∑ i ∈ Finset.Ico D (Fintype.card ι), hρ.isHermitian.descEigenvalue i ≤ 0 := by
    simp [Finset.Ico_eq_empty_of_le hD]
  simpa using hρ.vonNeumannEntropy_le_log_rank_add_tail hρ1 ht

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.PosSemidef.vonNeumannEntropy_le_log_rank_add_tail,
      ``Matrix.PosSemidef.vonNeumannEntropy_le_log_rank_add_traceNorm] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
