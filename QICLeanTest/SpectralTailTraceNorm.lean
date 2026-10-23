/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralTailTraceNorm
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Boundary cases and an axiom audit for rank-constrained approximation. -/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder

-- The zero approximation is admissible even when the original matrix has trace one.
example {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosSemidef) :
    ∑ i ∈ Finset.Ico 0 n, hρ.isHermitian.descEigenvalue i ≤ traceNorm ρ := by
  simpa using hρ.sum_descEigenvalue_tail_le_traceNorm
    (σ := 0) isHermitian_zero (by simp : (0 : Matrix (Fin n) (Fin n) ℂ).rank ≤ 0)

-- Neither theorem needs a nonempty ambient space or an upper bound on the rank budget.
example (k : ℕ) {ρ σ : Matrix (Fin 0) (Fin 0) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.IsHermitian) :
    ∑ i ∈ Finset.Ico k 0, hρ.isHermitian.descEigenvalue i ≤ traceNorm (ρ - σ) / 2 := by
  apply hρ.sum_descEigenvalue_tail_le_half_traceNorm hσ
  · have : σ = 0 := Subsingleton.elim _ _
    simp [this]
  · simp [Matrix.trace]

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.PosSemidef.sum_descEigenvalue_tail_le_traceNorm,
    ``Matrix.PosSemidef.sum_descEigenvalue_tail_le_half_traceNorm,
    ``Matrix.IsHermitian.sum_descEigenvalue_tail_le_add_half_traceNorm]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
