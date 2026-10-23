/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RenyiRankLowerBound
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Zero-error cases and an axiom audit for the Rényi rank lower bound. -/

open Matrix

-- Exact approximation recovers the usual entropy bound by the logarithm of the rank.
example {n D : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) (hrank : ρ.rank ≤ D)
    {α : ℝ} (hα : 1 < α) : renyiEntropy ρ hρ.isHermitian α ≤ Real.log D := by
  simpa using hρ.renyiEntropy_add_log_error_le_log_rank hρ1 hρ.isHermitian hrank hα
    (δ := 0) (by norm_num) (by simp)

-- A one-dimensional density matrix is a pure state with rank budget one.
example {α : ℝ} (hα : 1 < α) :
    renyiEntropy (1 : Matrix (Fin 1) (Fin 1) ℂ) isHermitian_one α ≤ 0 := by
  have hρ : (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef := PosSemidef.one
  simpa using hρ.renyiEntropy_add_log_error_le_log_rank (by simp) isHermitian_one
      (D := 1) (by simp) hα (δ := 0) (by norm_num) (by simp)

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.PosSemidef.renyiEntropy_add_log_error_le_log_rank,
    ``Matrix.PosSemidef.renyiEntropy_add_log_error_le_log_rank_of_rectangularTraceNorm]
  for decl in decls do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
