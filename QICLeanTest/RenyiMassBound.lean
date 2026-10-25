/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.RenyiMassBound
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! The zero-error boundary and standard-axiom audit for the Rényi mass bound. -/

open scoped BigOperators

example {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (s : Finset ι) {D : ℕ} (hD : 0 < D) (hcard : s.card ≤ D)
    {α : ℝ} (hα : 1 < α) (hmass : 1 ≤ ∑ i ∈ s, p i) :
    Real.log (∑ i, p i ^ α) / (1 - α) ≤ Real.log D := by
  simpa using Entropy.renyi_mass_sub_error_le_log_card p hp s hD hcard hα
    (δ := 0) le_rfl zero_lt_one (by simpa using hmass)

run_cmd do
  for decl in #[``Entropy.log_card_bound_of_renyi_mass,
      ``Entropy.renyi_mass_sub_error_le_log_card] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
