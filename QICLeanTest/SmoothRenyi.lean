/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.Renyi.Smooth

open scoped ComplexOrder
open Matrix

-- The additive tolerance needed for the family argument requires no minimizer.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (α : ℝ) {ε S : ℝ}
    (hε : 0 ≤ ε) (hS : smoothRenyiEntropy ρ α ε ≤ S) :
    ∃ (σ : Matrix ι ι ℂ) (hσ : σ.PosSemidef),
      σ.trace = 1 ∧ rectangularTraceNorm (ρ - σ) ≤ ε ∧
        renyiEntropy σ hσ.isHermitian α < S + 1 :=
  exists_densityMatrix_renyiEntropy_lt hρ htr α hε (lt_of_le_of_lt hS (by linarith))

/-- info: 'renyiEntropy_mem_smoothRenyiEntropyValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms renyiEntropy_mem_smoothRenyiEntropyValues

/-- info: 'exists_densityMatrix_renyiEntropy_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_densityMatrix_renyiEntropy_lt
