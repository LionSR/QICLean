/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.Renyi.Defs
import QICLean.Analysis.RectangularTraceNormAlgebra

/-!
# Infimal smoothing of Rényi entropy

We take the infimum of the entropy over density matrices in a closed ball for
the full trace norm. A density matrix belongs to its own ball at every
nonnegative radius, and every strict upper bound on the infimum admits a
witness in the ball. In particular, any positive additive tolerance is allowed.

Source: Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 543–547. The source writes a minimum. The definition here
uses an infimum and does not assert attainment. Identifying the two values
requires a minimizer; at positive orders below one, compactness and continuity
provide the usual argument, while order zero requires lower semicontinuity
of rank. Those attainment results are not proved in this module. The witness
lemmas require neither attainment nor a common smoothing state for distinct
matrices.
-/

open scoped ComplexOrder
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entropy values of density matrices within full trace-norm distance `ε` of `ρ`.
Source: arXiv:0705.0292v2, `paper_v2.tex`, lines 543–545. -/
def smoothRenyiEntropyValues (ρ : Matrix ι ι ℂ) (α ε : ℝ) : Set ℝ :=
  {s | ∃ (σ : Matrix ι ι ℂ) (hσ : σ.PosSemidef),
    σ.trace = 1 ∧ rectangularTraceNorm (ρ - σ) ≤ ε ∧
      renyiEntropy σ hσ.isHermitian α = s}

/-- Infimal smoothed Rényi entropy in the full trace norm. The minimum notation
in arXiv:0705.0292v2, `paper_v2.tex`, lines 543–545, gives this value whenever a
minimum is attained. No attainment assertion is included in this definition. -/
noncomputable def smoothRenyiEntropy (ρ : Matrix ι ι ℂ) (α ε : ℝ) : ℝ :=
  sInf (smoothRenyiEntropyValues ρ α ε)

/-- A density matrix witnesses membership in its own nonnegative-radius ball. -/
theorem renyiEntropy_mem_smoothRenyiEntropyValues {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (α : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    renyiEntropy ρ hρ.isHermitian α ∈ smoothRenyiEntropyValues ρ α ε := by
  exact ⟨ρ, hρ, htr, by simpa using hε, rfl⟩

/-- Every strict upper bound on the infimal smoothed entropy admits a nearby
density matrix with smaller Rényi entropy. In particular, one may add any
positive tolerance to the infimum. No minimizer is assumed.
Source: the smoothing ball in arXiv:0705.0292v2, lines 543–547. -/
theorem exists_densityMatrix_renyiEntropy_lt {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (α : ℝ) {ε T : ℝ}
    (hε : 0 ≤ ε) (hT : smoothRenyiEntropy ρ α ε < T) :
    ∃ (σ : Matrix ι ι ℂ) (hσ : σ.PosSemidef),
      σ.trace = 1 ∧ rectangularTraceNorm (ρ - σ) ≤ ε ∧
        renyiEntropy σ hσ.isHermitian α < T := by
  obtain ⟨s, ⟨σ, hσ, htrσ, hclose, heq⟩, hs⟩ :=
    exists_lt_of_csInf_lt
      (Set.nonempty_of_mem (renyiEntropy_mem_smoothRenyiEntropyValues hρ htr α hε)) hT
  exact ⟨σ, hσ, htrσ, hclose, heq.trans_lt hs⟩
