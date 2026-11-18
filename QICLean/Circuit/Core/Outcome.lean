/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Channel

/-!
# Measurement, branch probabilities and readouts

The measurement of a basis `α` is the Kraus family of the projections onto the basis vectors,
indexed by `α`. A branch `p` of a circuit has probability `tr(Kₚ ρ Kₚᴴ)` on an input `ρ`.
The branches of a circuit are dependent tuples of outcomes whose shape depends on the circuit,
so what an algorithm reports is a *readout* `r : c.Index → Ω` of its branches, and the
probability of a reported value `ω` is the total probability of the branches read as `ω`.

## Main definitions

* `KrausFamily.measure` — the measurement of a basis.
* `QuantumCircuit.Circuit.prob` — the probability of a branch.
* `QuantumCircuit.Circuit.outcomeProb` — the probability of a value of a readout.

## Main results

* `KrausFamily.isTP_measure` — a measurement is trace-preserving.
* `QuantumCircuit.Circuit.sum_prob` — for a circuit with trace-preserving local families the
  probabilities of the branches sum to the trace of the input.
* `QuantumCircuit.Circuit.sum_outcomeProb` — so do those of the values of a readout.
-/

open Matrix ManyBody

namespace KrausFamily

/-- The measurement of the basis `α`: the projections `|a⟩⟨a|`, indexed by `a : α`. -/
def measure (α : Type) [Fintype α] [DecidableEq α] : KrausFamily α α :=
  ⟨α, fun a ↦ Matrix.single a a 1⟩

theorem isTP_measure (α : Type) [Fintype α] [DecidableEq α] : (measure α).IsTP := by
  change ∑ a, (Matrix.single a a (1 : ℂ) : Matrix α α ℂ)ᴴ * Matrix.single a a (1 : ℂ) = 1
  ext x y
  simp [Matrix.single, mul_apply, Matrix.sum_apply, one_apply, ite_and, eq_comm]

end KrausFamily

namespace QuantumCircuit

namespace Circuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]
  {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)]

/-- The probability `tr(Kₚ ρ Kₚᴴ)` of the branch `p` on the input `ρ`. -/
noncomputable def prob (ev : Interpretation G) (c : Circuit Γ G X Z)
    (ρ : Matrix (Config X) (Config X) ℂ) (p : c.Index) : ℝ :=
  (c.kraus ev p * ρ * (c.kraus ev p)ᴴ).trace.re

/-- The probability that the readout `r` of the branches takes the value `ω`. -/
noncomputable def outcomeProb (ev : Interpretation G) (c : Circuit Γ G X Z) {Ω : Type}
    [DecidableEq Ω] (r : c.Index → Ω) (ρ : Matrix (Config X) (Config X) ℂ) (ω : Ω) : ℝ :=
  ∑ p ∈ Finset.univ.filter (r · = ω), c.prob ev ρ p

/-- For a circuit with trace-preserving local families the probabilities of the branches sum to
the trace of the input. -/
theorem sum_prob (ev : Interpretation G) (c : Circuit Γ G X Z)
    (h : c.Forall ev KrausFamily.IsTP) (ρ : Matrix (Config X) (Config X) ℂ) :
    ∑ p, c.prob ev ρ p = ρ.trace.re := by
  rw [← c.trace_map ev h ρ, map, KrausFamily.map_apply, trace_sum, Complex.re_sum]
  rfl

/-- For a circuit with trace-preserving local families the probabilities of the values of a
readout sum to the trace of the input. -/
theorem sum_outcomeProb (ev : Interpretation G) (c : Circuit Γ G X Z)
    (h : c.Forall ev KrausFamily.IsTP) {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (r : c.Index → Ω) (ρ : Matrix (Config X) (Config X) ℂ) :
    ∑ ω, c.outcomeProb ev r ρ ω = ρ.trace.re := by
  simp only [outcomeProb]
  rw [← c.sum_prob ev h ρ, Finset.sum_fiberwise]

end Circuit

end QuantumCircuit
