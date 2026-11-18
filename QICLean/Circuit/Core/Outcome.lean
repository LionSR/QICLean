/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Channel

/-!
# Measurement, branch probabilities and readouts

The measurement of a basis (`KrausFamily.measure`) has the projections onto the basis vectors as
its Kraus operators, so its outcomes are the basis vectors. A branch `p` of a circuit has
probability `tr(Kₚ ρ Kₚᴴ)` on an input `ρ`.
The branches of a circuit are dependent tuples of outcomes whose shape depends on the circuit,
so what an algorithm reports is a *readout* `r : c.Index → Ω` of its branches, and the
probability of a reported value `ω` is the total probability of the branches read as `ω`.

## Main definitions

* `QuantumCircuit.Circuit.prob` — the probability of a branch.
* `QuantumCircuit.Circuit.outcomeProb` — the probability of a value of a readout.

## Main results

* `QuantumCircuit.Circuit.prob_vecMulVec` — on a pure input the probability of a branch is the
  squared norm of the output vector.
* `QuantumCircuit.Circuit.outcomeProb_of_bijective` — for a bijective readout whose values
  determine the probabilities of the branches, the probability of a value.
-/

open Matrix ManyBody

namespace QuantumCircuit

namespace Circuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]
  {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)]

/-- The probability `tr(Kₚ ρ Kₚᴴ)` of the branch `p` on the input `ρ`. For a state `ρ` and a
circuit with trace-preserving gates and onsite families these numbers are probabilities: they are
nonnegative and sum to `1` over the branches. -/
noncomputable def prob (ev : Interpretation G) (c : Circuit Γ G X Z)
    (ρ : Matrix (Config X) (Config X) ℂ) (p : c.Index) : ℝ :=
  (c.kraus ev p * ρ * (c.kraus ev p)ᴴ).trace.re

/-- The probability that the readout `r` of the branches takes the value `ω`: the total
probability `tr(Kₚ ρ Kₚᴴ)` of the branches `p` read as `ω`. For a state `ρ` and a circuit with
trace-preserving gates and onsite families these are the probabilities of the values. -/
noncomputable def outcomeProb (ev : Interpretation G) (c : Circuit Γ G X Z) {Ω : Type}
    [DecidableEq Ω] (r : c.Index → Ω) (ρ : Matrix (Config X) (Config X) ℂ) (ω : Ω) : ℝ :=
  ∑ p ∈ Finset.univ.filter (r · = ω), c.prob ev ρ p

/-- On a pure input `ψψᴴ` the probability of a branch is the squared norm of `Kₚ ψ`. -/
theorem prob_vecMulVec (ev : Interpretation G) (c : Circuit Γ G X Z) (ψ : Config X → ℂ)
    (p : c.Index) : c.prob ev (vecMulVec ψ (star ψ)) p = ∑ σ, ‖(c.kraus ev p *ᵥ ψ) σ‖ ^ 2 := by
  rw [prob, mul_vecMulVec, vecMulVec_mul, ← star_mulVec, trace_vecMulVec, dotProduct,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/-- For a bijective readout `r` and probabilities of the branches that depend only on the value
`f (r p)` of the readout, the value `ω` has probability `f ω`. -/
theorem outcomeProb_of_bijective (ev : Interpretation G) (c : Circuit Γ G X Z) {Ω : Type}
    [DecidableEq Ω] {r : c.Index → Ω} (hr : Function.Bijective r)
    {ρ : Matrix (Config X) (Config X) ℂ} {f : Ω → ℝ} (hf : ∀ p, c.prob ev ρ p = f (r p))
    (ω : Ω) : c.outcomeProb ev r ρ ω = f ω := by
  obtain ⟨p, rfl⟩ := hr.2 ω
  rw [outcomeProb, Finset.sum_eq_single p (fun q hq hqp ↦ absurd (hr.1 (Finset.mem_filter.mp hq).2)
    hqp) (fun hp ↦ absurd (by simp) hp), hf]

end Circuit

end QuantumCircuit
