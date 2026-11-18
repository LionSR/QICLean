/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Algorithm.PhaseEstimation

/-!
# Semiclassical phase estimation

The inverse Fourier transform followed by a measurement can be replaced by measurements of the
qubits one at a time, each preceded by a phase correction chosen from the earlier outcomes
(Griffiths–Niu, *Semiclassical Fourier transform for quantum computation*, PRL 76 (1996) 3228;
Nielsen–Chuang, §5.2). After the preparation, the control qubit `j` carries
`(|0⟩ + e^{2πiφ 2^{t-1-j}} |1⟩)/√2`. The qubits are measured in the order `0, 1, …, t - 1`: the
qubit `j` gets the phase gate `diag(1, e^{-2πiθ})`, with `θ = ∑_{i < j} bᵢ / 2^{j-i+1}` from the
outcomes `bᵢ` of the qubits measured before it, then the Hadamard gate, and is measured. The
outcome of the qubit `j` is the bit of the estimate `k` at the site `t - 1 - j`.

This is a circuit with classical feedback: the layer measuring the qubit `j` depends on the
outcomes of the earlier layers. Its outcomes have the distribution of the coherent circuit, so
the success probability and the number of calls are those of phase estimation; the circuit has
no two-qubit gates after the calls.

## Main definitions

* `QuantumCircuit.PhaseEstimation.correction` — the phase correction from the earlier outcomes.
* `QuantumCircuit.PhaseEstimation.measureQubit` — the corrected measurement of one qubit.
* `QuantumCircuit.PhaseEstimation.semiclassical` — the circuit, with its readout
  `semiclassicalReadout`.

## Main results

* `QuantumCircuit.PhaseEstimation.semiclassical_outcomeProb_eq` — the outcome `k` has the
  probability `|αₖ|²` of the coherent circuit.
* `QuantumCircuit.PhaseEstimation.semiclassical_accurate_prob_ge` — the success probability.
* `QuantumCircuit.PhaseEstimation.queryCount_semiclassical` — the number of calls.
-/

open Matrix ManyBody Complex
open QuantumCircuit.Qubit (Q encode hadamard controlled)

namespace QuantumCircuit

namespace PhaseEstimation

variable (t m : ℕ)

/-- The phase correction `θ = ∑ₘ hₘ / 2^{m+2}` of the next qubit, from the outcomes `h` of the
qubits measured so far, the most recent first. -/
noncomputable def correction (h : List (Fin 2)) : ℝ :=
  (h.mapIdx fun i b ↦ ((b : ℕ) : ℝ) / 2 ^ (i + 2)).sum

/-- The measurement of a qubit after the phase gate `diag(1, e^{-2πiθ})` and the Hadamard gate:
the outcome `c` has the operator `|c⟩⟨c| H diag(1, e^{-2πiθ})`. -/
noncomputable def correctedMeasure (θ : ℝ) : KrausFamily (Fin 2) (Fin 2) :=
  ⟨Fin 2, fun c ↦ Matrix.single c c 1 * hadamard *
    diagonal fun x : Fin 2 ↦ exp (-(2 * Real.pi * I * θ * ((x : ℕ) : ℂ)))⟩

/-- The corrected measurement of the control qubit `j`. -/
noncomputable def measureQubit (j : Fin t) (θ : ℝ) :
    Layer (geometry t) (Gate t m) (system t m) (system t m) :=
  Layer.single (.inl (.inl j)) (.inl ⟨Fin 2, fun c ↦ ((correctedMeasure θ).op c).submatrix
    (siteEquiv (system t m) (.inl j)) (siteEquiv (system t m) (.inl j))⟩)

/-- The outcome of the corrected measurement of a qubit. -/
def qubitOutcome {j : Fin t} {θ : ℝ} (i : (measureQubit t m j θ).Index) : Fin 2 :=
  i.1 ⟨.inl (.inl j), Finset.mem_singleton_self _⟩

/-- The corrected measurements of the qubits of `l` in order, after the outcomes `h`, the most
recent first. -/
noncomputable def measureFrom :
    List (Fin t) → List (Fin 2) → Circuit (geometry t) (Gate t m) (system t m) (system t m)
  | [], _ => .done _
  | j :: l, h => .step (measureQubit t m j (correction h)) fun i ↦
      measureFrom l (qubitOutcome t m i :: h)

/-- The outcomes along a branch of `measureFrom l h`, the most recent first, after `h`. -/
noncomputable def outcomesFrom :
    (l : List (Fin t)) → (h : List (Fin 2)) → (measureFrom t m l h).Index → List (Fin 2)
  | [], h, _ => h
  | j :: l, h, p =>
    outcomesFrom l (qubitOutcome t m
      (p : Σ i : (measureQubit t m j (correction h)).Index,
        (measureFrom t m l (qubitOutcome t m i :: h)).Index).1 :: h) p.2

/-- Semiclassical phase estimation: the preparation, then the corrected measurements of the
qubits `0, 1, …, t - 1`. -/
noncomputable abbrev semiclassical : Circuit (geometry t) (Gate t m) (system t m) (system t m) :=
  (prepare t m).comp (measureFrom t m (List.finRange t) [])

/-- The measured integer: the outcome of the qubit `j` is the bit at the site `t - 1 - j`, so the
outcomes, the most recent first, are the bits from the site `0`. -/
noncomputable def semiclassicalReadout (p : (semiclassical t m).Index) : Fin (2 ^ t) :=
  encode t fun s ↦
    (outcomesFrom t m (List.finRange t) [] ((prepare t m).compIndexEquiv _ p).2).getD s 0

variable {t m}

/-- Semiclassical phase estimation has the outcome distribution of phase estimation: on the
input `|0…0⟩ ⊗ u` for an eigenvector `U u = e^{2πiφ} u` of norm `1`, the outcome `k` has the
probability `|αₖ|²` (Griffiths–Niu; Nielsen–Chuang, eq. (5.24)). -/
theorem semiclassical_outcomeProb_eq {U : Matrix (Fin m) (Fin m) ℂ} {u : Fin m → ℂ}
    (hu : star u ⬝ᵥ u = 1) {φ : ℝ} (huφ : U *ᵥ u = exp (2 * Real.pi * I * φ) • u)
    (k : Fin (2 ^ t)) :
    (semiclassical t m).outcomeProb (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U)))
      (semiclassicalReadout t m) (vecMulVec (input t m u) (star (input t m u))) k =
      ‖amplitude t φ k‖ ^ 2 := by
  sorry

/-- Semiclassical phase estimation with `t = n + ⌈log₂(2 + 1/(2ε))⌉` control qubits returns an
estimate within `2^{-n}` of `φ` modulo `1` with probability at least `1 - ε`. -/
theorem semiclassical_accurate_prob_ge (U : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → ℂ)
    (hu : star u ⬝ᵥ u = 1) (φ : ℝ) (huφ : U *ᵥ u = exp (2 * Real.pi * I * φ) • u) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) (ht : t = n + ⌈Real.logb 2 (2 + 1 / (2 * ε))⌉₊) :
    1 - ε ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin (2 ^ t) ↦
        |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n),
      (semiclassical t m).outcomeProb
        (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U)))
        (semiclassicalReadout t m) (vecMulVec (input t m u) (star (input t m u))) k := by
  simp only [semiclassical_outcomeProb_eq hu huφ]
  exact one_sub_le_sum_norm_sq_amplitude φ n hε ht

/-- Semiclassical phase estimation calls the oracle `2^t - 1` times. -/
theorem queryCount_semiclassical : (semiclassical t m).queryCount = 2 ^ t - 1 := by
  sorry

end PhaseEstimation

end QuantumCircuit
