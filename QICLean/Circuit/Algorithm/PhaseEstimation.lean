/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Algorithm.QFT
import QICLean.Circuit.Core.Oracle
import QICLean.Circuit.Core.Outcome
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Phase estimation

Phase estimation (Nielsen–Chuang, §5.2, Fig. 5.2 and 5.3) runs on a control register of `t`
qubits and a target of dimension `m`, with calls to an oracle `U` on the target controlled by
one qubit. Starting from `|0…0⟩ ⊗ |u⟩` for an eigenvector `U u = e^{2πiφ} u`, it applies the
Hadamard gate to every control qubit, then `U^{2^{t-1-j}}` controlled by the qubit `j` as
`2^{t-1-j}` controlled calls, then the inverse Fourier transform on the control register, and
measures the control register. The measured `t` bits, read as an integer `k`, give the estimate
`k / 2^t` of `φ`.

The circuit is one circuit for every oracle: its gates are plain gates and calls of the oracle
family `Oracle (Fin 2 × Fin m)`, and `U` enters only through the interpretation
`Oracle.ev (controlled U)`. The inverse Fourier transform is the adjoint of the circuit `qft t`
on its own sites `Fin t`, moved to the register `Fin t ⊕ Unit` along `Equiv.refl`, with the
target idle, and into the gate family of the circuit along the inclusion of plain gates. The
controlled calls are written on the register itself: a call on the pair cell of the qubit `j`
and the target identifies its configurations with `Fin 2 × Fin m` by `pairEquiv`, and no other
identification is needed, because the basis of each site of the register is `Fin 2` or `Fin m`
by definition.

## Main definitions

* `QuantumCircuit.PhaseEstimation.system` — the qubits of the control register and the target.
* `QuantumCircuit.PhaseEstimation.circuit` — the circuit of Nielsen–Chuang, Fig. 5.3, with the
  measurement of the control register.
* `QuantumCircuit.PhaseEstimation.readout` — the measured integer.

## Main results

* `QuantumCircuit.PhaseEstimation.queryCount_circuit` — the circuit calls the oracle
  `2^t - 1` times.
* `QuantumCircuit.PhaseEstimation.accurate_prob_ge` — with `t = n + ⌈log₂(2 + 1/(2ε))⌉` qubits
  the estimate is within `2^{-n}` of `φ`, modulo `1`, with probability at least `1 - ε`
  (Nielsen–Chuang, eq. (5.35)).
-/

open Matrix ManyBody Complex
open QuantumCircuit.Qubit (Q encode hadamard controlled dft gateLayers seqCells swapCells)

namespace QuantumCircuit

namespace PhaseEstimation

variable (t m : ℕ)

/-! ### The register -/

/-- The system of phase estimation on the sites `Fin t ⊕ Unit`: a qubit at each site of the
control register `Fin t`, and the basis `Fin m` at the target. It is the register of `t` qubits
extended by the target along `Equiv.refl`. -/
abbrev system : Fin t ⊕ Unit → Type :=
  extendSystem (Equiv.refl (Fin t ⊕ Unit)) (fun _ : Unit ↦ Fin m) (Q t)

/-- The geometry of the register: a cell on every site and on every ordered pair of distinct
sites, all of cost `1`. -/
abbrev geometry : Geometry (Fin t ⊕ Unit) :=
  Geometry.sitesAndPairs (Fin t ⊕ Unit) 1 1

/-- The gates of phase estimation: plain gates and calls of the oracle on a control qubit and
the target. -/
abbrev Gate : Finset (Fin t ⊕ Unit) → (Fin t ⊕ Unit → Type) → (Fin t ⊕ Unit → Type) → Type 1 :=
  GateSum KrausGate (Oracle (Fin 2 × Fin m))

/-- The cells of the register of `t` qubits as cells of the control register. -/
def geometryHom : (Qubit.geometry t).Hom (geometry t) (siteEmb (Equiv.refl (Fin t ⊕ Unit))) where
  cellMap :=
    ⟨fun
      | .inl a => .inl (.inl a)
      | .inr p => .inr ⟨(.inl p.1.1, .inl p.1.2), fun h ↦ p.2 (Sum.inl_injective h)⟩,
     by
      rintro (a | ⟨⟨a, b⟩, h⟩) (a' | ⟨⟨a', b'⟩, h'⟩) hab <;> simp_all⟩
  cell_cellMap := by
    rintro (a | ⟨⟨a, b⟩, h⟩) <;> simp <;> rfl

/-! ### The circuit -/

/-- The Hadamard gate on the control qubit `j`. -/
noncomputable def hadamardLayer (j : Fin t) :
    Layer (geometry t) (Gate t m) (system t m) (system t m) :=
  Layer.single (.inl (.inl j))
    (.inl (KrausGate.ofMatrix (siteEquiv (system t m) (.inl j)) hadamard))

/-- The call of the oracle controlled by the qubit `j`, on the pair cell of `j` and the
target. -/
noncomputable def queryLayer (j : Fin t) :
    Layer (geometry t) (Gate t m) (system t m) (system t m) :=
  Layer.single (.inr ⟨(.inl j, .inr ()), Sum.inl_ne_inr⟩)
    (.inr (Oracle.call (pairEquiv (system t m) Sum.inl_ne_inr)))

/-- The inverse Fourier transform on the control register: the adjoint of `qft t`, moved to the
register with the target idle, and into the gates of phase estimation. -/
noncomputable def qftInv : Circuit (geometry t) (Gate t m) (system t m) (system t m) :=
  ((Circuit.seqAdjoint (gateLayers (seqCells t ++ swapCells t))).mapSites
    (Equiv.refl (Fin t ⊕ Unit)) (fun _ : Unit ↦ Fin m) (geometryHom t)
    (KrausGate.transport _ _)).mapGate (Geometry.Hom.refl _) GateMorphism.inl

/-- The unitary part of phase estimation (Nielsen–Chuang, Fig. 5.2 followed by the inverse
Fourier transform): the Hadamard gates, the controlled calls `U^{2^{t-1-j}}` for
`j = t - 1, …, 0`, and the inverse Fourier transform. -/
noncomputable def unitary : Circuit (geometry t) (Gate t m) (system t m) (system t m) :=
  ((Circuit.seq ((List.finRange t).map (hadamardLayer t m))).comp
    (Circuit.seq ((List.finRange t).reverse.flatMap fun j : Fin t ↦
      List.replicate (2 ^ (t - 1 - (j : ℕ))) (queryLayer t m j)))).comp
    (qftInv t m)

/-- The measurement of the control register in the computational basis. -/
def measureLayer : Layer (geometry t) (Gate t m) (system t m) (system t m) where
  cells := ∅
  pairwiseDisjoint := by simp
  gate b := absurd b.2 (Finset.notMem_empty _)
  onsite
    | ⟨.inl _, _⟩ => KrausFamily.measure (Fin 2)
    | ⟨.inr _, _⟩ => KrausFamily.single 1

/-- Phase estimation (Nielsen–Chuang, Fig. 5.3): the unitary part, then the measurement of the
control register. -/
noncomputable def circuit : Circuit (geometry t) (Gate t m) (system t m) (system t m) :=
  (unitary t m).comp (.step (measureLayer t m) fun _ ↦ .done _)

/-- The measured integer of a branch: the outcomes of the measurement of the control register,
the qubit `0` most significant. -/
noncomputable def readout (p : (circuit t m).Index) : Fin (2 ^ t) :=
  encode t fun j ↦
    ((((unitary t m).compIndexEquiv _ p).2 : Σ _ : (measureLayer t m).Index, Unit).1.2
      ⟨.inl j, by simp [measureLayer]⟩ : Fin 2)

/-- The configuration of the control register. -/
def control (σ : Config (system t m)) : Config (Q t) :=
  fun j ↦ σ (.inl j)

/-- The input `|0…0⟩ ⊗ |u⟩`. -/
def input (u : Fin m → ℂ) : Config (system t m) → ℂ :=
  fun σ ↦ (if control t m σ = 0 then 1 else 0) * u (σ (.inr ()))

/-! ### The statements -/

/-- Phase estimation calls the oracle `∑_{j < t} 2^j = 2^t - 1` times. -/
theorem queryCount_circuit : (circuit t m).queryCount = 2 ^ t - 1 := by
  sorry

/-- Phase estimation with `t = n + ⌈log₂(2 + 1/(2ε))⌉` control qubits, on the input
`|0…0⟩ ⊗ |u⟩` for an eigenvector `U u = e^{2πiφ} u` of norm `1`, returns an integer `k` with
`k / 2^t` within `2^{-n}` of `φ` modulo `1` with probability at least `1 - ε`
(Nielsen–Chuang, §5.2.1, eq. (5.35)). -/
theorem accurate_prob_ge (U : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → ℂ) (hu : star u ⬝ᵥ u = 1)
    (φ : ℝ) (huφ : U *ᵥ u = exp (2 * Real.pi * I * φ) • u) (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (ht : t = n + ⌈Real.logb 2 (2 + 1 / (2 * ε))⌉₊) :
    1 - ε ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin (2 ^ t) ↦
        |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n),
      (circuit t m).outcomeProb (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U)))
        (readout t m) (vecMulVec (input t m u) (star (input t m u))) k := by
  sorry

end PhaseEstimation

end QuantumCircuit
