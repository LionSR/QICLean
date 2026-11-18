/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Algorithm.Qubit

/-!
# The quantum Fourier transform

The quantum Fourier transform on `n` qubits is the matrix
`F(y, x) = (2^n)^{-1/2} ω^{⟨y⟩⟨x⟩}` with `ω = e^{2πi/2^n}`, where `⟨x⟩` is the binary encoding
with site `0` most significant (`Qubit.encode`). Nielsen–Chuang, §5.1 and Fig. 5.1, implement
it by applying, for each qubit `i` in turn, a Hadamard gate on `i` and then the controlled
phase gates `R_{j-i+1}` with control `j` and target `i` for every `j > i`; this leaves the bits
of the output in reverse order, and the swaps of the qubits `i` and `n - 1 - i` for
`i < n / 2` restore it.

`qftCore n` is the circuit without the swaps and `qft n` the circuit with them. Both are
unbranched sequences of single-gate layers of unitary gates.

## Main definitions

* `QuantumCircuit.Qubit.dft` — the matrix of the Fourier transform.
* `QuantumCircuit.Qubit.qftCore`, `QuantumCircuit.Qubit.qft` — the circuits.

## Main results

* `QuantumCircuit.Qubit.kraus_qft` — the single Kraus operator of `qft n` is `dft n`.
* `QuantumCircuit.Qubit.kraus_qftCore` — that of `qftCore n` is `dft n` with the output bits in
  reverse order.
* `QuantumCircuit.Qubit.gateCount_qftCore` — `n (n + 1) / 2` gates;
  `QuantumCircuit.Qubit.gateCount_qft` adds `n / 2` swaps.
* `QuantumCircuit.Qubit.forall_isUnitary_qft`, `QuantumCircuit.Qubit.isUnbranched_qft`.
-/

open Matrix ManyBody Complex

namespace QuantumCircuit

namespace Qubit

/-- The matrix of the quantum Fourier transform, `(2^n)^{-1/2} e^{2πi ⟨y⟩⟨x⟩ / 2^n}`, in the
binary encoding with site `0` most significant. Nielsen–Chuang, eq. (5.2). -/
noncomputable def dft (n : ℕ) : Matrix (Config (Q n)) (Config (Q n)) ℂ :=
  Matrix.of fun y x ↦ ((Real.sqrt (2 ^ n) : ℂ))⁻¹ *
    exp (2 * Real.pi * I * ((encode n y : ℕ) * (encode n x : ℕ) : ℂ) / 2 ^ n)

/-- The controlled phase gate `R_{j-i+1}` with control `j` and target `i`. -/
noncomputable def rotationLayer {n : ℕ} {j i : Fin n} (h : j ≠ i) :
    Layer (geometry n) KrausGate (Q n) (Q n) :=
  pairLayer h (controlled (phaseShift ((j : ℕ) - i + 1)))

/-- The layers for the qubit `i`: a Hadamard gate on `i`, then the controlled phase gates with
target `i` and control `j`, for `j = i + 1, …, n - 1`. -/
noncomputable def qubitLayers {n : ℕ} (i : Fin n) :
    List (Layer (geometry n) KrausGate (Q n) (Q n)) :=
  siteLayer i hadamard :: (List.finRange n).filterMap fun j ↦
    if h : i < j then some (rotationLayer h.ne') else none

/-- The layers of the Fourier transform without the final swaps (Nielsen–Chuang, Fig. 5.1). -/
noncomputable def coreLayers (n : ℕ) : List (Layer (geometry n) KrausGate (Q n) (Q n)) :=
  (List.finRange n).flatMap qubitLayers

theorem rev_ne_of_lt_half {n : ℕ} (k : Fin (n / 2)) :
    (⟨k, by omega⟩ : Fin n) ≠ Fin.rev ⟨k, by omega⟩ := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_rev] at this
  omega

/-- The swaps of the qubits `k` and `n - 1 - k` for `k < n / 2`. -/
noncomputable def swapLayers (n : ℕ) : List (Layer (geometry n) KrausGate (Q n) (Q n)) :=
  List.ofFn fun k : Fin (n / 2) ↦ pairLayer (rev_ne_of_lt_half k) swap

/-- The Fourier transform with the output bits in reverse order. -/
noncomputable def qftCore (n : ℕ) : Circuit (geometry n) KrausGate (Q n) (Q n) :=
  Circuit.seq (coreLayers n)

/-- The quantum Fourier transform. -/
noncomputable def qft (n : ℕ) : Circuit (geometry n) KrausGate (Q n) (Q n) :=
  Circuit.seq (coreLayers n ++ swapLayers n)

/-! ### Statements -/

/-- Without the swaps, the Fourier transform reverses the order of the output bits. -/
theorem kraus_qftCore (n : ℕ) (p : (qftCore n).Index) (y x : Config (Q n)) :
    (qftCore n).kraus KrausGate.ev p y x = dft n (fun i ↦ y (Fin.rev i)) x := by
  sorry

/-- The single Kraus operator of the circuit `qft n` is the Fourier transform. -/
theorem kraus_qft (n : ℕ) (p : (qft n).Index) : (qft n).kraus KrausGate.ev p = dft n := by
  sorry

theorem isUnbranched_qft (n : ℕ) : (qft n).IsUnbranched :=
  Circuit.isUnbranched_seq _

theorem forall_isUnitary_qft (n : ℕ) : (qft n).Forall KrausGate.ev KrausFamily.IsUnitary := by
  refine Circuit.forall_seq _ _ fun L hL ↦ ?_
  simp only [List.mem_append, coreLayers, qubitLayers, List.mem_flatMap, List.mem_cons,
    List.mem_filterMap, swapLayers, List.mem_ofFn] at hL
  obtain ⟨i, -, rfl | ⟨j, -, hj⟩⟩ | ⟨k, rfl⟩ := hL
  · exact forall_isUnitary_siteLayer i hadamard_mem_unitaryGroup
  · split_ifs at hj with h
    obtain rfl := Option.some.inj hj
    exact forall_isUnitary_pairLayer _
      (controlled_mem_unitaryGroup (phaseShift_mem_unitaryGroup _))
  · exact forall_isUnitary_pairLayer _ swap_mem_unitaryGroup

/-- The Fourier transform without the swaps uses `n (n + 1) / 2` gates: `n` Hadamard gates and
`n (n - 1) / 2` controlled phase gates. -/
theorem gateCount_qftCore (n : ℕ) : (qftCore n).gateCount = n * (n + 1) / 2 := by
  sorry

theorem gateCount_qft (n : ℕ) : (qft n).gateCount = n * (n + 1) / 2 + n / 2 := by
  sorry

/-- A depth bound. Every layer holds one gate, so the depth is the gate count; packing
commuting gates into layers gives depth `O(n)`, which is not attempted here. -/
theorem depth_qft_le (n : ℕ) : (qft n).depth ≤ n * (n + 1) / 2 + n / 2 :=
  (Circuit.depth_le_gateCount _).trans (gateCount_qft n).le

end Qubit

end QuantumCircuit
