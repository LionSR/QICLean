/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.LocalGate
import QICLean.Circuit.Core.Seq

/-!
# Qubit registers and a gate set

A register of `n` qubits is the system with sites `Fin n` and basis `Fin 2` at every site. A
configuration `x` is encoded as the number `∑ᵢ xᵢ 2^(n-1-i)`: site `0` carries the most
significant bit, as in Nielsen–Chuang §5.1, where qubit `1` carries `j₁` in
`j = j₁ 2^(n-1) + ⋯ + jₙ`.

The gates are the Hadamard gate, the phase gates `R_k = diag(1, e^{2πi/2^k})`, their controlled
versions, and the swap, each a unitary matrix on `ℂ²` or on `ℂ² ⊗ ℂ²`, placed on a cell of the
geometry of sites and ordered pairs, where every cell has cost `1`. Cost `1` for one-qubit
gates makes the gate count the number of gates of Nielsen–Chuang, `n (n + 1) / 2` for the
Fourier transform without the final swaps.

## Main definitions

* `QuantumCircuit.Qubit.Q` — the register of `n` qubits.
* `QuantumCircuit.Qubit.encode` — the binary encoding `Config (Q n) ≃ Fin (2 ^ n)`.
* `QuantumCircuit.Qubit.hadamard`, `QuantumCircuit.Qubit.phaseShift`,
  `QuantumCircuit.Qubit.controlled`, `QuantumCircuit.Qubit.swap` — the matrices.
* `QuantumCircuit.Qubit.geometry` — cells on every qubit and every ordered pair, of cost `1`.
* `QuantumCircuit.Qubit.siteLayer`, `QuantumCircuit.Qubit.pairLayer` — a layer of one gate.

## Main results

* `QuantumCircuit.Qubit.encode_apply` — the value of the encoding.
* `QuantumCircuit.Qubit.hadamard_mem_unitaryGroup` and its analogues — the gates are unitary.
* `QuantumCircuit.Qubit.forall_isUnitary_siteLayer`,
  `QuantumCircuit.Qubit.forall_isUnitary_pairLayer` — layers of unitary gates are unitary.
-/

open Matrix ManyBody Complex

namespace QuantumCircuit

namespace Qubit

/-- The register of `n` qubits. -/
abbrev Q (n : ℕ) : Fin n → Type := fun _ ↦ Fin 2

/-- The binary encoding of a configuration, site `0` most significant. -/
def encode (n : ℕ) : Config (Q n) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))).trans finFunctionFinEquiv

theorem encode_apply {n : ℕ} (x : Config (Q n)) :
    (encode n x : ℕ) = ∑ i : Fin n, (x i : ℕ) * 2 ^ (n - 1 - (i : ℕ)) := by
  rw [encode, Equiv.trans_apply, finFunctionFinEquiv_apply]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i ↦ ?_
  simp [Equiv.arrowCongr_apply, Fin.val_rev]
  omega

/-! ### The matrices -/

/-- The Hadamard matrix `(√2)⁻¹ (-1)^{xy}`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun y x ↦ ((Real.sqrt 2 : ℂ))⁻¹ * (-1) ^ ((y : ℕ) * (x : ℕ))

/-- The phase gate `R_k = diag(1, e^{2πi/2^k})`. -/
noncomputable def phaseShift (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal fun b ↦ exp (2 * Real.pi * I * (b : ℕ) / 2 ^ k)

/-- The controlled gate `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U`, the control first. -/
def controlled {β : Type} [DecidableEq β] (U : Matrix β β ℂ) :
    Matrix (Fin 2 × β) (Fin 2 × β) ℂ :=
  Matrix.of fun y x ↦ if y.1 = x.1 then (if y.1 = 1 then U y.2 x.2 else (1 : Matrix β β ℂ) y.2 x.2)
    else 0

/-- The swap of two qubits. -/
def swap : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).submatrix id Prod.swap

theorem hadamard_mem_unitaryGroup : hadamard ∈ unitaryGroup (Fin 2) ℂ := by
  sorry

theorem phaseShift_mem_unitaryGroup (k : ℕ) : phaseShift k ∈ unitaryGroup (Fin 2) ℂ := by
  sorry

theorem controlled_mem_unitaryGroup {β : Type} [Fintype β] [DecidableEq β] {U : Matrix β β ℂ}
    (hU : U ∈ unitaryGroup β ℂ) : controlled U ∈ unitaryGroup (Fin 2 × β) ℂ := by
  sorry

theorem swap_mem_unitaryGroup : swap ∈ unitaryGroup (Fin 2 × Fin 2) ℂ :=
  submatrix_equiv_mem_unitary (e₁ := Equiv.refl _) (e₂ := Equiv.prodComm _ _) |>.mpr
    (one_mem _)

/-! ### Gates on a register -/

/-- Cells on every qubit and on every ordered pair of distinct qubits, all of cost `1`. -/
abbrev geometry (n : ℕ) : Geometry (Fin n) :=
  Geometry.sitesAndPairs (Fin n) 1 1

/-- The layer applying the one-qubit matrix `M` to the qubit `i`. -/
noncomputable def siteLayer {n : ℕ} (i : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Layer (geometry n) KrausGate (Q n) (Q n) :=
  Layer.single (Γ := geometry n) (.inl i) (KrausGate.ofMatrix (siteEquiv (Q n) i) M)

/-- The layer applying the two-qubit matrix `M` to the qubits `a` and `b`, in this order. -/
noncomputable def pairLayer {n : ℕ} {a b : Fin n} (h : a ≠ b)
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Layer (geometry n) KrausGate (Q n) (Q n) :=
  Layer.single (Γ := geometry n) (.inr ⟨(a, b), h⟩) (KrausGate.ofMatrix (pairEquiv (Q n) h) M)

theorem forall_isUnitary_siteLayer {n : ℕ} (i : Fin n) {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ unitaryGroup (Fin 2) ℂ) :
    (siteLayer i M).Forall KrausGate.ev KrausFamily.IsUnitary :=
  Layer.forall_single _ KrausFamily.isUnitary_single_one _ _
    (KrausGate.isUnitary_ofMatrix (siteEquiv (Q n) i) hM)

theorem forall_isUnitary_pairLayer {n : ℕ} {a b : Fin n} (h : a ≠ b)
    {M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hM : M ∈ unitaryGroup _ ℂ) :
    (pairLayer h M).Forall KrausGate.ev KrausFamily.IsUnitary :=
  Layer.forall_single _ KrausFamily.isUnitary_single_one _ _
    (KrausGate.isUnitary_ofMatrix (pairEquiv (Q n) h) hM)

/-- The single Kraus operator of a layer of one gate is its placement. -/
theorem kraus_siteLayer {n : ℕ} (i : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (p : (siteLayer i M).Index) :
    (siteLayer i M).kraus KrausGate.ev p = place {i} (M.submatrix (siteEquiv (Q n) i)
      (siteEquiv (Q n) i)) :=
  Layer.kraus_single (Γ := geometry n) (.inl i) _ p

theorem kraus_pairLayer {n : ℕ} {a b : Fin n} (h : a ≠ b)
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (p : (pairLayer h M).Index) :
    (pairLayer h M).kraus KrausGate.ev p = place ({a} ∪ {b}) (M.submatrix (pairEquiv (Q n) h)
      (pairEquiv (Q n) h)) :=
  Layer.kraus_single (Γ := geometry n) (.inr ⟨(a, b), h⟩) _ p

theorem nonempty_index_siteLayer {n : ℕ} (i : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Nonempty (siteLayer i M).Index :=
  sorry

theorem nonempty_index_pairLayer {n : ℕ} {a b : Fin n} (h : a ≠ b)
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Nonempty (pairLayer h M).Index :=
  sorry

end Qubit

end QuantumCircuit
