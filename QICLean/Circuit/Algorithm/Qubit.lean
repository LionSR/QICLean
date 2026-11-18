/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.ComplexSqrt
import QICLean.Channel.MaximallyEntangled
import QICLean.Circuit.Core.LocalGate
import QICLean.Circuit.Gate.Controlled

/-!
# Qubit registers and a gate set

A register of `n` qubits is the system with sites `Fin n` and basis `Fin 2` at every site. A
configuration `x` is encoded as the number `∑ᵢ xᵢ 2^(n-1-i)`: site `0` carries the most
significant bit, as in Nielsen–Chuang §5.1, where qubit `1` carries `j₁` in
`j = j₁ 2^(n-1) + ⋯ + jₙ`.

The gates are the Hadamard gate, the phase gates `R_k = diag(1, e^{2πi/2^k})`, their controlled
versions and the swap `Matrix.swapMatrix 2`, each a unitary matrix on `ℂ²` or on `ℂ² ⊗ ℂ²`,
placed on a cell of the geometry of sites and ordered pairs, where every cell has cost `1`.
Cost `1` for one-qubit gates makes the gate count the number of gates of Nielsen–Chuang,
`n (n + 1) / 2` for the Fourier transform without the final swaps.

## Main definitions

* `QuantumCircuit.Qubit.Q` — the register of `n` qubits.
* `QuantumCircuit.Qubit.encode` — the binary encoding `Config (Q n) ≃ Fin (2 ^ n)`.
* `QuantumCircuit.Qubit.hadamard`, `QuantumCircuit.Qubit.phaseShift`,
  `QuantumCircuit.Qubit.controlled` — the matrices.
* `QuantumCircuit.Qubit.geometry` — cells on every qubit and every ordered pair, of cost `1`.

## Main results

* `QuantumCircuit.Qubit.encode_apply` — the value of the encoding.
* `QuantumCircuit.Qubit.hadamard_mem_unitaryGroup` and its analogues — the gates are unitary.
* `QuantumCircuit.Qubit.controlled_phaseShift` — the controlled phase gate is diagonal.
-/

open Matrix ManyBody Complex
open scoped Kronecker

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
  Matrix.of fun y x ↦ invSqrtTwo * (-1) ^ ((y : ℕ) * (x : ℕ))

/-- The phase gate `R_k = diag(1, e^{2πi/2^k})`. -/
noncomputable def phaseShift (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal fun b ↦ exp (2 * Real.pi * I * (b : ℕ) / 2 ^ k)

/-- The controlled gate `C(|1⟩⟨1| ⊗ 1, 1 ⊗ U) = |0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U`, the control first. -/
noncomputable def controlled {β : Type} [Fintype β] [DecidableEq β] (U : Matrix β β ℂ) :
    Matrix (Fin 2 × β) (Fin 2 × β) ℂ :=
  ctrlElem (diagonal (fun c : Fin 2 ↦ if c = 1 then (1 : ℂ) else 0) ⊗ₖ (1 : Matrix β β ℂ))
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U)

theorem controlled_apply {β : Type} [Fintype β] [DecidableEq β] (U : Matrix β β ℂ)
    (y x : Fin 2 × β) :
    controlled U y x =
      if y.1 = x.1 then (if y.1 = 1 then U y.2 x.2 else (1 : Matrix β β ℂ) y.2 x.2) else 0 := by
  obtain ⟨c, b⟩ := y
  obtain ⟨c', b'⟩ := x
  rw [controlled, ctrlElem, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  fin_cases c <;> fin_cases c' <;>
    simp [Matrix.add_apply, Matrix.sub_apply, kroneckerMap_apply, one_apply]

theorem hadamard_mem_unitaryGroup : hadamard ∈ unitaryGroup (Fin 2) ℂ := by
  have hc : star invSqrtTwo = invSqrtTwo := by simp [invSqrtTwo, Complex.conj_ofReal]
  rw [mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, mul_apply, Fin.sum_univ_two, star_eq_conjTranspose, hc] <;>
    linear_combination (2 : ℂ) * invSqrtTwo_mul_self

theorem phaseShift_mem_unitaryGroup (k : ℕ) : phaseShift k ∈ unitaryGroup (Fin 2) ℂ := by
  refine diagonal_mem_unitary.mpr ?_
  rw [Unitary.mem_iff_star_mul_self]
  funext b
  simp only [Pi.mul_apply, Pi.star_apply, Pi.one_apply, Complex.star_def, ← Complex.exp_conj,
    ← Complex.exp_add]
  rw [← Complex.exp_zero]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]
  ring

theorem controlled_mem_unitaryGroup {β : Type} [Fintype β] [DecidableEq β] {U : Matrix β β ℂ}
    (hU : U ∈ unitaryGroup β ℂ) : controlled U ∈ unitaryGroup (Fin 2 × β) ℂ := by
  have heq : controlled U = (blockDiagonal fun c : Fin 2 ↦ if c = 1 then U else 1).submatrix
      (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext ⟨c, y⟩ ⟨c', x⟩
    simp only [controlled_apply, submatrix_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      blockDiagonal_apply]
    split_ifs <;> simp_all
  rw [heq]
  refine submatrix_equiv_mem_unitary.mpr ?_
  rw [← unitaryGroup, mem_unitaryGroup_iff, star_eq_conjTranspose, blockDiagonal_conjTranspose,
    ← blockDiagonal_mul, ← blockDiagonal_one]
  congr 1
  funext c
  split_ifs
  · exact mem_unitaryGroup_iff.mp hU
  · simp

/-- The controlled phase gate is the diagonal matrix `e^{2πi c t / 2^k}`. -/
theorem controlled_phaseShift (k : ℕ) :
    controlled (phaseShift k) = diagonal fun p : Fin 2 × Fin 2 ↦
      exp (2 * Real.pi * I * ((p.1 : ℕ) * (p.2 : ℕ) : ℂ) / 2 ^ k) := by
  ext ⟨c, t⟩ ⟨c', t'⟩
  rw [controlled_apply]
  fin_cases c <;> fin_cases c' <;> fin_cases t <;> fin_cases t' <;>
    simp [phaseShift, one_apply]

/-! ### The geometry of a register -/

/-- Cells on every qubit and on every ordered pair of distinct qubits, all of cost `1`. -/
abbrev geometry (n : ℕ) : Geometry (Fin n) :=
  Geometry.sitesAndPairs (Fin n) 1 1

end Qubit

end QuantumCircuit
