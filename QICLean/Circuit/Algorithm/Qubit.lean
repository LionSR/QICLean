/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.ComplexSqrt
import QICLean.Channel.MaximallyEntangled
import QICLean.Channel.WeylTwirl
import QICLean.Circuit.Core.LocalGate
import QICLean.Circuit.Gate.Controlled

/-!
# Registers of qudits and a gate set

A register of `n` qudits of dimension `d` is the system with sites `Fin n` and basis `Fin d` at
every site; qubits are the case `d = 2`. A configuration `x` is encoded as the number
`∑ᵢ xᵢ d^(n-1-i)`: site `0` carries the most significant digit, as in Nielsen–Chuang §5.1, where
qubit `1` carries `j₁` in `j = j₁ 2^(n-1) + ⋯ + jₙ`.

The gates are the Fourier matrix `F_d(y, x) = d^{-1/2} e^{2πi xy/d}` of one qudit, the controlled
phase `e^{2πi c t/d^k}` of two qudits and the swap `Matrix.swapMatrix d`, each placed on a cell of
the geometry of sites and ordered pairs, where every cell has cost `1`. Cost `1` for one-qudit
gates makes the gate count the number of gates of Nielsen–Chuang, `n (n + 1) / 2` for the Fourier
transform without the final swaps.

For qubits, the Fourier matrix is the Hadamard gate `(−1)^{xy}/√2` and the controlled phase is the
controlled gate of the phase gate `R_k = diag(1, e^{2πi/2^k})`.

## Main definitions

* `QuantumCircuit.Qudit.encode` — the base-`d` encoding `Config (Qudits (Fin n) d) ≃ Fin (d ^ n)`.
* `QuantumCircuit.Qudit.fourier`, `QuantumCircuit.Qudit.controlledPhase` — the matrices.
* `QuantumCircuit.Qudit.geometry` — cells on every qudit and every ordered pair, of cost `1`.
* `QuantumCircuit.Qubit.encode`, `QuantumCircuit.Qubit.hadamard` — the case `d = 2`.
* `QuantumCircuit.Qubit.phaseShift`, `QuantumCircuit.Qubit.controlled` — the phase gate and the
  controlled gate of a matrix, on qubits.

## Main results

* `QuantumCircuit.Qudit.encode_apply` — the value of the encoding.
* `QuantumCircuit.Qudit.fourier_mem_unitaryGroup` and its analogues — the gates are unitary.
* `QuantumCircuit.Qubit.hadamard_apply` — the entries `(−1)^{xy}/√2` of the Hadamard gate.
* `QuantumCircuit.Qubit.controlled_phaseShift` — the controlled phase gate of qubits is the
  controlled phase of `Fin 2`.
-/

open Matrix ManyBody Complex
open scoped Kronecker

namespace QuantumCircuit

namespace Qudit

variable {d : ℕ}

/-- The base-`d` encoding of a configuration, site `0` most significant. -/
def encode (d n : ℕ) : Config (Qudits (Fin n) d) ≃ Fin (d ^ n) :=
  (Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin d))).trans finFunctionFinEquiv

theorem encode_apply {n : ℕ} (x : Config (Qudits (Fin n) d)) :
    (encode d n x : ℕ) = ∑ i : Fin n, (x i : ℕ) * d ^ (n - 1 - (i : ℕ)) := by
  rw [encode, Equiv.trans_apply, finFunctionFinEquiv_apply]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i ↦ ?_
  simp only [Equiv.arrowCongr_apply, Fin.revPerm_apply, Equiv.refl_apply, Function.comp_apply,
    Fin.val_rev]
  congr 2
  omega

/-! ### The matrices -/

/-- The Fourier matrix `F_d(y, x) = d^{-1/2} e^{2πi xy/d}` of one qudit. -/
noncomputable def fourier (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun y x ↦ invSqrt d * exp (2 * Real.pi * I * ((y : ℕ) * (x : ℕ) : ℂ) / d)

theorem fourier_apply (y x : Fin d) :
    fourier d y x = invSqrt d * exp (2 * Real.pi * I * ((y : ℕ) * (x : ℕ) : ℂ) / d) :=
  rfl

/-- The controlled phase `e^{2πi c t/d^k}` of two qudits, a diagonal matrix. -/
noncomputable def controlledPhase (d k : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  diagonal fun p ↦ exp (2 * Real.pi * I * ((p.1 : ℕ) * (p.2 : ℕ) : ℂ) / (d : ℂ) ^ k)

theorem fourier_mem_unitaryGroup (d : ℕ) : fourier d ∈ unitaryGroup (Fin d) ℂ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Subsingleton.elim (fourier 0) 1]
    exact one_mem _
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hd.ne'
  have hζ := Complex.isPrimitiveRoot_exp (k + 1) (Nat.succ_ne_zero k)
  have hexp (y x : Fin (k + 1)) : exp (2 * Real.pi * I * ((y : ℕ) * (x : ℕ) : ℂ) / (k + 1 : ℕ)) =
      exp (2 * Real.pi * I / (k + 1 : ℕ)) ^ ((x : ℕ) * (y : ℕ)) := by
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [mem_unitaryGroup_iff]
  ext i j
  have := Matrix.sum_rootOfUnity_pow_eq hζ (show ZMod (k + 1) from i) (show ZMod (k + 1) from j)
  simp only [mul_apply, star_apply, fourier_apply, hexp, star_mul', star_invSqrt] at this ⊢
  rw [one_apply]
  calc _ = invSqrt (k + 1 : ℕ) * invSqrt (k + 1 : ℕ) * ∑ b : ZMod (k + 1),
          exp (2 * Real.pi * I / (k + 1 : ℕ)) ^ (b.val * (show ZMod (k + 1) from i).val) *
            (starRingEnd ℂ) (exp (2 * Real.pi * I / (k + 1 : ℕ)) ^
              (b.val * (show ZMod (k + 1) from j).val)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [show ZMod.val (show ZMod (k + 1) from b) = b from rfl,
          show ZMod.val (show ZMod (k + 1) from i) = i from rfl,
          show ZMod.val (show ZMod (k + 1) from j) = j from rfl, Complex.star_def]
        ring
    _ = if i = j then 1 else 0 := by
        rw [this, invSqrt_mul_self (Nat.cast_nonneg _)]
        split_ifs with h₁ h₂ h₃
        · exact inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero k)
        · exact absurd h₁ h₂
        · exact absurd h₃ h₁
        · exact mul_zero _

theorem controlledPhase_mem_unitaryGroup (d k : ℕ) :
    controlledPhase d k ∈ unitaryGroup (Fin d × Fin d) ℂ := by
  refine diagonal_mem_unitary.mpr ?_
  rw [Unitary.mem_iff_star_mul_self]
  funext p
  simp only [Pi.mul_apply, Pi.star_apply, Pi.one_apply, Complex.star_def, ← Complex.exp_conj,
    ← Complex.exp_add]
  rw [← Complex.exp_zero]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]
  ring

/-! ### The geometry of a register -/

/-- Cells on every qudit and on every ordered pair of distinct qudits, all of cost `1`. -/
abbrev geometry (n : ℕ) : Geometry (Fin n) :=
  Geometry.sitesAndPairs (Fin n) 1 1

end Qudit

/-! ### Qubits -/

namespace Qubit

export Qudit (geometry)

/-- The binary encoding of a configuration, site `0` most significant. -/
abbrev encode (n : ℕ) : Config (Qudits (Fin n) 2) ≃ Fin (2 ^ n) :=
  Qudit.encode 2 n

/-- The Hadamard gate, the Fourier matrix of a qubit. -/
noncomputable abbrev hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  Qudit.fourier 2

/-- The entries `(−1)^{xy}/√2` of the Hadamard gate. -/
theorem hadamard_apply (y x : Fin 2) :
    hadamard y x = invSqrtTwo * (-1) ^ ((y : ℕ) * (x : ℕ)) := by
  change Qudit.fourier 2 y x = _
  rw [Qudit.fourier_apply, Nat.cast_ofNat, invSqrt_two, ← Complex.exp_pi_mul_I,
    ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem hadamard_mem_unitaryGroup : hadamard ∈ unitaryGroup (Fin 2) ℂ :=
  Qudit.fourier_mem_unitaryGroup 2

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

/-- The controlled phase gate of qubits is the controlled phase `e^{2πi c t / 2^k}`. -/
theorem controlled_phaseShift (k : ℕ) : controlled (phaseShift k) = Qudit.controlledPhase 2 k := by
  ext ⟨c, t⟩ ⟨c', t'⟩
  rw [controlled_apply]
  fin_cases c <;> fin_cases c' <;> fin_cases t <;> fin_cases t' <;>
    simp [phaseShift, Qudit.controlledPhase, one_apply]

end Qubit

end QuantumCircuit
