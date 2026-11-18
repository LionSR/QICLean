/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Algorithm.Qubit
import QICLean.Circuit.Core.Parallel

/-!
# The quantum Fourier transform

The Fourier transform on `n` qubits is the matrix `2^{-n/2} e^{2πi ⟨y⟩⟨x⟩ / 2^n}`
(Nielsen–Chuang, eq. (5.2)). Its circuit (Nielsen–Chuang, Fig. 5.1) uses one gate per cell of
a table `qftGate`: the Hadamard gate on a qubit, the controlled phase gate `R_{j-i+1}` on an
ordered pair `(j, i)` with `i < j`, control `j` and target `i`, and the swap on an ordered pair
`(a, b)` with `a < b`.

The gates of the Hadamard and controlled phase cells can be applied in any order in which every
controlled phase gate `(j, i)` comes after the Hadamard gate on its target `i` and before the
Hadamard gate on its control `j` (`IsGateOrder`). Along every such order, followed by the swaps
of the qubits `k` and `n - 1 - k`, the product of the placed gates is the Fourier transform
(`prod_gateOp_eq_dft`). The proof follows the column of a basis vector `x`: after the gates of a
prefix the column is a product state, the transformed qubits `i` carrying
`2^{-1/2} (|0⟩ + e^{2πi θᵢ} |1⟩)` and the others their input bit.

The circuit `qft n` applies the gates one per layer in the order of Nielsen–Chuang; the circuit
of `QFTParallel.lean` applies the same gates in linear depth.

## Main definitions

* `QuantumCircuit.Qubit.dft` — the Fourier matrix.
* `QuantumCircuit.Qubit.qftGate`, `QuantumCircuit.Qubit.gateOp` — the gate on a cell, and its
  placement on the register.
* `QuantumCircuit.Qubit.IsGateOrder` — the admissible orders of the gates.
* `QuantumCircuit.Qubit.qftCore`, `QuantumCircuit.Qubit.qft` — the circuit of Nielsen–Chuang,
  without and with the final swaps.

## Main results

* `QuantumCircuit.Qubit.prod_gateOp_eq_dft` — any admissible order computes the Fourier
  transform.
* `QuantumCircuit.Qubit.kraus_qft`, `QuantumCircuit.Qubit.kraus_qftCore` — the Kraus operators.
* `QuantumCircuit.Qubit.forall_isUnitary_qft`, `QuantumCircuit.Qubit.gateCount_qft`.
* `QuantumCircuit.Qubit.dft_mem_unitaryGroup` — the Fourier matrix is unitary.
-/

open Matrix ManyBody Complex

namespace QuantumCircuit

namespace Qubit

variable {n : ℕ}

/-- The matrix of the quantum Fourier transform, `2^{-n/2} e^{2πi ⟨y⟩⟨x⟩ / 2^n}`, in the binary
encoding with site `0` most significant (Nielsen–Chuang, eq. (5.2)). Mathlib's `ZMod.dft` has the
opposite sign in the exponent and no normalization. -/
noncomputable def dft (n : ℕ) : Matrix (Config (Q n)) (Config (Q n)) ℂ :=
  Matrix.of fun y x ↦ invSqrtTwo ^ n *
    exp (2 * Real.pi * I * ((encode n y : ℕ) * (encode n x : ℕ) : ℂ) / 2 ^ n)

/-! ### The gates -/

/-- The matrix of the Fourier transform on a cell: the Hadamard gate on a qubit; on an ordered
pair `(j, i)` with `i < j` the controlled phase gate `R_{j-i+1}`, control `j` and target `i`; on
an ordered pair `(a, b)` with `a < b` the swap. -/
noncomputable def qftMatrix : (b : (geometry n).Cell) →
    Matrix (RegionConfig (Q n) ((geometry n).cell b))
      (RegionConfig (Q n) ((geometry n).cell b)) ℂ
  | .inl a => hadamard.submatrix (siteEquiv (Q n) a) (siteEquiv (Q n) a)
  | .inr p => (if p.1.2 < p.1.1 then controlled (phaseShift ((p.1.1 : ℕ) - p.1.2 + 1))
      else swapMatrix 2).submatrix (pairEquiv (Q n) p.2) (pairEquiv (Q n) p.2)

/-- The gate of the Fourier transform on a cell. -/
noncomputable def qftGate (b : (geometry n).Cell) : KrausGate ((geometry n).cell b) (Q n) (Q n) :=
  KrausFamily.single (qftMatrix b)

/-- The gate on a cell, placed on the register. -/
noncomputable def gateOp (b : (geometry n).Cell) : Matrix (Config (Q n)) (Config (Q n)) ℂ :=
  place ((geometry n).cell b) (qftMatrix b)

theorem qftMatrix_mem_unitaryGroup (b : (geometry n).Cell) :
    qftMatrix b ∈ unitaryGroup (RegionConfig (Q n) ((geometry n).cell b)) ℂ := by
  rcases b with a | p
  · exact submatrix_equiv_mem_unitary.mpr hadamard_mem_unitaryGroup
  · refine submatrix_equiv_mem_unitary.mpr ?_
    split_ifs
    · exact controlled_mem_unitaryGroup (phaseShift_mem_unitaryGroup _)
    · exact swapMatrix_mem_unitaryGroup

theorem isUnitary_qftGate (b : (geometry n).Cell) : (qftGate b).IsUnitary :=
  KrausFamily.isUnitary_single (qftMatrix_mem_unitaryGroup b)

theorem gateOp_mem_unitaryGroup (b : (geometry n).Cell) :
    gateOp b ∈ unitaryGroup (Config (Q n)) ℂ :=
  place_mem_unitaryGroup (qftMatrix_mem_unitaryGroup b)

/-! ### Admissible orders -/

/-- The Hadamard and controlled phase cells: every qubit, and every ordered pair `(j, i)` with
`i < j`. -/
def coreCells (n : ℕ) : Finset (geometry n).Cell :=
  Finset.univ.disjSum (Finset.univ.filter fun p : {p : Fin n × Fin n // p.1 ≠ p.2} ↦ p.1.2 < p.1.1)

/-- The qubits `A` together with those whose Hadamard gate is in the list. -/
def hadamardsAfter (A : Finset (Fin n)) : List (geometry n).Cell → Finset (Fin n)
  | [] => A
  | .inl a :: L => hadamardsAfter (insert a A) L
  | .inr _ :: L => hadamardsAfter A L

/-- The gates of the list can be applied in this order when the qubits `A` are already
Hadamard-transformed: every Hadamard gate acts on a qubit not yet transformed, and every
controlled phase gate `(j, i)` has `i < j`, a transformed target `i` and a control `j` not yet
transformed. -/
def IsGateOrder : Finset (Fin n) → List (geometry n).Cell → Prop
  | _, [] => True
  | A, .inl a :: L => a ∉ A ∧ IsGateOrder (insert a A) L
  | A, .inr p :: L => p.1.2 < p.1.1 ∧ p.1.2 ∈ A ∧ p.1.1 ∉ A ∧ IsGateOrder A L

theorem hadamardsAfter_append (A : Finset (Fin n)) (L₁ L₂ : List (geometry n).Cell) :
    hadamardsAfter A (L₁ ++ L₂) = hadamardsAfter (hadamardsAfter A L₁) L₂ := by
  induction L₁ generalizing A with
  | nil => rfl
  | cons b L₁ ih => rcases b with a | p <;> exact ih _

theorem isGateOrder_append {A : Finset (Fin n)} {L₁ L₂ : List (geometry n).Cell} :
    IsGateOrder A (L₁ ++ L₂) ↔ IsGateOrder A L₁ ∧ IsGateOrder (hadamardsAfter A L₁) L₂ := by
  induction L₁ generalizing A with
  | nil => simp [IsGateOrder, hadamardsAfter]
  | cons b L₁ ih =>
    rcases b with a | p
    · simp only [List.cons_append, IsGateOrder, hadamardsAfter, ih, and_assoc]
    · simp only [List.cons_append, IsGateOrder, hadamardsAfter, ih, and_assoc]

/-- The swap cells `(k, n - 1 - k)` for `k < n / 2`. -/
def swapCells (n : ℕ) : List (geometry n).Cell :=
  List.ofFn fun k : Fin (n / 2) ↦ .inr ⟨(⟨k, by omega⟩, Fin.rev ⟨k, by omega⟩), fun h ↦ by
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega⟩

theorem swapCells_nodup : (swapCells n).Nodup := by
  refine List.nodup_ofFn.mpr fun k k' h ↦ ?_
  simp only [Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
  exact Fin.ext h.1

/-! ### The column of a basis vector -/

/-- Products of matrices along a list, the first on the right, applied to a vector. -/
private theorem reverse_prod_mulVec (L : List (geometry n).Cell) (v : Config (Q n) → ℂ) :
    (L.map gateOp).reverse.prod *ᵥ v = L.foldl (fun w b ↦ gateOp b *ᵥ w) v := by
  induction L generalizing v with
  | nil => simp
  | cons b L ih =>
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, ← mulVec_mulVec,
      ih, List.foldl_cons]

section Column

variable (x : Config (Q n))

/-- The column with the qubits of `A` transformed with phases `θ` and the others still the input
bits of `x`. -/
private noncomputable def phaseState (A : Finset (Fin n)) (θ : Fin n → ℂ) (y : Config (Q n)) :
    ℂ :=
  invSqrtTwo ^ A.card * (if ∀ k, k ∉ A → y k = x k then 1 else 0) *
    ∏ i ∈ A, exp (2 * Real.pi * I * ((y i : ℕ) : ℂ) * θ i)

private theorem phaseState_congr {A : Finset (Fin n)} {θ θ' : Fin n → ℂ}
    (h : ∀ i ∈ A, θ i = θ' i) : phaseState x A θ = phaseState x A θ' := by
  funext y
  simp only [phaseState]
  rw [Finset.prod_congr rfl fun i hi ↦ by rw [h i hi]]

private theorem phaseState_empty (θ : Fin n → ℂ) : phaseState x ∅ θ = Pi.single x 1 := by
  funext y
  simp only [phaseState, Finset.card_empty, pow_zero, one_mul, Finset.notMem_empty,
    not_false_eq_true, true_implies, Finset.prod_empty, mul_one, Pi.single_apply]
  exact if_congr funext_iff.symm rfl rfl

private theorem neg_one_pow_eq_exp (a b : ℕ) :
    ((-1 : ℂ) ^ (a * b)) = exp (2 * Real.pi * I * (a : ℂ) * ((b : ℂ) / 2)) := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem hadamard_phaseState {A : Finset (Fin n)} {θ : Fin n → ℂ} {a : Fin n}
    (ha : a ∉ A) :
    gateOp (.inl a) *ᵥ phaseState x A θ =
      phaseState x (insert a A) (Function.update θ a (((x a : ℕ) : ℂ) / 2)) := by
  funext y
  change (place {a} (hadamard.submatrix (siteEquiv (Q n) a) (siteEquiv (Q n) a)) *ᵥ _) y = _
  rw [place_siteEquiv_mulVec, Fintype.sum_eq_single (x a)]
  · have hprod : ∏ i ∈ A, exp (2 * Real.pi * I * ((Function.update y a (x a) i : ℕ) : ℂ) * θ i) =
        ∏ i ∈ A, exp (2 * Real.pi * I * ((y i : ℕ) : ℂ) * θ i) :=
      Finset.prod_congr rfl fun i hi ↦ by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
    have hind : (∀ k, k ∉ A → Function.update y a (x a) k = x k) ↔
        ∀ k, k ∉ insert a A → y k = x k := by
      constructor
      · intro h k hk
        rw [Finset.mem_insert, not_or] at hk
        rw [← h k hk.2, Function.update_of_ne hk.1]
      · intro h k hk
        by_cases hka : k = a
        · rw [hka, Function.update_self]
        · rw [Function.update_of_ne hka]; exact h k (by simp [hka, hk])
    have hprod' : ∏ i ∈ insert a A, exp (2 * Real.pi * I * ((y i : ℕ) : ℂ) *
        Function.update θ a (((x a : ℕ) : ℂ) / 2) i) =
        exp (2 * Real.pi * I * ((y a : ℕ) : ℂ) * (((x a : ℕ) : ℂ) / 2)) *
          ∏ i ∈ A, exp (2 * Real.pi * I * ((y i : ℕ) : ℂ) * θ i) := by
      rw [Finset.prod_insert ha, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun i hi ↦ by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
    rw [phaseState, phaseState, hprod, if_congr hind rfl rfl, hprod',
      Finset.card_insert_of_notMem ha,
      hadamard, of_apply, neg_one_pow_eq_exp, pow_succ]
    ring
  · intro b hb
    rw [phaseState, ite_eq_right_iff.mpr fun h ↦ absurd (by simpa using h a ha) hb, mul_zero,
      zero_mul, mul_zero]

private theorem rotation_phaseState {A : Finset (Fin n)} {θ : Fin n → ℂ}
    {p : {p : Fin n × Fin n // p.1 ≠ p.2}} (hp : p.1.2 < p.1.1) (hi : p.1.2 ∈ A)
    (hj : p.1.1 ∉ A) :
    gateOp (.inr p) *ᵥ phaseState x A θ =
      phaseState x A (Function.update θ p.1.2
        (θ p.1.2 + ((x p.1.1 : ℕ) : ℂ) / 2 ^ ((p.1.1 : ℕ) - p.1.2 + 1))) := by
  obtain ⟨⟨j, i⟩, h⟩ := p
  funext y
  change (place ({j} ∪ {i}) ((if i < j then controlled (phaseShift ((j : ℕ) - i + 1))
    else swapMatrix 2).submatrix (pairEquiv (Q n) h) (pairEquiv (Q n) h)) *ᵥ _) y = _
  rw [ite_eq_left hp, controlled_phaseShift, submatrix_diagonal_equiv, place_diagonal_mulVec]
  change exp (2 * Real.pi * I * (((y j : ℕ) : ℂ) * ((y i : ℕ) : ℂ)) / 2 ^ ((j : ℕ) - i + 1)) *
    _ = _
  by_cases hy : ∀ k, k ∉ A → y k = x k
  · simp only [phaseState, ite_eq_left hy, hy j hj]
    have hR : ∏ l ∈ A, exp (2 * Real.pi * I * ((y l : ℕ) : ℂ) *
        Function.update θ i (θ i + ((x j : ℕ) : ℂ) / 2 ^ ((j : ℕ) - i + 1)) l) =
        exp (2 * Real.pi * I * ((y i : ℕ) : ℂ) * (θ i + ((x j : ℕ) : ℂ) / 2 ^ ((j : ℕ) - i + 1))) *
          ∏ l ∈ A.erase i, exp (2 * Real.pi * I * ((y l : ℕ) : ℂ) * θ l) := by
      rw [← Finset.mul_prod_erase A _ hi, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun l hl ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    rw [hR, ← Finset.mul_prod_erase A _ hi, mul_add, Complex.exp_add]
    have : 2 * (Real.pi : ℂ) * I * (((x j : ℕ) : ℂ) * ((y i : ℕ) : ℂ)) / 2 ^ ((j : ℕ) - i + 1) =
        2 * Real.pi * I * ((y i : ℕ) : ℂ) * (((x j : ℕ) : ℂ) / 2 ^ ((j : ℕ) - i + 1)) := by ring
    rw [this]
    ring
  · simp only [phaseState, ite_eq_right hy]
    ring

/-- The phase that the gate on the cell `b` adds to the qubit `k`. -/
private noncomputable def phaseStep (b : (geometry n).Cell) (k : Fin n) : ℂ :=
  match b with
  | .inl a => if a = k then ((x a : ℕ) : ℂ) / 2 else 0
  | .inr p => if p.1.2 = k ∧ p.1.2 < p.1.1 then
      ((x p.1.1 : ℕ) : ℂ) / 2 ^ ((p.1.1 : ℕ) - p.1.2 + 1) else 0

private theorem foldl_phaseState :
    (L : List (geometry n).Cell) → (A : Finset (Fin n)) → (θ : Fin n → ℂ) → IsGateOrder A L →
      (∀ k, k ∉ A → θ k = 0) →
      L.foldl (fun w b ↦ gateOp b *ᵥ w) (phaseState x A θ) =
        phaseState x (hadamardsAfter A L) fun k ↦ θ k + (L.map (phaseStep x · k)).sum
  | [], A, θ, _, _ => by simp [hadamardsAfter]
  | .inl a :: L, A, θ, ⟨ha, hL⟩, hθ => by
    rw [List.foldl_cons, hadamard_phaseState x ha,
      phaseState_congr x (θ' := fun k ↦ θ k + phaseStep x (.inl a) k) fun k hk ↦ by
        by_cases hka : k = a
        · subst hka; simp [phaseStep, hθ k ha]
        · simp [phaseStep, Function.update_of_ne hka, Ne.symm hka],
      foldl_phaseState L _ _ hL fun k hk ↦ by
        rw [Finset.mem_insert, not_or] at hk
        simp [phaseStep, hθ k hk.2, Ne.symm hk.1]]
    congr 1
    funext k
    simp only [List.map_cons, List.sum_cons]
    ring
  | .inr p :: L, A, θ, ⟨hp, hi, hj, hL⟩, hθ => by
    rw [List.foldl_cons, rotation_phaseState x hp hi hj,
      phaseState_congr x (θ' := fun k ↦ θ k + phaseStep x (.inr p) k) fun k hk ↦ by
        by_cases hk' : k = p.1.2
        · subst hk'; simp [phaseStep, hp]
        · simp [phaseStep, Function.update_of_ne hk', Ne.symm hk'],
      foldl_phaseState L _ _ hL fun k hk ↦ by
        have hpk : p.1.2 ≠ k := fun e ↦ hk (e ▸ hi)
        simp [phaseStep, hθ k hk, hpk]]
    congr 1
    funext k
    simp only [List.map_cons, List.sum_cons]
    ring

/-- The phase `0.xᵢxᵢ₊₁⋯xₙ₋₁` acquired by the qubit `i`. -/
private noncomputable def phase (i : Fin n) : ℂ :=
  ∑ j ∈ Finset.univ.filter (i ≤ ·), ((x j : ℕ) : ℂ) / 2 ^ ((j : ℕ) - i + 1)

private theorem sum_phaseStep (k : Fin n) : ∑ b ∈ coreCells n, phaseStep x b k = phase x k := by
  rw [coreCells, Finset.sum_disjSum, phase,
    show Finset.univ.filter (k ≤ ·) = insert k (Finset.univ.filter (k < ·)) by
      ext j; simp [le_iff_eq_or_lt, eq_comm],
    Finset.sum_insert (by simp)]
  simp only [phaseStep, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Nat.sub_self, zero_add,
    pow_one]
  congr 1
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun p _ ↦ p.1.1)
    (fun j hj ↦ ⟨(j, k), (Finset.mem_filter.mp hj).2.ne'⟩) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨h₁, h₂, -⟩ := hp
    exact h₂ ▸ h₁
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [hj]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Subtype.ext (Prod.ext rfl hp.2.1.symm)
  · intro j hj
    rfl
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [hp.2.1]

private theorem encode_rev_cast (y : Config (Q n)) :
    ((encode n (fun i ↦ y (Fin.rev i)) : ℕ) : ℂ) = ∑ i : Fin n, ((y i : ℕ) : ℂ) * 2 ^ (i : ℕ) := by
  rw [encode_apply]
  push_cast
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k ↦ ?_
  simp only [Fin.revPerm_apply, Fin.val_rev]
  congr 2
  omega

private theorem pow_ratio (i j : Fin n) :
    (2 : ℂ) ^ (i : ℕ) * 2 ^ (n - 1 - (j : ℕ)) / 2 ^ n =
      if i ≤ j then 1 / 2 ^ ((j : ℕ) - i + 1) else 2 ^ ((i : ℕ) - j - 1) := by
  have hj := j.2
  split_ifs with h
  · rw [div_eq_div_iff (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero), one_mul,
      ← pow_add, ← pow_add]
    congr 1
    rw [Fin.le_def] at h
    omega
  · rw [div_eq_iff (pow_ne_zero _ two_ne_zero), ← pow_add, ← pow_add]
    congr 1
    rw [Fin.le_def] at h
    omega

/-- The exponent of the Fourier matrix differs from the phases of the column by an integer. -/
private theorem exponent_eq (y : Config (Q n)) :
    ((encode n (fun i ↦ y (Fin.rev i)) : ℕ) : ℂ) * ((encode n x : ℕ) : ℂ) / 2 ^ n =
      (∑ i : Fin n, ((y i : ℕ) : ℂ) * phase x i) +
        ((∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j ↦ ¬ i ≤ j),
          (y i : ℕ) * (x j : ℕ) * 2 ^ ((i : ℕ) - j - 1) : ℕ) : ℂ) := by
  rw [encode_rev_cast, encode_apply]
  push_cast
  rw [Finset.sum_mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_div, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ i ≤ j), phase,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    have h := (Finset.mem_filter.mp hj).2
    rw [show ((y i : ℕ) : ℂ) * 2 ^ (i : ℕ) * (((x j : ℕ) : ℂ) * 2 ^ (n - 1 - (j : ℕ))) / 2 ^ n =
      ((y i : ℕ) : ℂ) * ((x j : ℕ) : ℂ) * ((2 : ℂ) ^ (i : ℕ) * 2 ^ (n - 1 - (j : ℕ)) / 2 ^ n) by
        ring, pow_ratio, ite_eq_left h]
    ring
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    have h := (Finset.mem_filter.mp hj).2
    rw [show ((y i : ℕ) : ℂ) * 2 ^ (i : ℕ) * (((x j : ℕ) : ℂ) * 2 ^ (n - 1 - (j : ℕ))) / 2 ^ n =
      ((y i : ℕ) : ℂ) * ((x j : ℕ) : ℂ) * ((2 : ℂ) ^ (i : ℕ) * 2 ^ (n - 1 - (j : ℕ)) / 2 ^ n) by
        ring, pow_ratio, ite_eq_right h]

/-- The column with every qubit transformed is the column of the Fourier matrix, read with the
output bits in reverse order. -/
private theorem phaseState_univ (y : Config (Q n)) :
    phaseState x Finset.univ (phase x) y = dft n (fun i ↦ y (Fin.rev i)) x := by
  rw [phaseState, dft, of_apply, Finset.card_univ, Fintype.card_fin,
    ite_eq_left (fun k hk ↦ absurd (Finset.mem_univ k) hk), mul_one, ← Complex.exp_sum]
  congr 1
  rw [mul_div_assoc, exponent_eq, mul_add, Complex.exp_add,
    show 2 * (Real.pi : ℂ) * I * ((_ : ℕ) : ℂ) = ((_ : ℕ) : ℂ) * (2 * Real.pi * I) from
      mul_comm _ _,
    Complex.exp_nat_mul_two_pi_mul_I, mul_one, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ by ring)

/-- The swap on the cell `(a, b)` with `a < b` exchanges the two qubits. -/
private theorem swap_mulVec {p : {p : Fin n × Fin n // p.1 ≠ p.2}} (hp : ¬ p.1.2 < p.1.1)
    (ψ : Config (Q n) → ℂ) (y : Config (Q n)) :
    (gateOp (.inr p) *ᵥ ψ) y = ψ (fun v ↦ y (Equiv.swap p.1.1 p.1.2 v)) := by
  obtain ⟨⟨a, b⟩, h⟩ := p
  change (place ({a} ∪ {b}) ((if b < a then controlled (phaseShift ((a : ℕ) - b + 1))
    else swapMatrix 2).submatrix (pairEquiv (Q n) h) (pairEquiv (Q n) h)) *ᵥ ψ) y = _
  rw [ite_eq_right hp, place_mulVec_apply,
    Finset.sum_eq_single ((pairEquiv (Q n) h).symm (y b, y a))]
  · rw [submatrix_apply, Equiv.apply_symm_apply]
    have hc : (pairEquiv (Q n) h fun v ↦ y v) = (y a, y b) := rfl
    rw [hc, swapMatrix_apply, ite_eq_left ⟨rfl, rfl⟩, one_mul]
    congr 1
    funext v
    by_cases hva : v = a
    · subst hva
      rw [cutEquiv_symm_apply_mem _ _ (by simp), Equiv.swap_apply_left]
      exact pairEquiv_symm_apply_left (Q n) h _
    · by_cases hvb : v = b
      · subst hvb
        rw [cutEquiv_symm_apply_mem _ _ (by simp), Equiv.swap_apply_right]
        exact pairEquiv_symm_apply_right (Q n) h _
      · rw [cutEquiv_symm_apply_not_mem _ _ (by simp [hva, hvb]),
          Equiv.swap_apply_of_ne_of_ne hva hvb]
        rfl
  · intro a' _ ha'
    have hne : pairEquiv (Q n) h a' ≠ (y b, y a) :=
      fun e ↦ ha' (by rw [← e, Equiv.symm_apply_apply])
    rw [submatrix_apply]
    rcases hq : pairEquiv (Q n) h a' with ⟨c₁, c₂⟩
    rw [hq] at hne
    change swapMatrix 2 (y a, y b) (c₁, c₂) * _ = 0
    rw [swapMatrix_apply, ite_eq_right_iff.mpr fun hc ↦ absurd (Prod.ext hc.2.symm hc.1.symm) hne,
      zero_mul]
  · intro hm; exact absurd (Finset.mem_univ _) hm

/-- The configuration after the first `m` swaps: the sites `v` with `v < m` or `rev v < m` are
reversed, the others fixed. -/
private def swapped (m : ℕ) (v : Fin n) : Fin n :=
  if (v : ℕ) < m ∨ (Fin.rev v : ℕ) < m then Fin.rev v else v

private theorem foldl_swapCells (ψ : Config (Q n) → ℂ) :
    (swapCells n).foldl (fun w b ↦ gateOp b *ᵥ w) ψ = fun y ↦ ψ (fun v ↦ y (Fin.rev v)) := by
  have key : ∀ m ≤ n / 2, ((swapCells n).take m).foldl (fun w b ↦ gateOp b *ᵥ w) ψ =
      fun y ↦ ψ (fun v ↦ y (swapped m v)) := by
    intro m hm
    induction m with
    | zero => funext y; simp [swapped]
    | succ m ih =>
      have hget : (swapCells n)[m]? = some ((swapCells n)[m]'(by simp [swapCells]; omega)) :=
        List.getElem?_eq_getElem _
      rw [List.take_add_one, hget, Option.toList_some, List.foldl_append, ih (by omega),
        List.foldl_cons, List.foldl_nil]
      funext y
      simp only [swapCells, List.getElem_ofFn]
      rw [swap_mulVec (by simp only [Fin.lt_def, Fin.val_rev, not_lt]; omega)]
      congr 1
      funext v
      refine congrArg y ?_
      simp only [swapped, Equiv.swap_apply_def]
      split_ifs <;> simp only [Fin.ext_iff, Fin.val_rev] at * <;> omega
  rw [← List.take_of_length_le (le_of_eq (by simp [swapCells] : (swapCells n).length = n / 2)),
    key _ le_rfl]
  funext y
  congr 1
  funext v
  refine congrArg y ?_
  simp only [swapped]
  split_ifs with h
  · rfl
  · push Not at h
    ext
    simp only [Fin.val_rev] at h ⊢
    omega

end Column

private theorem hadamardsAfter_eq (A : Finset (Fin n)) (L : List (geometry n).Cell) :
    hadamardsAfter A L = A ∪ Finset.univ.filter fun a ↦ Sum.inl a ∈ L := by
  induction L generalizing A with
  | nil => simp [hadamardsAfter]
  | cons b L ih =>
    rcases b with a | p
    · rw [hadamardsAfter, ih]
      ext k
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
        true_and, List.mem_cons, Sum.inl.injEq]
      tauto
    · rw [hadamardsAfter, ih]
      ext k
      simp

/-- Along any admissible order of the Hadamard and controlled phase gates, the product of the
placed gates is the Fourier matrix read with the output bits in reverse order. -/
theorem prod_gateOp_core {L : List (geometry n).Cell} (hL : IsGateOrder ∅ L) (hnd : L.Nodup)
    (hcells : L.toFinset = coreCells n) (y x : Config (Q n)) :
    (L.map gateOp).reverse.prod y x = dft n (fun i ↦ y (Fin.rev i)) x := by
  have hA : hadamardsAfter ∅ L = Finset.univ := by
    rw [hadamardsAfter_eq]
    refine Finset.eq_univ_of_forall fun a ↦ ?_
    have : Sum.inl a ∈ L.toFinset := by rw [hcells]; simp [coreCells]
    simpa using List.mem_toFinset.mp this
  have hcol := reverse_prod_mulVec L (Pi.single x 1)
  rw [← phaseState_empty x 0, foldl_phaseState x L ∅ 0 hL fun _ _ ↦ rfl, hA] at hcol
  have hy := congrFun hcol y
  rw [phaseState_empty, mulVec_single_one, col_apply] at hy
  rw [hy, ← phaseState_univ x y]
  congr 1
  funext k
  rw [Pi.zero_apply, zero_add, ← List.sum_toFinset _ hnd, hcells, sum_phaseStep]

/-- Along any admissible order of the Hadamard and controlled phase gates, followed by the swaps,
the product of the placed gates is the Fourier matrix. -/
theorem prod_gateOp_eq_dft {L : List (geometry n).Cell} (hL : IsGateOrder ∅ L) (hnd : L.Nodup)
    (hcells : L.toFinset = coreCells n) :
    ((L ++ swapCells n).map gateOp).reverse.prod = dft n := by
  ext y x
  rw [← col_apply (((L ++ swapCells n).map gateOp).reverse.prod) x y, ← mulVec_single_one,
    reverse_prod_mulVec, List.foldl_append,
    ← reverse_prod_mulVec L, foldl_swapCells, mulVec_single_one]
  change (L.map gateOp).reverse.prod (fun v ↦ y v.rev) x = _
  rw [prod_gateOp_core hL hnd hcells]
  congr 2
  funext i
  rw [Fin.rev_rev]

/-! ### The circuit of Nielsen–Chuang -/

/-- The cells of the qubit `i` in the order of Nielsen–Chuang, Fig. 5.1: the Hadamard gate, then
the controlled phase gates with target `i` and control `j = i + 1, …, n - 1`. -/
def qubitCells (i : Fin n) : List (geometry n).Cell :=
  .inl i :: (List.finRange n).filterMap fun j ↦
    if h : i < j then some (.inr ⟨(j, i), h.ne'⟩) else none

/-- The Hadamard and controlled phase cells in the order of Nielsen–Chuang, Fig. 5.1. -/
def seqCells (n : ℕ) : List (geometry n).Cell :=
  (List.finRange n).flatMap qubitCells

/-- The layers of one gate each along a list of cells. -/
noncomputable def gateLayers (L : List (geometry n).Cell) :
    List (Layer (geometry n) KrausGate (Q n) (Q n)) :=
  L.map fun b ↦ Layer.single b (qftGate b)

/-- The Fourier transform with the output bits in reverse order. -/
noncomputable def qftCore (n : ℕ) : Circuit (geometry n) KrausGate (Q n) (Q n) :=
  Circuit.seq (gateLayers (seqCells n))

/-- The quantum Fourier transform of Nielsen–Chuang, Fig. 5.1. -/
noncomputable def qft (n : ℕ) : Circuit (geometry n) KrausGate (Q n) (Q n) :=
  Circuit.seq (gateLayers (seqCells n ++ swapCells n))

private theorem mem_qubitCells {i : Fin n} {b : (geometry n).Cell} :
    b ∈ qubitCells i ↔ b = .inl i ∨ ∃ p : {p : Fin n × Fin n // p.1 ≠ p.2},
      p.1.2 = i ∧ i < p.1.1 ∧ b = .inr p := by
  simp only [qubitCells, List.mem_cons, List.mem_filterMap, List.mem_finRange, true_and]
  refine or_congr_right ⟨fun ⟨j, hj⟩ ↦ ?_, fun ⟨p, hp, hlt, hb⟩ ↦ ?_⟩
  · by_cases h : i < j
    · rw [dite_eq_left_of_eq_true (eq_true h)] at hj
      exact ⟨_, rfl, h, (Option.some.inj hj).symm⟩
    · rw [dite_eq_right_of_eq_false (eq_false h)] at hj
      cases hj
  · refine ⟨p.1.1, ?_⟩
    rw [dite_eq_left_of_eq_true (eq_true hlt), hb]
    obtain ⟨⟨j, i'⟩, h⟩ := p
    obtain rfl : i' = i := hp
    rfl

private theorem isGateOrder_qubitCells (i : Fin n) :
    IsGateOrder (Finset.univ.filter fun k : Fin n ↦ k < i) (qubitCells i) ∧
      hadamardsAfter (Finset.univ.filter fun k : Fin n ↦ k < i) (qubitCells i) =
        Finset.univ.filter fun k : Fin n ↦ k ≤ i := by
  have key : ∀ (l : List (Fin n)) (A : Finset (Fin n)), i ∈ A → (∀ j ∈ l, i < j → j ∉ A) →
      IsGateOrder A (l.filterMap fun j ↦
          if h : i < j then some (Sum.inr ⟨(j, i), h.ne'⟩ : (geometry n).Cell) else none) ∧
        hadamardsAfter A (l.filterMap fun j ↦
          if h : i < j then some (Sum.inr ⟨(j, i), h.ne'⟩ : (geometry n).Cell) else none) = A := by
    intro l A hi hl
    induction l with
    | nil => exact ⟨trivial, rfl⟩
    | cons j l ih =>
      have ih' := ih fun j' hj' ↦ hl j' (List.mem_cons_of_mem _ hj')
      by_cases h : i < j
      · rw [List.filterMap_cons, dite_eq_left_of_eq_true (eq_true h)]
        exact ⟨⟨h, hi, hl j List.mem_cons_self h, ih'.1⟩, ih'.2⟩
      · rw [List.filterMap_cons, dite_eq_right_of_eq_false (eq_false h)]
        exact ih'
  have hins : insert i (Finset.univ.filter fun k : Fin n ↦ k < i) =
      Finset.univ.filter fun k : Fin n ↦ k ≤ i := by
    ext k; simp [le_iff_eq_or_lt]
  have h := key (List.finRange n) (insert i (Finset.univ.filter fun k : Fin n ↦ k < i))
    (Finset.mem_insert_self i _) fun j _ hj ↦ by simp [Fin.ne_of_gt hj, not_lt.mpr hj.le]
  rw [hins] at h
  refine ⟨⟨by simp, ?_⟩, ?_⟩
  · exact hins ▸ h.1
  · exact hins ▸ h.2

theorem isGateOrder_seqCells : IsGateOrder ∅ (seqCells n) := by
  have key : ∀ m ≤ n, IsGateOrder ∅ ((List.finRange n).take m |>.flatMap qubitCells) ∧
      hadamardsAfter ∅ ((List.finRange n).take m |>.flatMap qubitCells) =
        Finset.univ.filter fun k : Fin n ↦ (k : ℕ) < m := by
    intro m hm
    induction m with
    | zero => exact ⟨trivial, by simp [hadamardsAfter]⟩
    | succ m ih =>
      have hget : (List.finRange n)[m]? = some ⟨m, hm⟩ := by
        rw [List.getElem?_eq_getElem (by simpa using hm)]; simp
      obtain ⟨h₁, h₂⟩ := ih (by omega)
      have hA : (Finset.univ.filter fun k : Fin n ↦ (k : ℕ) < m) =
          Finset.univ.filter fun k : Fin n ↦ k < ⟨m, hm⟩ :=
        Finset.filter_congr fun _ _ ↦ Iff.rfl
      obtain ⟨h₃, h₄⟩ := isGateOrder_qubitCells (⟨m, hm⟩ : Fin n)
      rw [List.take_add_one, hget, Option.toList_some, List.flatMap_append, List.flatMap_singleton,
        isGateOrder_append, hadamardsAfter_append, h₂, hA]
      refine ⟨⟨h₁, h₃⟩, h₄.trans ?_⟩
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
      omega
  have h := (key n le_rfl).1
  rwa [List.take_of_length_le (List.length_finRange ▸ le_rfl)] at h

theorem seqCells_nodup : (seqCells n).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun i _ ↦ ?_, ?_⟩
  · refine List.nodup_cons.mpr ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp h
      split_ifs at hj
      cases hj
    · refine (List.nodup_finRange n).filterMap fun j j' b hj hj' ↦ ?_
      split_ifs at hj hj' <;> simp only [Option.mem_def, Option.some.injEq, reduceCtorEq] at hj hj'
      subst hj
      simp only [Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq] at hj'
      exact hj'.1.symm
  · refine (List.nodup_finRange n).pairwise_of_forall_ne fun i _ i' _ hii' ↦ ?_
    refine List.disjoint_left.mpr fun b hb hb' ↦ hii' ?_
    rcases mem_qubitCells.mp hb with rfl | ⟨p, hp, -, rfl⟩
    · rcases mem_qubitCells.mp hb' with h | ⟨p', -, -, h⟩
      · exact Sum.inl.inj h
      · cases h
    · rcases mem_qubitCells.mp hb' with h | ⟨p', hp', -, h⟩
      · cases h
      · rw [← hp, ← hp', Sum.inr.inj h]

theorem toFinset_seqCells : (seqCells n).toFinset = coreCells n := by
  ext b
  rw [List.mem_toFinset, seqCells, List.mem_flatMap]
  constructor
  · rintro ⟨i, -, hb⟩
    rcases mem_qubitCells.mp hb with rfl | ⟨p, hp, hlt, rfl⟩
    · simp [coreCells]
    · simp [coreCells, hp ▸ hlt]
  · intro hb
    rcases b with a | p
    · exact ⟨a, List.mem_finRange _, mem_qubitCells.mpr (Or.inl rfl)⟩
    · have : p.1.2 < p.1.1 := by simpa [coreCells] using hb
      exact ⟨p.1.2, List.mem_finRange _, mem_qubitCells.mpr (Or.inr ⟨p, rfl, this, rfl⟩)⟩

/-- The Fourier matrix is unitary. -/
theorem dft_mem_unitaryGroup (n : ℕ) : dft n ∈ unitaryGroup (Config (Q n)) ℂ := by
  rw [← prod_gateOp_eq_dft isGateOrder_seqCells seqCells_nodup toFinset_seqCells]
  refine Submonoid.list_prod_mem _ fun M hM ↦ ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hM)
  exact gateOp_mem_unitaryGroup b

private theorem length_qubitCells (i : Fin n) : (qubitCells i).length = n - i := by
  rw [qubitCells, List.length_cons, List.length_filterMap_eq_countP]
  have : ∀ j : Fin n, ((if h : i < j then
      some (Sum.inr ⟨(j, i), h.ne'⟩ : (geometry n).Cell) else none).isSome) = decide (i < j) :=
    fun j ↦ by split_ifs with h <;> simp [h]
  simp only [this]
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _), List.toFinset_filter,
    List.toFinset_finRange]
  simp only [decide_eq_true_eq]
  rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  omega

theorem length_seqCells : (seqCells n).length = n * (n + 1) / 2 := by
  rw [seqCells, List.length_flatMap, List.map_congr_left fun i _ ↦ length_qubitCells i]
  rw [← Fin.sum_univ_def, Fin.sum_univ_eq_sum_range (fun k ↦ n - k)]
  have h1 : ∑ k ∈ Finset.range n, (n - k) = ∑ k ∈ Finset.range n, (n - 1 - k + 1) :=
    Finset.sum_congr rfl fun k hk ↦ by rw [Finset.mem_range] at hk; omega
  rw [h1, Finset.sum_range_reflect (fun k ↦ k + 1) n, Finset.sum_add_distrib, Finset.sum_range_id,
    Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have : n * (n + 1) = n * (n - 1) + n * 2 := by
    cases n with
    | zero => rfl
    | succ m => simp only [Nat.add_sub_cancel]; ring
  rw [this, Nat.add_mul_div_right _ _ two_pos]

private theorem forall₂_gateLayers (L : List (geometry n).Cell) :
    List.Forall₂ (fun (M : Layer (geometry n) KrausGate (Q n) (Q n)) U ↦
      ∀ i, M.kraus KrausGate.ev i = U) (gateLayers L) (L.map gateOp) := by
  rw [gateLayers, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun b _ i ↦ Layer.kraus_single b (qftMatrix b) i

/-- Without the swaps, the Fourier transform reverses the order of the output bits. -/
theorem kraus_qftCore (n : ℕ) (p : (qftCore n).Index) (y x : Config (Q n)) :
    (qftCore n).kraus KrausGate.ev p y x = dft n (fun i ↦ y (Fin.rev i)) x := by
  rw [show (qftCore n).kraus KrausGate.ev p = _ from
      Circuit.kraus_seq KrausGate.ev (forall₂_gateLayers _) p,
    prod_gateOp_core isGateOrder_seqCells seqCells_nodup toFinset_seqCells]

/-- The single Kraus operator of the circuit `qft n` is the Fourier transform. -/
theorem kraus_qft (n : ℕ) (p : (qft n).Index) : (qft n).kraus KrausGate.ev p = dft n := by
  rw [show (qft n).kraus KrausGate.ev p = _ from
      Circuit.kraus_seq KrausGate.ev (forall₂_gateLayers _) p,
    prod_gateOp_eq_dft isGateOrder_seqCells seqCells_nodup toFinset_seqCells]

theorem isUnbranched_qft (n : ℕ) : (qft n).IsUnbranched :=
  Circuit.isUnbranched_seq _

private theorem forall_isUnitary_gateLayers (L : List (geometry n).Cell) :
    ∀ M ∈ gateLayers L, M.Forall KrausGate.ev KrausFamily.IsUnitary := by
  intro M hM
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hM
  exact Layer.forall_single _ (KrausFamily.isUnitary_single (one_mem _)) b _ (isUnitary_qftGate b)

theorem forall_isUnitary_qft (n : ℕ) : (qft n).Forall KrausGate.ev KrausFamily.IsUnitary :=
  Circuit.forall_seq _ _ (forall_isUnitary_gateLayers _)

private theorem gateCount_gateLayers (L : List (geometry n).Cell) :
    (Circuit.seq (gateLayers L)).gateCount = L.length := by
  rw [Circuit.gateCount_seq_eq_length]
  · simp [gateLayers]
  · intro M hM
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hM
    exact Layer.nonempty_index_single (hg := ⟨()⟩) b _
  · intro M hM
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hM
    rcases b with a | p <;> exact Layer.gateCount_single _ _

theorem gateCount_qftCore (n : ℕ) : (qftCore n).gateCount = n * (n + 1) / 2 := by
  rw [qftCore, gateCount_gateLayers, length_seqCells]

theorem gateCount_qft (n : ℕ) : (qft n).gateCount = n * (n + 1) / 2 + n / 2 := by
  rw [qft, gateCount_gateLayers, List.length_append, length_seqCells, swapCells, List.length_ofFn]

/-- The depth is at most the gate count, since every layer holds one gate. The circuit of
`QFTParallel.lean` applies the same gates in depth at most `2n`. -/
theorem depth_qft_le (n : ℕ) : (qft n).depth ≤ n * (n + 1) / 2 + n / 2 :=
  (Circuit.depth_le_gateCount _).trans (gateCount_qft n).le

end Qubit

end QuantumCircuit
