/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Algorithm.Qubit
import QICLean.Circuit.Core.Parallel

/-!
# The quantum Fourier transform

The Fourier transform on `n` qudits of dimension `d` is the matrix
`d^{-n/2} e^{2πi ⟨y⟩⟨x⟩ / d^n}`, with `⟨x⟩` the base-`d` encoding (Nielsen–Chuang, eq. (5.2) for
`d = 2`). Its circuit (Nielsen–Chuang, Fig. 5.1) uses one gate per cell of a table `qftGate`: the
Fourier matrix `F_d` on a qudit, the controlled phase `e^{2πi c t/d^{j-i+1}}` on an ordered pair
`(j, i)` with `i < j`, control `j` and target `i`, and the swap on an ordered pair `(a, b)` with
`a < b`. For qubits these are the Hadamard gate and the controlled phase gate `R_{j-i+1}`.

The gates of the Fourier and controlled phase cells can be applied in any order in which every
controlled phase `(j, i)` comes after the Fourier gate on its target `i` and before the Fourier
gate on its control `j` (`IsGateOrder`). Along every such order, followed by the swaps of the
qudits `k` and `n - 1 - k`, the product of the placed gates is the Fourier transform
(`prod_gateOp_eq_dft`). The proof follows the column of a basis vector `x`: after the gates of a
prefix the column is a product state, the transformed qudits `i` carrying
`d^{-1/2} ∑_c e^{2πi c θᵢ} |c⟩` and the others their input digit.

The circuit `qft d n` applies the gates one per layer in the order of Nielsen–Chuang; the circuit
of `QFTParallel.lean` applies the same gates in linear depth. The qubit circuit is the case
`d = 2`, under the names of the namespace `QuantumCircuit.Qubit`.

## Main definitions

* `QuantumCircuit.Qudit.dft` — the Fourier matrix.
* `QuantumCircuit.Qudit.qftGate`, `QuantumCircuit.Qudit.gateOp` — the gate on a cell, and its
  placement on the register.
* `QuantumCircuit.Qudit.IsGateOrder` — the admissible orders of the gates.
* `QuantumCircuit.Qudit.qftCore`, `QuantumCircuit.Qudit.qft` — the circuit of Nielsen–Chuang,
  without and with the final swaps.
* `QuantumCircuit.Qubit.dft`, `QuantumCircuit.Qubit.qft` — the case `d = 2`.

## Main results

* `QuantumCircuit.Qudit.prod_gateOp_eq_dft` — any admissible order computes the Fourier
  transform.
* `QuantumCircuit.Qudit.kraus_qft`, `QuantumCircuit.Qudit.kraus_qftCore` — the Kraus operators.
* `QuantumCircuit.Qudit.forall_isUnitary_qft`, `QuantumCircuit.Qudit.gateCount_qft`.
* `QuantumCircuit.Qudit.dft_mem_unitaryGroup` — the Fourier matrix is unitary.
* `QuantumCircuit.Qubit.kraus_qft`, `QuantumCircuit.Qubit.gateCount_qft`,
  `QuantumCircuit.Qubit.depth_qft_le` — the case `d = 2`.
-/

open Matrix ManyBody Complex

namespace QuantumCircuit

namespace Qudit

variable {d n : ℕ}

/-- The matrix of the quantum Fourier transform, `d^{-n/2} e^{2πi ⟨y⟩⟨x⟩ / d^n}`, in the base-`d`
encoding with site `0` most significant (Nielsen–Chuang, eq. (5.2) for `d = 2`). Mathlib's
`ZMod.dft` has the opposite sign in the exponent and no normalization. -/
noncomputable def dft (d n : ℕ) :
    Matrix (Config (Qudits (Fin n) d)) (Config (Qudits (Fin n) d)) ℂ :=
  Matrix.of fun y x ↦ invSqrt d ^ n *
    exp (2 * Real.pi * I * ((encode d n y : ℕ) * (encode d n x : ℕ) : ℂ) / (d : ℂ) ^ n)

/-! ### The gates -/

/-- The matrix of the Fourier transform on a cell: the Fourier matrix on a qudit; on an ordered
pair `(j, i)` with `i < j` the controlled phase `e^{2πi c t/d^{j-i+1}}`, control `j` and target
`i`; on
an ordered pair `(a, b)` with `a < b` the swap. -/
noncomputable def qftMatrix (d : ℕ) : (b : (geometry n).Cell) →
    Matrix (RegionConfig (Qudits (Fin n) d) ((geometry n).cell b))
      (RegionConfig (Qudits (Fin n) d) ((geometry n).cell b)) ℂ
  | .inl a => (fourier d).submatrix (siteEquiv (Qudits (Fin n) d) a)
      (siteEquiv (Qudits (Fin n) d) a)
  | .inr p => (if p.1.2 < p.1.1 then controlledPhase d ((p.1.1 : ℕ) - p.1.2 + 1)
      else swapMatrix d).submatrix (pairEquiv (Qudits (Fin n) d) p.2)
        (pairEquiv (Qudits (Fin n) d) p.2)

/-- The gate of the Fourier transform on a cell. -/
noncomputable def qftGate (d : ℕ) (b : (geometry n).Cell) :
    KrausGate ((geometry n).cell b) (Qudits (Fin n) d) (Qudits (Fin n) d) :=
  KrausFamily.single (qftMatrix d b)

/-- The gate on a cell, placed on the register. -/
noncomputable def gateOp (d : ℕ) (b : (geometry n).Cell) :
    Matrix (Config (Qudits (Fin n) d)) (Config (Qudits (Fin n) d)) ℂ :=
  place ((geometry n).cell b) (qftMatrix d b)

theorem qftMatrix_mem_unitaryGroup (b : (geometry n).Cell) :
    qftMatrix d b ∈ unitaryGroup (RegionConfig (Qudits (Fin n) d) ((geometry n).cell b)) ℂ := by
  rcases b with a | p
  · exact submatrix_equiv_mem_unitary.mpr (fourier_mem_unitaryGroup d)
  · refine submatrix_equiv_mem_unitary.mpr ?_
    split_ifs
    · exact controlledPhase_mem_unitaryGroup d _
    · exact swapMatrix_mem_unitaryGroup

theorem isUnitary_qftGate (b : (geometry n).Cell) : (qftGate d b).IsUnitary :=
  KrausFamily.isUnitary_single (qftMatrix_mem_unitaryGroup b)

theorem gateOp_mem_unitaryGroup (b : (geometry n).Cell) :
    gateOp d b ∈ unitaryGroup (Config (Qudits (Fin n) d)) ℂ :=
  place_mem_unitaryGroup (qftMatrix_mem_unitaryGroup b)

/-! ### Admissible orders -/

/-- The Fourier and controlled phase cells: every qudit, and every ordered pair `(j, i)` with
`i < j`. -/
def coreCells (n : ℕ) : Finset (geometry n).Cell :=
  Finset.univ.disjSum (Finset.univ.filter fun p : {p : Fin n × Fin n // p.1 ≠ p.2} ↦ p.1.2 < p.1.1)

/-- The qudits `A` together with those whose Fourier gate is in the list. -/
def fourierAfter (A : Finset (Fin n)) : List (geometry n).Cell → Finset (Fin n)
  | [] => A
  | .inl a :: L => fourierAfter (insert a A) L
  | .inr _ :: L => fourierAfter A L

/-- The gates of the list can be applied in this order when the qudits `A` are already
transformed: every Fourier gate acts on a qudit not yet transformed, and every
controlled phase gate `(j, i)` has `i < j`, a transformed target `i` and a control `j` not yet
transformed. -/
def IsGateOrder : Finset (Fin n) → List (geometry n).Cell → Prop
  | _, [] => True
  | A, .inl a :: L => a ∉ A ∧ IsGateOrder (insert a A) L
  | A, .inr p :: L => p.1.2 < p.1.1 ∧ p.1.2 ∈ A ∧ p.1.1 ∉ A ∧ IsGateOrder A L

theorem fourierAfter_append (A : Finset (Fin n)) (L₁ L₂ : List (geometry n).Cell) :
    fourierAfter A (L₁ ++ L₂) = fourierAfter (fourierAfter A L₁) L₂ := by
  induction L₁ generalizing A with
  | nil => rfl
  | cons b L₁ ih => rcases b with a | p <;> exact ih _

theorem isGateOrder_append {A : Finset (Fin n)} {L₁ L₂ : List (geometry n).Cell} :
    IsGateOrder A (L₁ ++ L₂) ↔ IsGateOrder A L₁ ∧ IsGateOrder (fourierAfter A L₁) L₂ := by
  induction L₁ generalizing A with
  | nil => simp [IsGateOrder, fourierAfter]
  | cons b L₁ ih =>
    rcases b with a | p
    · simp only [List.cons_append, IsGateOrder, fourierAfter, ih, and_assoc]
    · simp only [List.cons_append, IsGateOrder, fourierAfter, ih, and_assoc]

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

section Column

variable (x : Config (Qudits (Fin n) d))

/-- The column with the qudits of `A` transformed with phases `θ` and the others still the input
digits of `x`. -/
private noncomputable def phaseState (A : Finset (Fin n)) (θ : Fin n → ℂ)
    (y : Config (Qudits (Fin n) d)) :
    ℂ :=
  invSqrt d ^ A.card * (if ∀ k, k ∉ A → y k = x k then 1 else 0) *
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

private theorem fourier_phaseState {A : Finset (Fin n)} {θ : Fin n → ℂ} {a : Fin n}
    (ha : a ∉ A) :
    gateOp d (.inl a) *ᵥ phaseState x A θ =
      phaseState x (insert a A) (Function.update θ a (((x a : ℕ) : ℂ) / d)) := by
  funext y
  change (place {a} ((fourier d).submatrix (siteEquiv (Qudits (Fin n) d) a)
    (siteEquiv (Qudits (Fin n) d) a)) *ᵥ _) y = _
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
        Function.update θ a (((x a : ℕ) : ℂ) / d) i) =
        exp (2 * Real.pi * I * ((y a : ℕ) : ℂ) * (((x a : ℕ) : ℂ) / d)) *
          ∏ i ∈ A, exp (2 * Real.pi * I * ((y i : ℕ) : ℂ) * θ i) := by
      rw [Finset.prod_insert ha, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun i hi ↦ by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
    rw [phaseState, phaseState, hprod, if_congr hind rfl rfl, hprod',
      Finset.card_insert_of_notMem ha,
      fourier_apply, pow_succ, show 2 * (Real.pi : ℂ) * I * (((y a : ℕ) : ℂ) * ((x a : ℕ) : ℂ)) /
        (d : ℂ) = 2 * Real.pi * I * ((y a : ℕ) : ℂ) * (((x a : ℕ) : ℂ) / d) by ring]
    ring
  · intro b hb
    rw [phaseState, ite_eq_right_iff.mpr fun h ↦ absurd (by simpa using h a ha) hb, mul_zero,
      zero_mul, mul_zero]

private theorem rotation_phaseState {A : Finset (Fin n)} {θ : Fin n → ℂ}
    {p : {p : Fin n × Fin n // p.1 ≠ p.2}} (hp : p.1.2 < p.1.1) (hi : p.1.2 ∈ A)
    (hj : p.1.1 ∉ A) :
    gateOp d (.inr p) *ᵥ phaseState x A θ =
      phaseState x A (Function.update θ p.1.2
        (θ p.1.2 + ((x p.1.1 : ℕ) : ℂ) / (d : ℂ) ^ ((p.1.1 : ℕ) - p.1.2 + 1))) := by
  obtain ⟨⟨j, i⟩, h⟩ := p
  funext y
  change (place ({j} ∪ {i}) ((if i < j then controlledPhase d ((j : ℕ) - i + 1)
    else swapMatrix d).submatrix (pairEquiv (Qudits (Fin n) d) h)
      (pairEquiv (Qudits (Fin n) d) h)) *ᵥ _) y = _
  rw [ite_eq_left hp, controlledPhase, submatrix_diagonal_equiv, place_diagonal_mulVec]
  change exp (2 * Real.pi * I * (((y j : ℕ) : ℂ) * ((y i : ℕ) : ℂ)) / (d : ℂ) ^ ((j : ℕ) - i + 1)) *
    _ = _
  by_cases hy : ∀ k, k ∉ A → y k = x k
  · simp only [phaseState, ite_eq_left hy, hy j hj]
    have hR : ∏ l ∈ A, exp (2 * Real.pi * I * ((y l : ℕ) : ℂ) *
        Function.update θ i (θ i + ((x j : ℕ) : ℂ) / (d : ℂ) ^ ((j : ℕ) - i + 1)) l) =
        exp (2 * Real.pi * I * ((y i : ℕ) : ℂ) *
          (θ i + ((x j : ℕ) : ℂ) / (d : ℂ) ^ ((j : ℕ) - i + 1))) *
          ∏ l ∈ A.erase i, exp (2 * Real.pi * I * ((y l : ℕ) : ℂ) * θ l) := by
      rw [← Finset.mul_prod_erase A _ hi, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun l hl ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    rw [hR, ← Finset.mul_prod_erase A _ hi, mul_add, Complex.exp_add]
    have : 2 * (Real.pi : ℂ) * I * (((x j : ℕ) : ℂ) * ((y i : ℕ) : ℂ)) /
        (d : ℂ) ^ ((j : ℕ) - i + 1) =
        2 * Real.pi * I * ((y i : ℕ) : ℂ) * (((x j : ℕ) : ℂ) / (d : ℂ) ^ ((j : ℕ) - i + 1)) := by
      ring
    rw [this]
    ring
  · simp only [phaseState, ite_eq_right hy]
    ring

/-- The phase that the gate on the cell `b` adds to the qudit `k`. -/
private noncomputable def phaseStep (b : (geometry n).Cell) (k : Fin n) : ℂ :=
  match b with
  | .inl a => if a = k then ((x a : ℕ) : ℂ) / d else 0
  | .inr p => if p.1.2 = k ∧ p.1.2 < p.1.1 then
      ((x p.1.1 : ℕ) : ℂ) / (d : ℂ) ^ ((p.1.1 : ℕ) - p.1.2 + 1) else 0

private theorem foldl_phaseState :
    (L : List (geometry n).Cell) → (A : Finset (Fin n)) → (θ : Fin n → ℂ) → IsGateOrder A L →
      (∀ k, k ∉ A → θ k = 0) →
      L.foldl (fun w b ↦ gateOp d b *ᵥ w) (phaseState x A θ) =
        phaseState x (fourierAfter A L) fun k ↦ θ k + (L.map (phaseStep x · k)).sum
  | [], A, θ, _, _ => by simp [fourierAfter]
  | .inl a :: L, A, θ, ⟨ha, hL⟩, hθ => by
    rw [List.foldl_cons, fourier_phaseState x ha,
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

/-- The phase `0.xᵢxᵢ₊₁⋯xₙ₋₁` in base `d` acquired by the qudit `i`. -/
private noncomputable def phase (i : Fin n) : ℂ :=
  ∑ j ∈ Finset.univ.filter (i ≤ ·), ((x j : ℕ) : ℂ) / (d : ℂ) ^ ((j : ℕ) - i + 1)

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

private theorem encode_rev_cast (y : Config (Qudits (Fin n) d)) :
    ((encode d n (fun i ↦ y (Fin.rev i)) : ℕ) : ℂ) =
      ∑ i : Fin n, ((y i : ℕ) : ℂ) * (d : ℂ) ^ (i : ℕ) := by
  rw [encode_apply]
  push_cast
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k ↦ ?_
  simp only [Fin.revPerm_apply, Fin.val_rev]
  congr 2
  omega

private theorem pow_ratio (hd : (d : ℂ) ≠ 0) (i j : Fin n) :
    (d : ℂ) ^ (i : ℕ) * (d : ℂ) ^ (n - 1 - (j : ℕ)) / (d : ℂ) ^ n =
      if i ≤ j then 1 / (d : ℂ) ^ ((j : ℕ) - i + 1) else (d : ℂ) ^ ((i : ℕ) - j - 1) := by
  have hj := j.2
  split_ifs with h
  · rw [div_eq_div_iff (pow_ne_zero _ hd) (pow_ne_zero _ hd), one_mul,
      ← pow_add, ← pow_add]
    congr 1
    rw [Fin.le_def] at h
    omega
  · rw [div_eq_iff (pow_ne_zero _ hd), ← pow_add, ← pow_add]
    congr 1
    rw [Fin.le_def] at h
    omega

/-- The exponent of the Fourier matrix differs from the phases of the column by an integer. -/
private theorem exponent_eq (y : Config (Qudits (Fin n) d)) :
    ((encode d n (fun i ↦ y (Fin.rev i)) : ℕ) : ℂ) * ((encode d n x : ℕ) : ℂ) / (d : ℂ) ^ n =
      (∑ i : Fin n, ((y i : ℕ) : ℂ) * phase x i) +
        ((∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j ↦ ¬ i ≤ j),
          (y i : ℕ) * (x j : ℕ) * d ^ ((i : ℕ) - j - 1) : ℕ) : ℂ) := by
  rw [encode_rev_cast, encode_apply]
  push_cast
  rw [Finset.sum_mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (y i).pos.ne'
  rw [Finset.sum_div, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ i ≤ j), phase,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    have h := (Finset.mem_filter.mp hj).2
    rw [show ((y i : ℕ) : ℂ) * (d : ℂ) ^ (i : ℕ) * (((x j : ℕ) : ℂ) * (d : ℂ) ^ (n - 1 - (j : ℕ))) /
        (d : ℂ) ^ n = ((y i : ℕ) : ℂ) * ((x j : ℕ) : ℂ) *
          ((d : ℂ) ^ (i : ℕ) * (d : ℂ) ^ (n - 1 - (j : ℕ)) / (d : ℂ) ^ n) by ring, pow_ratio hd,
      ite_eq_left h]
    ring
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    have h := (Finset.mem_filter.mp hj).2
    rw [show ((y i : ℕ) : ℂ) * (d : ℂ) ^ (i : ℕ) * (((x j : ℕ) : ℂ) * (d : ℂ) ^ (n - 1 - (j : ℕ))) /
        (d : ℂ) ^ n = ((y i : ℕ) : ℂ) * ((x j : ℕ) : ℂ) *
          ((d : ℂ) ^ (i : ℕ) * (d : ℂ) ^ (n - 1 - (j : ℕ)) / (d : ℂ) ^ n) by ring, pow_ratio hd,
      ite_eq_right h]

/-- The column with every qudit transformed is the column of the Fourier matrix, read with the
output digits in reverse order. -/
private theorem phaseState_univ (y : Config (Qudits (Fin n) d)) :
    phaseState x Finset.univ (phase x) y = dft d n (fun i ↦ y (Fin.rev i)) x := by
  rw [phaseState, dft, of_apply, Finset.card_univ, Fintype.card_fin,
    ite_eq_left (fun k hk ↦ absurd (Finset.mem_univ k) hk), mul_one, ← Complex.exp_sum]
  congr 1
  rw [mul_div_assoc, exponent_eq, mul_add, Complex.exp_add,
    show 2 * (Real.pi : ℂ) * I * ((_ : ℕ) : ℂ) = ((_ : ℕ) : ℂ) * (2 * Real.pi * I) from
      mul_comm _ _,
    Complex.exp_nat_mul_two_pi_mul_I, mul_one, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ by ring)

/-- The swap on the cell `(a, b)` with `a < b` exchanges the two qudits. -/
private theorem swap_mulVec {p : {p : Fin n × Fin n // p.1 ≠ p.2}} (hp : ¬ p.1.2 < p.1.1)
    (ψ : Config (Qudits (Fin n) d) → ℂ) (y : Config (Qudits (Fin n) d)) :
    (gateOp d (.inr p) *ᵥ ψ) y = ψ (fun v ↦ y (Equiv.swap p.1.1 p.1.2 v)) := by
  obtain ⟨⟨a, b⟩, h⟩ := p
  change (place ({a} ∪ {b}) ((if b < a then controlledPhase d ((a : ℕ) - b + 1)
    else swapMatrix d).submatrix (pairEquiv (Qudits (Fin n) d) h)
      (pairEquiv (Qudits (Fin n) d) h)) *ᵥ ψ) y = _
  rw [ite_eq_right hp, place_pairEquiv_mulVec, Finset.sum_eq_single (y b, y a)
    (fun q _ hq ↦ by rw [swapMatrix_apply, ite_eq_right_iff.mpr fun hc ↦
      absurd (Prod.ext hc.2.symm hc.1.symm) hq, zero_mul]) (by simp),
    swapMatrix_apply, ite_eq_left ⟨rfl, rfl⟩, one_mul]
  congr 1
  funext v
  by_cases hvb : v = b
  · subst hvb
    rw [Function.update_self, Equiv.swap_apply_right]
  · rw [Function.update_of_ne hvb]
    by_cases hva : v = a
    · subst hva
      rw [Function.update_self, Equiv.swap_apply_left]
    · rw [Function.update_of_ne hva, Equiv.swap_apply_of_ne_of_ne hva hvb]

/-- The configuration after the first `m` swaps: the sites `v` with `v < m` or `rev v < m` are
reversed, the others fixed. -/
private def swapped (m : ℕ) (v : Fin n) : Fin n :=
  if (v : ℕ) < m ∨ (Fin.rev v : ℕ) < m then Fin.rev v else v

private theorem foldl_swapCells (ψ : Config (Qudits (Fin n) d) → ℂ) :
    (swapCells n).foldl (fun w b ↦ gateOp d b *ᵥ w) ψ = fun y ↦ ψ (fun v ↦ y (Fin.rev v)) := by
  have key : ∀ m ≤ n / 2, ((swapCells n).take m).foldl (fun w b ↦ gateOp d b *ᵥ w) ψ =
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

private theorem fourierAfter_eq (A : Finset (Fin n)) (L : List (geometry n).Cell) :
    fourierAfter A L = A ∪ Finset.univ.filter fun a ↦ Sum.inl a ∈ L := by
  induction L generalizing A with
  | nil => simp [fourierAfter]
  | cons b L ih =>
    rcases b with a | p
    · rw [fourierAfter, ih]
      ext k
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
        true_and, List.mem_cons, Sum.inl.injEq]
      tauto
    · rw [fourierAfter, ih]
      ext k
      simp

/-- Along any admissible order of the Fourier and controlled phase gates, the product of the
placed gates is the Fourier matrix read with the output digits in reverse order. -/
theorem prod_gateOp_core {L : List (geometry n).Cell} (hL : IsGateOrder ∅ L) (hnd : L.Nodup)
    (hcells : L.toFinset = coreCells n) (y x : Config (Qudits (Fin n) d)) :
    (L.map (gateOp d)).reverse.prod y x = dft d n (fun i ↦ y (Fin.rev i)) x := by
  have hA : fourierAfter ∅ L = Finset.univ := by
    rw [fourierAfter_eq]
    refine Finset.eq_univ_of_forall fun a ↦ ?_
    have : Sum.inl a ∈ L.toFinset := by rw [hcells]; simp [coreCells]
    simpa using List.mem_toFinset.mp this
  have hcol := reverse_prod_mulVec (gateOp d) L (Pi.single x 1)
  rw [← phaseState_empty x 0, foldl_phaseState x L ∅ 0 hL fun _ _ ↦ rfl, hA] at hcol
  have hy := congrFun hcol y
  rw [phaseState_empty, mulVec_single_one, col_apply] at hy
  rw [hy, ← phaseState_univ x y]
  congr 1
  funext k
  rw [Pi.zero_apply, zero_add, ← List.sum_toFinset _ hnd, hcells, sum_phaseStep]

/-- Along any admissible order of the Fourier and controlled phase gates, followed by the swaps,
the product of the placed gates is the Fourier matrix. -/
theorem prod_gateOp_eq_dft {L : List (geometry n).Cell} (hL : IsGateOrder ∅ L) (hnd : L.Nodup)
    (hcells : L.toFinset = coreCells n) :
    ((L ++ swapCells n).map (gateOp d)).reverse.prod = dft d n := by
  ext y x
  rw [← col_apply (((L ++ swapCells n).map (gateOp d)).reverse.prod) x y, ← mulVec_single_one,
    reverse_prod_mulVec, List.foldl_append,
    ← reverse_prod_mulVec (gateOp d) L, foldl_swapCells, mulVec_single_one]
  change (L.map (gateOp d)).reverse.prod (fun v ↦ y v.rev) x = _
  rw [prod_gateOp_core hL hnd hcells]
  congr 2
  funext i
  rw [Fin.rev_rev]

/-! ### The circuit of Nielsen–Chuang -/

/-- The cells of the qudit `i` in the order of Nielsen–Chuang, Fig. 5.1: the Fourier gate, then
the controlled phase gates with target `i` and control `j = i + 1, …, n - 1`. -/
def siteCells (i : Fin n) : List (geometry n).Cell :=
  .inl i :: (List.finRange n).filterMap fun j ↦
    if h : i < j then some (.inr ⟨(j, i), h.ne'⟩) else none

/-- The Fourier and controlled phase cells in the order of Nielsen–Chuang, Fig. 5.1. -/
def seqCells (n : ℕ) : List (geometry n).Cell :=
  (List.finRange n).flatMap siteCells

/-- The layers of one gate each along a list of cells. -/
noncomputable def gateLayers (d : ℕ) (L : List (geometry n).Cell) :
    List (Layer (geometry n) KrausGate (Qudits (Fin n) d) (Qudits (Fin n) d)) :=
  L.map fun b ↦ Layer.single b (qftGate d b)

/-- The Fourier transform with the output digits in reverse order. -/
noncomputable def qftCore (d n : ℕ) :
    Circuit (geometry n) KrausGate (Qudits (Fin n) d) (Qudits (Fin n) d) :=
  Circuit.seq (gateLayers d (seqCells n))

/-- The quantum Fourier transform of Nielsen–Chuang, Fig. 5.1. -/
noncomputable def qft (d n : ℕ) :
    Circuit (geometry n) KrausGate (Qudits (Fin n) d) (Qudits (Fin n) d) :=
  Circuit.seq (gateLayers d (seqCells n ++ swapCells n))

private theorem mem_siteCells {i : Fin n} {b : (geometry n).Cell} :
    b ∈ siteCells i ↔ b = .inl i ∨ ∃ p : {p : Fin n × Fin n // p.1 ≠ p.2},
      p.1.2 = i ∧ i < p.1.1 ∧ b = .inr p := by
  simp only [siteCells, List.mem_cons, List.mem_filterMap, List.mem_finRange, true_and]
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

private theorem isGateOrder_siteCells (i : Fin n) :
    IsGateOrder (Finset.univ.filter fun k : Fin n ↦ k < i) (siteCells i) ∧
      fourierAfter (Finset.univ.filter fun k : Fin n ↦ k < i) (siteCells i) =
        Finset.univ.filter fun k : Fin n ↦ k ≤ i := by
  have key : ∀ (l : List (Fin n)) (A : Finset (Fin n)), i ∈ A → (∀ j ∈ l, i < j → j ∉ A) →
      IsGateOrder A (l.filterMap fun j ↦
          if h : i < j then some (Sum.inr ⟨(j, i), h.ne'⟩ : (geometry n).Cell) else none) ∧
        fourierAfter A (l.filterMap fun j ↦
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
  have key : ∀ m ≤ n, IsGateOrder ∅ ((List.finRange n).take m |>.flatMap siteCells) ∧
      fourierAfter ∅ ((List.finRange n).take m |>.flatMap siteCells) =
        Finset.univ.filter fun k : Fin n ↦ (k : ℕ) < m := by
    intro m hm
    induction m with
    | zero => exact ⟨trivial, by simp [fourierAfter]⟩
    | succ m ih =>
      have hget : (List.finRange n)[m]? = some ⟨m, hm⟩ := by
        rw [List.getElem?_eq_getElem (by simpa using hm)]; simp
      obtain ⟨h₁, h₂⟩ := ih (by omega)
      have hA : (Finset.univ.filter fun k : Fin n ↦ (k : ℕ) < m) =
          Finset.univ.filter fun k : Fin n ↦ k < ⟨m, hm⟩ :=
        Finset.filter_congr fun _ _ ↦ Iff.rfl
      obtain ⟨h₃, h₄⟩ := isGateOrder_siteCells (⟨m, hm⟩ : Fin n)
      rw [List.take_add_one, hget, Option.toList_some, List.flatMap_append, List.flatMap_singleton,
        isGateOrder_append, fourierAfter_append, h₂, hA]
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
    rcases mem_siteCells.mp hb with rfl | ⟨p, hp, -, rfl⟩
    · rcases mem_siteCells.mp hb' with h | ⟨p', -, -, h⟩
      · exact Sum.inl.inj h
      · cases h
    · rcases mem_siteCells.mp hb' with h | ⟨p', hp', -, h⟩
      · cases h
      · rw [← hp, ← hp', Sum.inr.inj h]

theorem toFinset_seqCells : (seqCells n).toFinset = coreCells n := by
  ext b
  rw [List.mem_toFinset, seqCells, List.mem_flatMap]
  constructor
  · rintro ⟨i, -, hb⟩
    rcases mem_siteCells.mp hb with rfl | ⟨p, hp, hlt, rfl⟩
    · simp [coreCells]
    · simp [coreCells, hp ▸ hlt]
  · intro hb
    rcases b with a | p
    · exact ⟨a, List.mem_finRange _, mem_siteCells.mpr (Or.inl rfl)⟩
    · have : p.1.2 < p.1.1 := by simpa [coreCells] using hb
      exact ⟨p.1.2, List.mem_finRange _, mem_siteCells.mpr (Or.inr ⟨p, rfl, this, rfl⟩)⟩

/-- The Fourier matrix is unitary. -/
theorem dft_mem_unitaryGroup (d n : ℕ) : dft d n ∈ unitaryGroup (Config (Qudits (Fin n) d)) ℂ := by
  rw [← prod_gateOp_eq_dft isGateOrder_seqCells seqCells_nodup toFinset_seqCells]
  refine Submonoid.list_prod_mem _ fun M hM ↦ ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hM)
  exact gateOp_mem_unitaryGroup b

private theorem length_siteCells (i : Fin n) : (siteCells i).length = n - i := by
  rw [siteCells, List.length_cons, List.length_filterMap_eq_countP]
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
  rw [seqCells, List.length_flatMap, List.map_congr_left fun i _ ↦ length_siteCells i]
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

/-- Without the swaps, the Fourier transform reverses the order of the output digits. -/
theorem kraus_qftCore (d n : ℕ) (p : (qftCore d n).Index) (y x : Config (Qudits (Fin n) d)) :
    (qftCore d n).kraus KrausGate.ev p y x = dft d n (fun i ↦ y (Fin.rev i)) x := by
  rw [show (qftCore d n).kraus KrausGate.ev p = _ from
      Circuit.kraus_seq_map KrausGate.ev _ (gateOp d) _
      (fun b _ i ↦ Layer.kraus_single KrausGate.ev b (qftGate d b) i) p,
    prod_gateOp_core isGateOrder_seqCells seqCells_nodup toFinset_seqCells]

/-- The single Kraus operator of the circuit `qft d n` is the Fourier transform. -/
theorem kraus_qft (d n : ℕ) (p : (qft d n).Index) : (qft d n).kraus KrausGate.ev p = dft d n := by
  rw [show (qft d n).kraus KrausGate.ev p = _ from Circuit.kraus_seq_map KrausGate.ev _ (gateOp d) _
      (fun b _ i ↦ Layer.kraus_single KrausGate.ev b (qftGate d b) i) p,
    prod_gateOp_eq_dft isGateOrder_seqCells seqCells_nodup toFinset_seqCells]

theorem isUnbranched_qft (d n : ℕ) : (qft d n).IsUnbranched :=
  Circuit.isUnbranched_seq _

private theorem forall_isUnitary_gateLayers (L : List (geometry n).Cell) :
    ∀ M ∈ gateLayers d L, M.Forall KrausGate.ev KrausFamily.IsUnitary := by
  intro M hM
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hM
  exact Layer.forall_single _ (KrausFamily.isUnitary_single (one_mem _)) b _ (isUnitary_qftGate b)

theorem forall_isUnitary_qft (d n : ℕ) : (qft d n).Forall KrausGate.ev KrausFamily.IsUnitary :=
  Circuit.forall_seq _ _ (forall_isUnitary_gateLayers _)

private theorem gateCount_gateLayers (L : List (geometry n).Cell) :
    (Circuit.seq (gateLayers d L)).gateCount = L.length := by
  rw [Circuit.gateCount_seq_eq_length]
  · simp [gateLayers]
  · intro M hM
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hM
    exact Layer.nonempty_index_single (hg := ⟨()⟩) b _
  · intro M hM
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hM
    rcases b with a | p <;> exact Layer.gateCount_single _ _

theorem gateCount_qftCore (d n : ℕ) : (qftCore d n).gateCount = n * (n + 1) / 2 := by
  rw [qftCore, gateCount_gateLayers, length_seqCells]

theorem gateCount_qft (d n : ℕ) : (qft d n).gateCount = n * (n + 1) / 2 + n / 2 := by
  rw [qft, gateCount_gateLayers, List.length_append, length_seqCells, swapCells, List.length_ofFn]

/-- The depth is at most the gate count, since every layer holds one gate. The circuit of
`QFTParallel.lean` applies the same gates in depth at most `2n`. -/
theorem depth_qft_le (d n : ℕ) : (qft d n).depth ≤ n * (n + 1) / 2 + n / 2 :=
  (Circuit.depth_le_gateCount _).trans (gateCount_qft d n).le

end Qudit

/-! ### Qubits -/

namespace Qubit

export Qudit (coreCells IsGateOrder swapCells seqCells isGateOrder_seqCells seqCells_nodup
  toFinset_seqCells length_seqCells)

/-- The matrix of the quantum Fourier transform on `n` qubits (Nielsen–Chuang, eq. (5.2)). -/
noncomputable abbrev dft (n : ℕ) :
    Matrix (Config (Qudits (Fin n) 2)) (Config (Qudits (Fin n) 2)) ℂ :=
  Qudit.dft 2 n

theorem dft_apply {n : ℕ} (y x : Config (Qudits (Fin n) 2)) :
    dft n y x = invSqrtTwo ^ n *
      exp (2 * Real.pi * I * ((encode n y : ℕ) * (encode n x : ℕ) : ℂ) / 2 ^ n) := by
  simp only [dft, Qudit.dft, of_apply, Nat.cast_ofNat]

/-- The gate of the Fourier transform on a cell of a register of qubits. -/
noncomputable abbrev qftGate {n : ℕ} (b : (geometry n).Cell) :
    KrausGate ((geometry n).cell b) (Qudits (Fin n) 2) (Qudits (Fin n) 2) :=
  Qudit.qftGate 2 b

/-- The gate on a cell, placed on the register of qubits. -/
noncomputable abbrev gateOp {n : ℕ} (b : (geometry n).Cell) :
    Matrix (Config (Qudits (Fin n) 2)) (Config (Qudits (Fin n) 2)) ℂ :=
  Qudit.gateOp 2 b

/-- The layers of one gate each along a list of cells. -/
noncomputable abbrev gateLayers {n : ℕ} (L : List (geometry n).Cell) :
    List (Layer (geometry n) KrausGate (Qudits (Fin n) 2) (Qudits (Fin n) 2)) :=
  Qudit.gateLayers 2 L

/-- The quantum Fourier transform on `n` qubits of Nielsen–Chuang, Fig. 5.1. -/
noncomputable abbrev qft (n : ℕ) :
    Circuit (geometry n) KrausGate (Qudits (Fin n) 2) (Qudits (Fin n) 2) :=
  Qudit.qft 2 n

theorem dft_mem_unitaryGroup (n : ℕ) : dft n ∈ unitaryGroup (Config (Qudits (Fin n) 2)) ℂ :=
  Qudit.dft_mem_unitaryGroup 2 n

theorem kraus_qft (n : ℕ) (p : (qft n).Index) : (qft n).kraus KrausGate.ev p = dft n :=
  Qudit.kraus_qft 2 n p

theorem gateCount_qft (n : ℕ) : (qft n).gateCount = n * (n + 1) / 2 + n / 2 :=
  Qudit.gateCount_qft 2 n

theorem depth_qft_le (n : ℕ) : (qft n).depth ≤ n * (n + 1) / 2 + n / 2 :=
  Qudit.depth_qft_le 2 n

end Qubit

end QuantumCircuit
