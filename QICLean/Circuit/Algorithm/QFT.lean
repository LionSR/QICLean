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

/-! ### Layers on vectors -/

open Classical in
/-- The single Kraus operator of a layer, for layers with one. -/
noncomputable def U1 {n : ℕ} (L : Layer (geometry n) KrausGate (Q n) (Q n)) :
    Matrix (Config (Q n)) (Config (Q n)) ℂ :=
  if h : Nonempty L.Index then L.kraus KrausGate.ev h.some else 0

theorem U1_siteLayer {n : ℕ} (i : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    U1 (siteLayer i M) = place {i} (M.submatrix (siteEquiv (Q n) i) (siteEquiv (Q n) i)) := by
  rw [U1, dite_eq_left_of_eq_true (eq_true (nonempty_index_siteLayer i M)), kraus_siteLayer]

theorem U1_pairLayer {n : ℕ} {a b : Fin n} (h : a ≠ b)
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    U1 (pairLayer h M) = place ({a} ∪ {b}) (M.submatrix (pairEquiv (Q n) h) (pairEquiv (Q n) h)) := by
  rw [U1, dite_eq_left_of_eq_true (eq_true (nonempty_index_pairLayer h M)), kraus_pairLayer]

theorem prod_mulVec {n : ℕ} (Ls : List (Layer (geometry n) KrausGate (Q n) (Q n)))
    (v : Config (Q n) → ℂ) :
    ((Ls.map U1).reverse.prod *ᵥ v) = Ls.foldl (fun w L ↦ U1 L *ᵥ w) v := by
  induction Ls generalizing v with
  | nil => simp
  | cons L Ls ih =>
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, ← mulVec_mulVec,
      ih, List.foldl_cons]

theorem rotation_mulVec {n : ℕ} {j i : Fin n} (h : j ≠ i) (ψ : Config (Q n) → ℂ)
    (y : Config (Q n)) :
    (U1 (rotationLayer h) *ᵥ ψ) y =
      exp (2 * Real.pi * I * ((y j : ℕ) * (y i : ℕ) : ℂ) / 2 ^ ((j : ℕ) - i + 1)) * ψ y := by
  rw [rotationLayer, U1_pairLayer, controlled_phaseShift, submatrix_diagonal_equiv,
    place_diagonal_mulVec]
  rfl

theorem swap_mulVec {n : ℕ} {a b : Fin n} (h : a ≠ b) (ψ : Config (Q n) → ℂ)
    (y : Config (Q n)) :
    (U1 (pairLayer h swap) *ᵥ ψ) y = ψ (fun v ↦ y (Equiv.swap a b v)) := by
  rw [U1_pairLayer, place_mulVec_apply, Finset.sum_eq_single
    ((pairEquiv (Q n) h).symm (y b, y a))]
  · rw [submatrix_apply, Equiv.apply_symm_apply]
    have hc : (pairEquiv (Q n) h fun v ↦ y v) = (y b, y a).swap := rfl
    simp only [swap, submatrix_apply, id, one_apply, hc, ↓reduceIte, one_mul]
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
    rw [submatrix_apply]
    simp only [swap, submatrix_apply, id, one_apply]
    rw [ite_eq_right_iff.mpr fun hc ↦ absurd ?_ ha', zero_mul]
    rw [← (pairEquiv (Q n) h).symm_apply_apply a', ← Prod.swap_swap (pairEquiv (Q n) h a'), ← hc]
    rfl
  · intro hm; exact absurd (Finset.mem_univ _) hm

/-! ### The column of the Fourier transform -/

theorem kraus_eq_U1_of_mem {n : ℕ} {L : Layer (geometry n) KrausGate (Q n) (Q n)}
    (hL : L ∈ coreLayers n ++ swapLayers n) (i : L.Index) : L.kraus KrausGate.ev i = U1 L := by
  simp only [List.mem_append, coreLayers, qubitLayers, List.mem_flatMap, List.mem_cons,
    List.mem_filterMap, swapLayers, List.mem_ofFn] at hL
  obtain ⟨m, -, rfl | ⟨j, -, hj⟩⟩ | ⟨k, rfl⟩ := hL
  · rw [kraus_siteLayer, U1_siteLayer]
  · split_ifs at hj with h
    obtain rfl := Option.some.inj hj
    exact (kraus_pairLayer _ _ i).trans (U1_pairLayer _ _).symm
  · rw [kraus_pairLayer, U1_pairLayer]

section Column

variable {n : ℕ} (x : Config (Q n))

/-- The phase `0.xᵢxᵢ₊₁⋯xₙ₋₁` acquired by the qubit `i`. -/
noncomputable def phase (i : Fin n) : ℂ :=
  ∑ j ∈ Finset.univ.filter (i ≤ ·), ((x j : ℕ) : ℂ) / 2 ^ ((j : ℕ) - i + 1)

/-- The column after the qubits `i < m` have been processed. -/
noncomputable def qstate (m : ℕ) (y : Config (Q n)) : ℂ :=
  ((Real.sqrt 2 : ℂ))⁻¹ ^ m * (if ∀ k : Fin n, m ≤ k → y k = x k then 1 else 0) *
    ∏ i ∈ Finset.univ.filter (fun i : Fin n ↦ (i : ℕ) < m),
      exp (2 * Real.pi * I * ((y i : ℕ) : ℂ) * phase x i)

/-- The column during the processing of the qubit `m`, with the phase `c` acquired so far. -/
noncomputable def qstate' (m : Fin n) (c : ℂ) (y : Config (Q n)) : ℂ :=
  ((Real.sqrt 2 : ℂ))⁻¹ ^ ((m : ℕ) + 1) * (if ∀ k : Fin n, m < k → y k = x k then 1 else 0) *
    (∏ i ∈ Finset.univ.filter (fun i : Fin n ↦ (i : ℕ) < m),
      exp (2 * Real.pi * I * ((y i : ℕ) : ℂ) * phase x i)) *
    exp (2 * Real.pi * I * ((y m : ℕ) : ℂ) * c)

theorem neg_one_pow_eq_exp (a b : ℕ) :
    ((-1 : ℂ) ^ (a * b)) = exp (2 * Real.pi * I * (a : ℂ) * ((b : ℂ) / 2)) := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem hadamard_qstate (m : Fin n) :
    U1 (siteLayer m hadamard) *ᵥ qstate x m = qstate' x m (((x m : ℕ) : ℂ) / 2) := by
  funext y
  rw [U1_siteLayer, place_site_mulVec, Fintype.sum_eq_single (x m)]
  · have hupd : ∀ i : Fin n, (i : ℕ) < m → Function.update y m (x m) i = y i :=
      fun i hi ↦ Function.update_of_ne (Fin.ne_of_lt hi) _ _
    have hprod : ∏ i ∈ Finset.univ.filter (fun i : Fin n ↦ (i : ℕ) < m),
        exp (2 * Real.pi * I * ((Function.update y m (x m) i : ℕ) : ℂ) * phase x i) =
        ∏ i ∈ Finset.univ.filter (fun i : Fin n ↦ (i : ℕ) < m),
          exp (2 * Real.pi * I * ((y i : ℕ) : ℂ) * phase x i) :=
      Finset.prod_congr rfl fun i hi ↦ by rw [hupd i (Finset.mem_filter.mp hi).2]
    have hind : (∀ k : Fin n, (m : ℕ) ≤ k → Function.update y m (x m) k = x k) ↔
        ∀ k : Fin n, m < k → y k = x k := by
      constructor
      · intro h k hk
        rw [← h k hk.le, Function.update_of_ne (Fin.ne_of_gt hk)]
      · intro h k hk
        rcases (Fin.le_iff_val_le_val.mpr hk).lt_or_eq with hk | hk
        · rw [Function.update_of_ne (Fin.ne_of_gt hk)]; exact h k hk
        · rw [← hk, Function.update_self]
    have hH : Qubit.hadamard (y m) (x m) = ((Real.sqrt 2 : ℂ))⁻¹ *
        exp (2 * Real.pi * I * ((y m : ℕ) : ℂ) * (((x m : ℕ) : ℂ) / 2)) := by
      rw [Qubit.hadamard, of_apply, neg_one_pow_eq_exp]
    rw [qstate, qstate', hprod, if_congr hind rfl rfl, hH, pow_succ]
    ring
  · intro b hb
    rw [qstate, ite_eq_right_iff.mpr fun h ↦ absurd (by simpa using h m le_rfl) hb, mul_zero,
      zero_mul, mul_zero]

theorem rotation_qstate' {m j : Fin n} (h : m < j) (c : ℂ) :
    U1 (rotationLayer h.ne') *ᵥ qstate' x m c =
      qstate' x m (c + ((x j : ℕ) : ℂ) / 2 ^ ((j : ℕ) - m + 1)) := by
  funext y
  rw [rotation_mulVec]
  by_cases hy : ∀ k : Fin n, m < k → y k = x k
  · simp only [qstate', if_pos hy, hy j h]
    rw [mul_add, Complex.exp_add]
    have : 2 * (Real.pi : ℂ) * I * (((x j : ℕ) : ℂ) * ((y m : ℕ) : ℂ)) / 2 ^ ((j : ℕ) - m + 1) =
        2 * Real.pi * I * ((y m : ℕ) : ℂ) * (((x j : ℕ) : ℂ) / 2 ^ ((j : ℕ) - m + 1)) := by ring
    rw [this]
    ring
  · simp only [qstate', if_neg hy]
    ring

theorem foldl_rotations (m : Fin n) (c : ℂ) (l : List (Fin n)) :
    (l.filterMap fun j ↦ if h : m < j then some (rotationLayer h.ne') else none).foldl
        (fun w L ↦ U1 L *ᵥ w) (qstate' x m c) =
      qstate' x m (c + ((l.filter (m < ·)).map fun j ↦
        ((x j : ℕ) : ℂ) / 2 ^ ((j : ℕ) - m + 1)).sum) := by
  induction l generalizing c with
  | nil => simp
  | cons j l ih =>
    by_cases h : m < j
    · rw [List.filterMap_cons, dif_pos h, List.foldl_cons, rotation_qstate' x h, ih,
        List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, add_assoc]
    · rw [List.filterMap_cons, dif_neg h, ih, List.filter_cons_of_neg (by simpa using h)]

theorem sum_filter_finRange (p : Fin n → Prop) [DecidablePred p] (f : Fin n → ℂ) :
    (((List.finRange n).filter (p ·)).map f).sum = ∑ j ∈ Finset.univ.filter p, f j := by
  rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _), List.toFinset_filter,
    List.toFinset_finRange]
  simp

theorem phase_eq (m : Fin n) : phase x m = ((x m : ℕ) : ℂ) / 2 +
    ∑ j ∈ Finset.univ.filter (m < ·), ((x j : ℕ) : ℂ) / 2 ^ ((j : ℕ) - m + 1) := by
  rw [phase, show Finset.univ.filter (m ≤ ·) = insert m (Finset.univ.filter (m < ·)) by
      ext k; simp [le_iff_eq_or_lt, eq_comm], Finset.sum_insert (by simp)]
  simp

theorem foldl_qubitLayers (m : Fin n) :
    (qubitLayers m).foldl (fun w L ↦ U1 L *ᵥ w) (qstate x m) = qstate x (m + 1) := by
  rw [qubitLayers, List.foldl_cons, hadamard_qstate, foldl_rotations,
    sum_filter_finRange (m < ·), ← phase_eq]
  funext y
  have hind : (∀ k : Fin n, m < k → y k = x k) ↔ ∀ k : Fin n, (m : ℕ) + 1 ≤ k → y k = x k :=
    forall_congr' fun k ↦ by rw [Fin.lt_iff_val_lt_val, Nat.succ_le_iff]
  have hfil : Finset.univ.filter (fun i : Fin n ↦ (i : ℕ) < m + 1) =
      insert m (Finset.univ.filter fun i : Fin n ↦ (i : ℕ) < m) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [qstate', qstate, if_congr hind rfl rfl, hfil, Finset.prod_insert (by simp)]
  ring

theorem qstate_zero : qstate x 0 = Pi.single x 1 := by
  funext y
  simp only [qstate, pow_zero, one_mul, Nat.zero_le, true_implies, Nat.not_lt_zero,
    Finset.filter_false, Finset.prod_empty, mul_one, Pi.single_apply]
  exact if_congr funext_iff.symm rfl rfl

theorem foldl_coreLayers :
    (coreLayers n).foldl (fun w L ↦ U1 L *ᵥ w) (Pi.single x 1) = qstate x n := by
  rw [coreLayers, List.foldl_flatMap, ← qstate_zero]
  have key : ∀ m ≤ n, ((List.finRange n).take m).foldl
      (fun acc i ↦ (qubitLayers i).foldl (fun w L ↦ U1 L *ᵥ w) acc) (qstate x 0) = qstate x m := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      have hget : (List.finRange n)[m]? = some ⟨m, hm⟩ := by
        rw [List.getElem?_eq_getElem (by simpa using hm)]; simp
      rw [List.take_add_one, hget, Option.toList_some, List.foldl_append, ih (by omega),
        List.foldl_cons, List.foldl_nil]
      exact foldl_qubitLayers x ⟨m, hm⟩
  rw [← key n le_rfl, List.take_of_length_le (by simp)]

/-- The configuration after the first `m` swaps: sites `v` with `v < m` or `rev v < m` are
reversed, the others fixed. -/
def swapped (m : ℕ) (v : Fin n) : Fin n :=
  if (v : ℕ) < m ∨ (Fin.rev v : ℕ) < m then Fin.rev v else v

theorem foldl_swapLayers (ψ : Config (Q n) → ℂ) :
    (swapLayers n).foldl (fun w L ↦ U1 L *ᵥ w) ψ = fun y ↦ ψ (fun v ↦ y (Fin.rev v)) := by
  have key : ∀ m ≤ n / 2, ((swapLayers n).take m).foldl (fun w L ↦ U1 L *ᵥ w) ψ =
      fun y ↦ ψ (fun v ↦ y (swapped m v)) := by
    intro m hm
    induction m with
    | zero => funext y; simp [swapped]
    | succ m ih =>
      have hget : (swapLayers n)[m]? = some (pairLayer (rev_ne_of_lt_half ⟨m, by omega⟩) swap) := by
        rw [List.getElem?_eq_getElem (by simp [swapLayers]; omega)]; simp [swapLayers]
      rw [List.take_add_one, hget, Option.toList_some, List.foldl_append, ih (by omega),
        List.foldl_cons, List.foldl_nil]
      funext y
      rw [swap_mulVec]
      congr 1
      funext v
      refine congrArg y ?_
      simp only [swapped, Equiv.swap_apply_def]
      split_ifs <;> simp only [Fin.ext_iff, Fin.val_rev] at * <;> omega
  rw [← List.take_of_length_le (le_of_eq (by simp [swapLayers] : (swapLayers n).length = n / 2)),
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

theorem encode_rev_cast (y : Config (Q n)) :
    ((encode n (fun i ↦ y (Fin.rev i)) : ℕ) : ℂ) = ∑ i : Fin n, ((y i : ℕ) : ℂ) * 2 ^ (i : ℕ) := by
  rw [encode_apply]
  push_cast
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k ↦ ?_
  simp only [Fin.revPerm_apply, Fin.val_rev]
  congr 2
  omega

theorem encode_cast (x : Config (Q n)) :
    ((encode n x : ℕ) : ℂ) = ∑ j : Fin n, ((x j : ℕ) : ℂ) * 2 ^ (n - 1 - (j : ℕ)) := by
  rw [encode_apply]; push_cast; rfl

theorem pow_ratio (i j : Fin n) :
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

theorem exponent_eq (y : Config (Q n)) :
    ((encode n (fun i ↦ y (Fin.rev i)) : ℕ) : ℂ) * ((encode n x : ℕ) : ℂ) / 2 ^ n =
      (∑ i : Fin n, ((y i : ℕ) : ℂ) * phase x i) +
        ((∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j ↦ ¬ i ≤ j),
          (y i : ℕ) * (x j : ℕ) * 2 ^ ((i : ℕ) - j - 1) : ℕ) : ℂ) := by
  rw [encode_rev_cast, encode_cast, Finset.sum_mul_sum, Finset.sum_div]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_div, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ i ≤ j), phase,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    have h := (Finset.mem_filter.mp hj).2
    rw [show ((y i : ℕ) : ℂ) * 2 ^ (i : ℕ) * (((x j : ℕ) : ℂ) * 2 ^ (n - 1 - (j : ℕ))) / 2 ^ n =
      ((y i : ℕ) : ℂ) * ((x j : ℕ) : ℂ) * ((2 : ℂ) ^ (i : ℕ) * 2 ^ (n - 1 - (j : ℕ)) / 2 ^ n) by
        ring, pow_ratio, if_pos h]
    ring
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    have h := (Finset.mem_filter.mp hj).2
    rw [show ((y i : ℕ) : ℂ) * 2 ^ (i : ℕ) * (((x j : ℕ) : ℂ) * 2 ^ (n - 1 - (j : ℕ))) / 2 ^ n =
      ((y i : ℕ) : ℂ) * ((x j : ℕ) : ℂ) * ((2 : ℂ) ^ (i : ℕ) * 2 ^ (n - 1 - (j : ℕ)) / 2 ^ n) by
        ring, pow_ratio, if_neg h]

theorem qstate_n (y : Config (Q n)) : qstate x n y = dft n (fun i ↦ y (Fin.rev i)) x := by
  have hr : Real.sqrt (2 ^ n) = Real.sqrt 2 ^ n := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
      Real.mul_self_sqrt (by norm_num)]
  have hsqrt : ((Real.sqrt 2 : ℂ))⁻¹ ^ n = ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ := by
    rw [hr, Complex.ofReal_pow, inv_pow]
  have hfil : Finset.univ.filter (fun i : Fin n ↦ (i : ℕ) < n) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ ↦ i.2
  rw [qstate, dft, of_apply, hsqrt, hfil, if_pos (fun k hk ↦ absurd k.2 (by omega)), mul_one,
    ← Complex.exp_sum]
  congr 1
  rw [mul_div_assoc, exponent_eq, mul_add, Complex.exp_add,
    show 2 * (Real.pi : ℂ) * I * ((_ : ℕ) : ℂ) = ((_ : ℕ) : ℂ) * (2 * Real.pi * I) from mul_comm _ _,
    Complex.exp_nat_mul_two_pi_mul_I, mul_one, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ by ring)

end Column

/-! ### Statements -/

/-- Without the swaps, the Fourier transform reverses the order of the output bits. -/
theorem kraus_qftCore (n : ℕ) (p : (qftCore n).Index) (y x : Config (Q n)) :
    (qftCore n).kraus KrausGate.ev p y x = dft n (fun i ↦ y (Fin.rev i)) x := by
  rw [show (qftCore n).kraus KrausGate.ev p = ((coreLayers n).map U1).reverse.prod from
    Circuit.kraus_seq KrausGate.ev U1 _ (fun L hL ↦ kraus_eq_U1_of_mem (List.mem_append_left _ hL)) p,
    ← col_apply ((coreLayers n).map U1).reverse.prod x y,
    ← mulVec_single_one, prod_mulVec, foldl_coreLayers, qstate_n]

/-- The single Kraus operator of the circuit `qft n` is the Fourier transform. -/
theorem kraus_qft (n : ℕ) (p : (qft n).Index) : (qft n).kraus KrausGate.ev p = dft n := by
  ext y x
  rw [show (qft n).kraus KrausGate.ev p = ((coreLayers n ++ swapLayers n).map U1).reverse.prod
      from Circuit.kraus_seq KrausGate.ev U1 _ (fun L hL ↦ kraus_eq_U1_of_mem hL) p,
    ← col_apply (((coreLayers n ++ swapLayers n).map U1).reverse.prod) x y,
    ← mulVec_single_one, prod_mulVec, List.foldl_append, foldl_coreLayers, foldl_swapLayers]
  change qstate x n (fun v ↦ y v.rev) = dft n y x
  rw [qstate_n]
  congr 2
  funext i
  rw [Fin.rev_rev]

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

/-! ### Gate counts -/

theorem nonempty_index_and_gateCount_of_mem {n : ℕ} {L : Layer (geometry n) KrausGate (Q n) (Q n)}
    (hL : L ∈ coreLayers n ++ swapLayers n) : Nonempty L.Index ∧ L.gateCount = 1 := by
  simp only [List.mem_append, coreLayers, qubitLayers, List.mem_flatMap, List.mem_cons,
    List.mem_filterMap, swapLayers, List.mem_ofFn] at hL
  obtain ⟨i, -, rfl | ⟨j, -, hj⟩⟩ | ⟨k, rfl⟩ := hL
  · exact ⟨nonempty_index_siteLayer _ _, Layer.gateCount_single (Γ := geometry n) _ _⟩
  · split_ifs at hj with h
    obtain rfl := Option.some.inj hj
    exact ⟨nonempty_index_pairLayer _ _, Layer.gateCount_single (Γ := geometry n) _ _⟩
  · exact ⟨nonempty_index_pairLayer _ _, Layer.gateCount_single (Γ := geometry n) _ _⟩

theorem gateCount_seq_eq_length {n : ℕ} (Ls : List (Layer (geometry n) KrausGate (Q n) (Q n)))
    (h : ∀ L ∈ Ls, Nonempty L.Index ∧ L.gateCount = 1) :
    (Circuit.seq Ls).gateCount = Ls.length := by
  rw [Circuit.gateCount, Circuit.total_seq _ Ls fun L hL ↦ (h L hL).1,
    List.map_congr_left fun L hL ↦ (h L hL).2, List.map_const', List.sum_replicate, smul_eq_mul,
    mul_one]

theorem length_qubitLayers {n : ℕ} (i : Fin n) : (qubitLayers i).length = n - i := by
  rw [qubitLayers, List.length_cons, List.length_filterMap_eq_countP]
  have : ∀ j : Fin n, ((if h : i < j then some (rotationLayer h.ne') else none).isSome) =
      decide (i < j) := fun j ↦ by split_ifs with h <;> simp [h]
  simp only [this]
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _), List.toFinset_filter,
    List.toFinset_finRange]
  simp only [decide_eq_true_eq]
  rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  omega

theorem length_coreLayers (n : ℕ) : (coreLayers n).length = n * (n + 1) / 2 := by
  rw [coreLayers, List.length_flatMap]
  simp only [length_qubitLayers]
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

/-- The Fourier transform without the swaps uses `n (n + 1) / 2` gates: `n` Hadamard gates and
`n (n - 1) / 2` controlled phase gates. -/
theorem gateCount_qftCore (n : ℕ) : (qftCore n).gateCount = n * (n + 1) / 2 := by
  rw [qftCore, gateCount_seq_eq_length _ fun L hL ↦
    nonempty_index_and_gateCount_of_mem (List.mem_append_left _ hL), length_coreLayers]

theorem gateCount_qft (n : ℕ) : (qft n).gateCount = n * (n + 1) / 2 + n / 2 := by
  rw [qft, gateCount_seq_eq_length _ fun L hL ↦ nonempty_index_and_gateCount_of_mem hL,
    List.length_append, length_coreLayers, swapLayers, List.length_ofFn]

/-- A depth bound. Every layer holds one gate, so the depth is the gate count; packing
commuting gates into layers gives depth `O(n)`, which is not attempted here. -/
theorem depth_qft_le (n : ℕ) : (qft n).depth ≤ n * (n + 1) / 2 + n / 2 :=
  (Circuit.depth_le_gateCount _).trans (gateCount_qft n).le

end Qubit

end QuantumCircuit
