/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Algorithm.QFT
import QICLean.Circuit.Core.Parallel

/-!
# The quantum Fourier transform in linear depth

The gates of the Fourier transform of Nielsen–Chuang, Fig. 5.1, can be scheduled in time: the
Hadamard gate on the qubit `i` at time `2i` and the controlled phase gate with control `j`
and target `i < j` at time `i + j`. The gates at one time act on pairwise disjoint cells, the
order of the gates on each qubit is kept, and a controlled phase gate with control `j` acts
before the Hadamard gate on `j`. The `2n - 1` layers so obtained, followed by one layer of the
`n / 2` swaps, give a circuit of depth at most `2n` whose Kraus operator is the Fourier
transform.

## Main definitions

* `QuantumCircuit.Qubit.timeLayer` — the gates at one time.
* `QuantumCircuit.Qubit.qftPar` — the Fourier transform in `2n` layers.

## Main results

* `QuantumCircuit.Qubit.kraus_qftPar` — the Kraus operator of `qftPar n` is `dft n`.
* `QuantumCircuit.Qubit.depth_qftPar_le` — its depth is at most `2n`.
* `QuantumCircuit.Qubit.gateCount_qftPar` — it uses the gates of `qft n`.
-/

open Matrix ManyBody Complex

namespace QuantumCircuit

namespace Qubit

variable {n : ℕ}

/-- The matrix of the Fourier transform on a cell: the Hadamard gate on a qubit, the controlled
phase gate `R_{j-i+1}` on the ordered pair `(j, i)`. -/
noncomputable def qftV : (b : (geometry n).Cell) →
    Matrix (RegionConfig (Q n) ((geometry n).cell b)) (RegionConfig (Q n) ((geometry n).cell b)) ℂ
  | .inl a => hadamard.submatrix (siteEquiv (Q n) a) (siteEquiv (Q n) a)
  | .inr ⟨(j, i), h⟩ => (controlled (phaseShift ((j : ℕ) - i + 1))).submatrix (pairEquiv (Q n) h)
      (pairEquiv (Q n) h)

/-- The gate of the Fourier transform on a cell. -/
noncomputable abbrev qftGate (b : (geometry n).Cell) :
    KrausGate ((geometry n).cell b) (Q n) (Q n) :=
  KrausFamily.single (qftV b)

/-- The cells used at time `t`: the qubit `a` with `2a = t`, and the pairs `(j, i)` with `i < j`
and `i + j = t`. -/
def timeCells (t : ℕ) : Finset (Fin n ⊕ {p : Fin n × Fin n // p.1 ≠ p.2}) :=
  (Finset.univ.filter fun a : Fin n ↦ 2 * (a : ℕ) = t).disjSum
    (Finset.univ.filter fun p : {p : Fin n × Fin n // p.1 ≠ p.2} ↦
      p.1.2 < p.1.1 ∧ (p.1.1 : ℕ) + p.1.2 = t)

theorem mem_cell_inl {a v : Fin n} : v ∈ (geometry n).cell (.inl a) ↔ v = a :=
  Finset.mem_singleton

theorem mem_cell_inr {p : {p : Fin n × Fin n // p.1 ≠ p.2}} {v : Fin n} :
    v ∈ (geometry n).cell (.inr p) ↔ v = p.1.1 ∨ v = p.1.2 := by
  change v ∈ ({p.1.1} ∪ {p.1.2} : Finset (Fin n)) ↔ _
  simp

theorem timeCells_pairwiseDisjoint (t : ℕ) :
    ((timeCells (n := n) t : Set (geometry n).Cell)).PairwiseDisjoint (geometry n).cell := by
  intro b hb b' hb' hne
  rw [Finset.mem_coe] at hb hb'
  refine Finset.disjoint_left.mpr fun v hv hv' ↦ hne ?_
  change Fin n ⊕ {p : Fin n × Fin n // p.1 ≠ p.2} at b b'
  rcases b with a | p <;> rcases b' with a' | p' <;>
    simp only [timeCells, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.lt_def] at hb hb'
  · rw [mem_cell_inl] at hv hv'
    exact congrArg Sum.inl (hv.symm.trans hv')
  · exfalso
    rw [mem_cell_inl] at hv
    rw [mem_cell_inr] at hv'
    subst hv
    rcases hv' with h | h <;> (rw [Fin.ext_iff] at h; omega)
  · exfalso
    rw [mem_cell_inr] at hv
    rw [mem_cell_inl] at hv'
    subst hv'
    rcases hv with h | h <;> (rw [Fin.ext_iff] at h; omega)
  · rw [mem_cell_inr, Fin.ext_iff, Fin.ext_iff] at hv hv'
    have h₁ : p.1.1 = p'.1.1 := Fin.ext (by
      rcases hv with h | h <;> rcases hv' with h' | h' <;> omega)
    have h₂ : p.1.2 = p'.1.2 := Fin.ext (by have := congrArg Fin.val h₁; omega)
    exact congrArg Sum.inr (Subtype.ext (Prod.ext h₁ h₂))

/-- The gates of the Fourier transform at time `t`. -/
noncomputable abbrev timeLayer (t : ℕ) : Layer (geometry n) KrausGate (Q n) (Q n) :=
  Layer.ofCells (timeCells t) (timeCells_pairwiseDisjoint t) qftGate

/-- The cell of the swap of the qubits `k` and `rev k`, for `k < n / 2`. -/
def swapCell (k : Fin (n / 2)) : (geometry n).Cell :=
  .inr ⟨(⟨k, by omega⟩, Fin.rev ⟨k, by omega⟩), rev_ne_of_lt_half k⟩

/-- The cells of the swaps: the pairs `(k, rev k)` with `k < n / 2`. -/
def swapCells : Finset (geometry n).Cell :=
  (Finset.univ : Finset (Fin (n / 2))).map ⟨swapCell, fun k k' h ↦ by
      simp only [swapCell, Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
      exact Fin.ext h.1⟩

/-- The swap on a pair, and the identity on a qubit. -/
noncomputable def swapV : (b : (geometry n).Cell) →
    Matrix (RegionConfig (Q n) ((geometry n).cell b)) (RegionConfig (Q n) ((geometry n).cell b)) ℂ
  | .inl _ => 1
  | .inr ⟨_, h⟩ => swap.submatrix (pairEquiv (Q n) h) (pairEquiv (Q n) h)

/-- The gate of the swaps. -/
noncomputable abbrev swapGate (b : (geometry n).Cell) :
    KrausGate ((geometry n).cell b) (Q n) (Q n) :=
  KrausFamily.single (swapV b)

theorem swapCells_pairwiseDisjoint :
    ((swapCells (n := n) : Set (geometry n).Cell)).PairwiseDisjoint (geometry n).cell := by
  intro b hb b' hb' hne
  simp only [Finset.mem_coe, swapCells, Finset.mem_map, Finset.mem_univ, true_and] at hb hb'
  obtain ⟨k, rfl⟩ := hb
  obtain ⟨k', rfl⟩ := hb'
  have hk : (k : ℕ) ≠ k' := fun h ↦ hne (by rw [Fin.ext h])
  refine Finset.disjoint_left.mpr fun v hv hv' ↦ ?_
  have h₁ := (mem_cell_inr (p := ⟨(⟨k, by omega⟩, Fin.rev ⟨k, by omega⟩),
    rev_ne_of_lt_half k⟩)).mp hv
  have h₂ := (mem_cell_inr (p := ⟨(⟨k', by omega⟩, Fin.rev ⟨k', by omega⟩),
    rev_ne_of_lt_half k'⟩)).mp hv'
  clear hv hv'
  rw [Fin.ext_iff, Fin.ext_iff] at h₁ h₂
  simp only [Fin.val_rev] at h₁ h₂
  have := k.2; have := k'.2
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> omega

/-- The layer of all swaps. -/
noncomputable abbrev swapAll : Layer (geometry n) KrausGate (Q n) (Q n) :=
  Layer.ofCells swapCells swapCells_pairwiseDisjoint swapGate

/-- The Fourier transform in `2n` layers: the gates at the times `0, …, 2n - 2`, then the swaps. -/
noncomputable def qftPar (n : ℕ) : Circuit (geometry n) KrausGate (Q n) (Q n) :=
  Circuit.seq ((List.range (2 * n - 1)).map timeLayer ++ [swapAll])

/-! ### The column of a basis vector -/
section Column

variable (x : Config (Q n))

/-- A column with the qubits of `A` Hadamard-transformed with phases `θ`, the others still the
input bits. -/
noncomputable def pstate (A : Finset (Fin n)) (c : ℂ) (θ : Fin n → ℂ) (y : Config (Q n)) : ℂ :=
  c * (if ∀ k, k ∉ A → y k = x k then 1 else 0) *
    ∏ i ∈ A, exp (2 * Real.pi * I * ((y i : ℕ) : ℂ) * θ i)

theorem pstate_congr {A : Finset (Fin n)} {c : ℂ} {θ θ' : Fin n → ℂ}
    (h : ∀ i ∈ A, θ i = θ' i) : pstate x A c θ = pstate x A c θ' := by
  funext y
  simp only [pstate]
  rw [Finset.prod_congr rfl fun i hi ↦ by rw [h i hi]]

theorem hadamard_pstate {A : Finset (Fin n)} {c : ℂ} {θ : Fin n → ℂ} {a : Fin n} (ha : a ∉ A) :
    place {a} (hadamard.submatrix (siteEquiv (Q n) a) (siteEquiv (Q n) a)) *ᵥ pstate x A c θ =
      pstate x (insert a A) (c * ((Real.sqrt 2 : ℂ))⁻¹)
        (Function.update θ a (((x a : ℕ) : ℂ) / 2)) := by
  funext y
  rw [place_site_mulVec, Fintype.sum_eq_single (x a)]
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
    have hH : Qubit.hadamard (y a) (x a) = ((Real.sqrt 2 : ℂ))⁻¹ *
        exp (2 * Real.pi * I * ((y a : ℕ) : ℂ) * (((x a : ℕ) : ℂ) / 2)) := by
      rw [Qubit.hadamard, of_apply, neg_one_pow_eq_exp]
    rw [pstate, pstate, hprod, if_congr hind rfl rfl, hH, hprod']
    ring
  · intro b hb
    rw [pstate, ite_eq_right_iff.mpr fun h ↦ absurd (by simpa using h a ha) hb, mul_zero,
      zero_mul, mul_zero]

theorem rotation_pstate {A : Finset (Fin n)} {c : ℂ} {θ : Fin n → ℂ} {j i : Fin n} (h : j ≠ i)
    (hi : i ∈ A) (hj : j ∉ A) (k : ℕ) :
    place ({j} ∪ {i}) ((controlled (phaseShift k)).submatrix (pairEquiv (Q n) h)
      (pairEquiv (Q n) h)) *ᵥ pstate x A c θ =
      pstate x A c (Function.update θ i (θ i + ((x j : ℕ) : ℂ) / 2 ^ k)) := by
  funext y
  rw [controlled_phaseShift, submatrix_diagonal_equiv, place_diagonal_mulVec]
  change exp (2 * Real.pi * I * (((y j : ℕ) : ℂ) * ((y i : ℕ) : ℂ)) / 2 ^ k) * _ = _
  by_cases hy : ∀ k, k ∉ A → y k = x k
  · simp only [pstate, ite_eq_left hy, hy j hj]
    have hR : ∏ l ∈ A, exp (2 * Real.pi * I * ((y l : ℕ) : ℂ) *
        Function.update θ i (θ i + ((x j : ℕ) : ℂ) / 2 ^ k) l) =
        exp (2 * Real.pi * I * ((y i : ℕ) : ℂ) * (θ i + ((x j : ℕ) : ℂ) / 2 ^ k)) *
          ∏ l ∈ A.erase i, exp (2 * Real.pi * I * ((y l : ℕ) : ℂ) * θ l) := by
      rw [← Finset.mul_prod_erase A _ hi, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun l hl ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    rw [hR, ← Finset.mul_prod_erase A _ hi, mul_add, Complex.exp_add]
    have : 2 * (Real.pi : ℂ) * I * (((x j : ℕ) : ℂ) * ((y i : ℕ) : ℂ)) / 2 ^ k =
        2 * Real.pi * I * ((y i : ℕ) : ℂ) * (((x j : ℕ) : ℂ) / 2 ^ k) := by ring
    rw [this]
    ring
  · simp only [pstate, ite_eq_right hy]
    ring

/-- The value of the input bit at the site `m`, and `0` past the last site. -/
noncomputable def xval (m : ℕ) : ℂ :=
  if h : m < n then ((x ⟨m, h⟩ : ℕ) : ℂ) else 0

/-- The qubits Hadamard-transformed before time `t`. -/
def doneSet (t : ℕ) : Finset (Fin n) := Finset.univ.filter fun a ↦ 2 * (a : ℕ) < t

/-- The phase of the qubit `k` before time `t`. -/
noncomputable def θt (t : ℕ) (k : Fin n) : ℂ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ k ≤ j ∧ (k : ℕ) + j < t),
    ((x j : ℕ) : ℂ) / 2 ^ ((j : ℕ) - k + 1)

/-- The column before time `t`. -/
noncomputable def tstate (t : ℕ) : Config (Q n) → ℂ :=
  pstate x (doneSet t) (((Real.sqrt 2 : ℂ))⁻¹ ^ (doneSet (n := n) t).card) (θt x t)

theorem tstate_zero : tstate x 0 = Pi.single x 1 := by
  funext y
  simp only [tstate, pstate, doneSet, Nat.not_lt_zero, Finset.filter_false, Finset.card_empty,
    pow_zero, one_mul, Finset.notMem_empty, not_false_eq_true, true_implies, Finset.prod_empty,
    mul_one, Pi.single_apply]
  exact if_congr funext_iff.symm rfl rfl

/-- The targets `i` of the rotations at time `t`, with control `t - i`. -/
def rotValid (t : ℕ) (i : Fin n) : Prop := (i : ℕ) < t - i ∧ t - i < n

instance (t : ℕ) : DecidablePred (rotValid (n := n) t) := fun _ ↦ instDecidableAnd

theorem rot_ne {t : ℕ} {i : Fin n} (h : rotValid t i) : (⟨t - i, h.2⟩ : Fin n) ≠ i :=
  fun e ↦ by have := congrArg Fin.val e; simp only at this; have := h.1; omega

/-- The rotation cell at time `t` with target `i`. -/
def rotCell {t : ℕ} {i : Fin n} (h : rotValid t i) : (geometry n).Cell :=
  .inr ⟨(⟨t - i, h.2⟩, i), rot_ne h⟩

/-- The rotation cells at time `t`, by target. -/
def rList (t : ℕ) (L : List (Fin n)) : List (geometry n).Cell :=
  L.filterMap fun i ↦ if h : rotValid t i then some (rotCell h) else none

/-- The phases added at time `t` by the rotations with targets in `L`. -/
noncomputable def contrib (t : ℕ) (L : List (Fin n)) (k : Fin n) : ℂ :=
  ((L.filter fun i ↦ rotValid t i ∧ i = k).map fun i : Fin n ↦
    xval x (t - (i : ℕ)) / 2 ^ ((t - (i : ℕ)) - (i : ℕ) + 1)).sum

theorem contrib_nil (t : ℕ) (k : Fin n) : contrib x t [] k = 0 := rfl

theorem contrib_cons (t : ℕ) (i : Fin n) (L : List (Fin n)) (k : Fin n) :
    contrib x t (i :: L) k = (if rotValid t i ∧ i = k then
      xval x (t - (i : ℕ)) / 2 ^ ((t - (i : ℕ)) - (i : ℕ) + 1) else 0) + contrib x t L k := by
  unfold contrib
  by_cases h : rotValid t i ∧ i = k
  · rw [List.filter_cons_of_pos (by simpa using h), ite_eq_left h, List.map_cons, List.sum_cons]
  · rw [List.filter_cons_of_neg (by simpa using h), ite_eq_right h, zero_add]

theorem rList_mulVec (t : ℕ) (A : Finset (Fin n)) (c : ℂ)
    (hA : ∀ i (h : rotValid t i), i ∈ A ∧ (⟨t - i, h.2⟩ : Fin n) ∉ A) :
    (L : List (Fin n)) → (θ : Fin n → ℂ) →
      ((rList t L).map fun b ↦ place ((geometry n).cell b) (qftV b)).prod *ᵥ pstate x A c θ =
        pstate x A c (fun k ↦ θ k + contrib x t L k)
  | [], θ => by simp [rList, contrib_nil]
  | i :: L, θ => by
    by_cases h : rotValid t i
    · rw [rList, List.filterMap_cons, dite_eq_left_of_eq_true (eq_true h), ← rList, List.map_cons,
        List.prod_cons, ← mulVec_mulVec, rList_mulVec t A c hA L θ]
      refine ((rotation_pstate x (rot_ne h) (hA i h).1 (hA i h).2 _).trans ?_)
      congr 1
      funext k
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, contrib_cons, ite_eq_left ⟨h, rfl⟩, xval, dite_eq_left h.2]
        ring
      · rw [Function.update_of_ne hk, contrib_cons, ite_eq_right (fun e ↦ hk e.2.symm), zero_add]
    · rw [rList, List.filterMap_cons, dite_eq_right_of_eq_false (eq_false h), ← rList,
        rList_mulVec t A c hA L θ]
      congr 1
      funext k
      rw [contrib_cons, ite_eq_right (fun e ↦ h e.1), zero_add]

/-- The Hadamard cell at time `t`, if `t` is even and `t / 2` a qubit. -/
def hList (t : ℕ) : List (geometry n).Cell :=
  if h : t % 2 = 0 ∧ t / 2 < n then [.inl ⟨t / 2, h.2⟩] else []

/-- The cells at time `t`, the Hadamard cell last. -/
def timeList (t : ℕ) : List (geometry n).Cell := rList t (List.finRange n) ++ hList t

theorem mem_rList {t : ℕ} {L : List (Fin n)} {b : (geometry n).Cell} :
    b ∈ rList t L ↔ ∃ i ∈ L, ∃ h : rotValid t i, rotCell h = b := by
  simp only [rList, List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, hb⟩
    by_cases h : rotValid t i
    · rw [dite_eq_left_of_eq_true (eq_true h)] at hb
      exact ⟨i, hi, h, Option.some.inj hb⟩
    · rw [dite_eq_right_of_eq_false (eq_false h)] at hb; cases hb
  · rintro ⟨i, hi, h, rfl⟩
    exact ⟨i, hi, by rw [dite_eq_left_of_eq_true (eq_true h)]⟩

theorem timeList_nodup (t : ℕ) : (timeList (n := n) t).Nodup := by
  refine List.Nodup.append ?_ ?_ ?_
  · refine List.Nodup.filterMap ?_ (List.nodup_finRange n)
    intro i i' b hb hb'
    by_cases h : rotValid t i <;> by_cases h' : rotValid t i' <;>
      simp only [h, h', dite_eq_left_of_eq_true, dite_eq_right_of_eq_false, eq_true,
        Option.mem_def, Option.some.injEq, reduceCtorEq] at hb hb'
    subst hb
    simp only [rotCell, Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq] at hb'
    exact hb'.2.symm
  · unfold hList; split_ifs <;> simp
  · intro b hb hb'
    unfold hList at hb'
    split_ifs at hb' with h
    · rw [List.mem_singleton] at hb'
      subst hb'
      obtain ⟨i, -, hv, hc⟩ := mem_rList.mp hb
      cases hc
    · cases hb'

theorem timeList_toFinset (t : ℕ) : (timeList (n := n) t).toFinset = timeCells t := by
  ext b
  rw [List.mem_toFinset, timeList, List.mem_append, mem_rList]
  rcases b with a | ⟨⟨j, i⟩, h⟩
  · simp only [timeCells, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and,
      rotCell, reduceCtorEq, and_false, exists_false, false_or, hList]
    split_ifs with hc
    · rw [List.mem_singleton, Sum.inl.injEq, Fin.ext_iff]
      change (a : ℕ) = t / 2 ↔ _
      omega
    · simp only [List.not_mem_nil, false_iff]; omega
  · simp only [timeCells, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and,
      hList]
    have hh : Sum.inr ⟨(j, i), h⟩ ∉ (if h : t % 2 = 0 ∧ t / 2 < n then
        [(Sum.inl ⟨t / 2, h.2⟩ : (geometry n).Cell)] else []) := by
      split_ifs <;> simp
    simp only [hh, or_false, rotCell, Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq,
      List.mem_finRange, true_and, Fin.lt_def]
    constructor
    · rintro ⟨i', hv, h₁, h₂⟩
      subst h₁ h₂
      simp only [rotValid] at hv
      change (i' : ℕ) < t - i' ∧ t - i' + i' = t
      omega
    · rintro ⟨h₁, h₂⟩
      exact ⟨i, ⟨by omega, by omega⟩, Fin.ext (by simp; omega), rfl⟩

theorem θt_succ (t : ℕ) (k : Fin n) : θt x (t + 1) k = θt x t k +
    (if (k : ℕ) ≤ t - k ∧ t - k < n then xval x (t - k) / 2 ^ ((t - k) - k + 1) else 0) := by
  unfold θt
  rw [show Finset.univ.filter (fun j : Fin n ↦ k ≤ j ∧ (k : ℕ) + j < t + 1) =
      Finset.univ.filter (fun j : Fin n ↦ k ≤ j ∧ (k : ℕ) + j < t) ∪
        Finset.univ.filter (fun j : Fin n ↦ k ≤ j ∧ (k : ℕ) + j = t) by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega,
    Finset.sum_union (by
      rw [Finset.disjoint_filter]; intro j _ h₁ h₂; omega)]
  congr 1
  split_ifs with h
  · rw [show Finset.univ.filter (fun j : Fin n ↦ k ≤ j ∧ (k : ℕ) + j = t) = {⟨t - k, h.2⟩} by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Fin.ext_iff, Fin.le_def]; omega, Finset.sum_singleton, xval, dite_eq_left h.2]
  · rw [Finset.sum_eq_zero]
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hj
    exact absurd ⟨by omega, by omega⟩ h

theorem contrib_finRange (t : ℕ) (k : Fin n) : contrib x t (List.finRange n) k =
    if rotValid t k then xval x (t - k) / 2 ^ ((t - k) - k + 1) else 0 := by
  unfold contrib
  rw [sum_filter_finRange (fun i ↦ rotValid t i ∧ i = k)]
  split_ifs with h
  · rw [show Finset.univ.filter (fun i : Fin n ↦ rotValid t i ∧ i = k) = {k} by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h' ↦ h'.2, fun h' ↦ ⟨h' ▸ h, h'⟩⟩, Finset.sum_singleton]
  · rw [Finset.sum_eq_zero]
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact absurd (hi.2 ▸ hi.1) h

theorem timeList_mulVec (t : ℕ) :
    ((timeList t).map fun b ↦ place ((geometry n).cell b) (qftV b)).prod *ᵥ tstate x t =
      tstate x (t + 1) := by
  rw [timeList, List.map_append, List.prod_append, ← mulVec_mulVec]
  have hrot : ∀ i (h : rotValid t i), i ∈ doneSet (n := n) (t + 1) ∧
      (⟨t - i, h.2⟩ : Fin n) ∉ doneSet (t + 1) := by
    intro i h
    simp only [doneSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have := h.1
    omega
  by_cases hc : t % 2 = 0 ∧ t / 2 < n
  · set a : Fin n := ⟨t / 2, hc.2⟩ with ha
    have hav : (a : ℕ) = t / 2 := by rw [ha]
    have ht2 := hc.1
    have hdone : doneSet (n := n) (t + 1) = insert a (doneSet t) := by
      ext k
      simp only [doneSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff]
      omega
    have hna : a ∉ doneSet (n := n) t := by
      simp only [doneSet, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [hList, dite_eq_left_of_eq_true (eq_true hc), List.map_singleton, List.prod_singleton]
    have hH : place ((geometry n).cell (Sum.inl a)) (qftV (Sum.inl a)) *ᵥ tstate x t =
        pstate x (insert a (doneSet t))
          (((Real.sqrt 2 : ℂ))⁻¹ ^ (doneSet (n := n) t).card * ((Real.sqrt 2 : ℂ))⁻¹)
          (Function.update (θt x t) a (((x a : ℕ) : ℂ) / 2)) :=
      hadamard_pstate x hna
    rw [hH, ← hdone, rList_mulVec x t _ _ hrot, tstate, hdone,
      Finset.card_insert_of_notMem hna, pow_succ]
    refine pstate_congr x fun k hk ↦ ?_
    rw [contrib_finRange, θt_succ]
    by_cases hka : k = a
    · subst hka
      have hθ : θt x t a = 0 := Finset.sum_eq_zero fun j hj ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hj; omega
      rw [Function.update_self, ite_eq_right (by simp only [rotValid]; omega), hθ,
        ite_eq_left (by omega), xval, dite_eq_left (by omega)]
      rw [show t - (a : ℕ) - a + 1 = 1 by omega, pow_one, zero_add, add_zero]
      have hfin : (⟨t - (a : ℕ), by omega⟩ : Fin n) = a :=
        Fin.ext (by change t - (a : ℕ) = a; omega)
      rw [hfin]
    · rw [Function.update_of_ne hka]
      have hk' : 2 * (k : ℕ) < t := by
        rw [Finset.mem_insert] at hk
        rcases hk with hk | hk
        · exact absurd hk hka
        · simpa [doneSet] using hk
      congr 1
      by_cases hv : t - (k : ℕ) < n
      · rw [ite_eq_left ⟨by omega, hv⟩, ite_eq_left ⟨by omega, hv⟩]
      · rw [ite_eq_right (fun h ↦ hv h.2), ite_eq_right (fun h ↦ hv h.2)]
  · have hdone : doneSet (n := n) (t + 1) = doneSet t := by
      ext k
      simp only [doneSet, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hk
        by_contra hk'
        exact hc ⟨by omega, by omega⟩
      · intro hk; omega
    rw [hList, dite_eq_right_of_eq_false (eq_false hc), List.map_nil, List.prod_nil, one_mulVec,
      tstate, ← hdone, rList_mulVec x t _ _ hrot, tstate, hdone]
    refine pstate_congr x fun k hk ↦ ?_
    rw [contrib_finRange, θt_succ]
    have hk' : 2 * (k : ℕ) < t := by simpa [doneSet] using hk
    congr 1
    by_cases hv : t - (k : ℕ) < n
    · rw [ite_eq_left ⟨by omega, hv⟩, ite_eq_left ⟨by omega, hv⟩]
    · rw [ite_eq_right (fun h ↦ hv h.2), ite_eq_right (fun h ↦ hv h.2)]

theorem kraus_timeLayer (t : ℕ) (i : (timeLayer (n := n) t).Index) :
    (timeLayer t).kraus KrausGate.ev i =
      ((timeList t).map fun b ↦ place ((geometry n).cell b) (qftV b)).prod := by
  refine Layer.kraus_ofCells (Γ := geometry n) (X := Q n) (timeCells t)
    (timeCells_pairwiseDisjoint t) qftV (timeList t) (timeList_nodup t) ?_ i
  exact timeList_toFinset t

theorem nonempty_index_timeLayer (t : ℕ) : Nonempty (timeLayer (n := n) t).Index :=
  Layer.nonempty_index_ofCells _ _ _ fun _ ↦ ⟨()⟩

theorem U1_timeLayer (t : ℕ) :
    U1 (timeLayer (n := n) t) =
      ((timeList t).map fun b ↦ place ((geometry n).cell b) (qftV b)).prod := by
  rw [U1, dite_eq_left_of_eq_true (eq_true (nonempty_index_timeLayer t)), kraus_timeLayer]

theorem swapCell_injective : Function.Injective (swapCell (n := n)) := fun k k' h ↦ by
  simp only [swapCell, Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
  exact Fin.ext h.1

theorem kraus_swapAll (i : (swapAll (n := n)).Index) :
    (swapAll (n := n)).kraus KrausGate.ev i = ((swapLayers n).map U1).reverse.prod := by
  rw [Layer.kraus_ofCells swapCells swapCells_pairwiseDisjoint swapV
    (List.ofFn swapCell).reverse (List.nodup_reverse.mpr (List.nodup_ofFn.mpr swapCell_injective))
    (by ext b; simp only [List.mem_toFinset, List.mem_reverse, List.mem_ofFn, swapCells,
      Finset.mem_map, Finset.mem_univ, true_and]; exact Iff.rfl)]
  rw [List.map_reverse, swapLayers, List.map_ofFn, List.map_ofFn]
  congr 2
  refine congrArg List.ofFn (funext fun k ↦ ?_)
  rw [Function.comp_apply, Function.comp_apply, U1_pairLayer]
  rfl

theorem nonempty_index_swapAll : Nonempty (swapAll (n := n)).Index :=
  Layer.nonempty_index_ofCells _ _ _ fun _ ↦ ⟨()⟩

theorem U1_swapAll : U1 (swapAll (n := n)) = ((swapLayers n).map U1).reverse.prod := by
  rw [U1, dite_eq_left_of_eq_true (eq_true nonempty_index_swapAll), kraus_swapAll]

theorem list_prod_mulVec (l : List (geometry n).Cell)
    (P : (geometry n).Cell → Matrix (Config (Q n)) (Config (Q n)) ℂ) (ψ : Config (Q n) → ℂ) :
    (l.map P).prod *ᵥ ψ = l.foldr (fun b w ↦ P b *ᵥ w) ψ := by
  induction l with
  | nil => simp
  | cons b l ih => rw [List.map_cons, List.prod_cons, ← mulVec_mulVec, ih, List.foldr_cons]

theorem foldl_timeLayers (m : ℕ) :
    ((List.range m).map timeLayer).foldl (fun w L ↦ U1 L *ᵥ w) (Pi.single x 1) = tstate x m := by
  induction m with
  | zero => rw [List.range_zero, List.map_nil, List.foldl_nil, tstate_zero]
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih, List.map_singleton,
      List.foldl_cons, List.foldl_nil, U1_timeLayer, timeList_mulVec]

theorem tstate_final : tstate x (2 * n - 1) = qstate x n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [tstate, show 2 * 0 - 1 = 0 from rfl, ← tstate, tstate_zero, qstate_zero]
  have hdone : doneSet (n := n) (2 * n - 1) = Finset.univ :=
    Finset.filter_true_of_mem fun a _ ↦ by have := a.2; omega
  funext y
  rw [tstate, pstate, qstate, hdone, Finset.card_univ, Fintype.card_fin,
    ite_eq_left (fun k hk ↦ absurd (Finset.mem_univ k) hk),
    ite_eq_left (fun k hk ↦ absurd k.2 (by omega)),
    Finset.filter_true_of_mem fun i _ ↦ i.2]
  congr 1
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  congr 2
  unfold θt phase
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have := j.2; have := k.2
  constructor
  · exact fun h ↦ h.1
  · exact fun h ↦ ⟨h, by omega⟩

theorem kraus_eq_U1_of_mem_par {L : Layer (geometry n) KrausGate (Q n) (Q n)}
    (hL : L ∈ (List.range (2 * n - 1)).map timeLayer ++ [swapAll]) (i : L.Index) :
    L.kraus KrausGate.ev i = U1 L := by
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hL
  obtain ⟨t, -, rfl⟩ | rfl := hL
  · rw [kraus_timeLayer, U1_timeLayer]
  · rw [kraus_swapAll, U1_swapAll]

/-- The Fourier transform in linear depth has the matrix of the Fourier transform. -/
theorem kraus_qftPar (n : ℕ) (p : (qftPar n).Index) :
    (qftPar n).kraus KrausGate.ev p = dft n := by
  ext y x
  have h := Circuit.kraus_seq KrausGate.ev U1
    ((List.range (2 * n - 1)).map timeLayer ++ [swapAll]) (fun L hL ↦ kraus_eq_U1_of_mem_par hL) p
  change (Circuit.seq ((List.range (2 * n - 1)).map timeLayer ++ [swapAll])).kraus
    KrausGate.ev p y x = _
  rw [h]
  have hc : (((List.range (2 * n - 1)).map timeLayer ++ [swapAll]).map U1).reverse.prod *ᵥ
      Pi.single x 1 = fun y ↦ qstate x n (fun v ↦ y v.rev) := by
    rw [prod_mulVec, List.foldl_append, foldl_timeLayers, tstate_final, List.foldl_cons,
      List.foldl_nil, U1_swapAll, prod_mulVec, foldl_swapLayers]
  have hy := congrFun hc y
  rw [mulVec_single_one, col_apply] at hy
  rw [hy, qstate_n]
  congr 2
  funext i
  rw [Fin.rev_rev]

end Column

/-! ### Depth -/

theorem depth_qftPar_le (n : ℕ) : (qftPar n).depth ≤ 2 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · change (Circuit.seq [swapAll (n := 0)]).depth ≤ 0
    refine (Circuit.depth_seq_le _).trans ?_
    simp [Layer.depth, swapAll, Layer.ofCells, swapCells]
  refine (Circuit.depth_seq_le _).trans ?_
  have : ∀ L ∈ (List.range (2 * n - 1)).map timeLayer ++ [swapAll (n := n)], L.depth ≤ 1 := by
    intro L hL
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hL
    obtain ⟨t, -, rfl⟩ | rfl := hL
    · exact Layer.depth_ofCells_le_one _ _ _
    · exact Layer.depth_ofCells_le_one _ _ _
  calc (((List.range (2 * n - 1)).map timeLayer ++ [swapAll]).map Layer.depth).sum
      ≤ (((List.range (2 * n - 1)).map timeLayer ++ [swapAll (n := n)]).map fun _ ↦ 1).sum :=
        List.sum_le_sum fun L hL ↦ this L hL
    _ ≤ 2 * n := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul, mul_one, List.length_append,
        List.length_map, List.length_range, List.length_singleton]
      omega

end Qubit

end QuantumCircuit
