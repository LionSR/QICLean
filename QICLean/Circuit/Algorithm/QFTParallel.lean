/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Algorithm.QFT

/-!
# The quantum Fourier transform in linear depth

The gates of the Fourier transform of Nielsen–Chuang, Fig. 5.1, can be scheduled in time: the
Fourier gate on the qudit `i` at time `2i` and the controlled phase with control `j` and target
`i < j` at time `i + j`. The gates at one time act on pairwise disjoint cells, and the order of
the times is an admissible order (`QuantumCircuit.Qudit.IsGateOrder`): a controlled phase
`(j, i)` acts after the Fourier gate on `i`, since `2i < i + j`, and before the Fourier gate on
`j`, since `i + j < 2j`. The `2n - 1` layers so obtained, followed by one layer of the `n / 2`
swaps, give a circuit of depth at most `2n` with the gates of `qft d n`, whose Kraus operator is
the Fourier transform. The qubit circuit is the case `d = 2`.

## Main definitions

* `QuantumCircuit.Qudit.timeCells` — the cells of the gates at one time.
* `QuantumCircuit.Qudit.qftPar` — the Fourier transform in `2n` layers.
* `QuantumCircuit.Qubit.qftPar` — the case `d = 2`.

## Main results

* `QuantumCircuit.Qudit.kraus_qftPar` — the Kraus operator of `qftPar d n` is `dft d n`.
* `QuantumCircuit.Qudit.depth_qftPar_le` — its depth is at most `2n`.
* `QuantumCircuit.Qudit.gateCount_qftPar` — it uses as many gates as `qft d n`.
* `QuantumCircuit.Qudit.forall_isUnitary_qftPar`, `QuantumCircuit.Qudit.isUnbranched_qftPar`.
* `QuantumCircuit.Qubit.kraus_qftPar`, `QuantumCircuit.Qubit.depth_qftPar_le`,
  `QuantumCircuit.Qubit.gateCount_qftPar` — the case `d = 2`.
-/

open Matrix ManyBody

namespace QuantumCircuit

namespace Qudit

variable {d n : ℕ}

/-! ### The cells at one time -/

private theorem rotation_ne {t : ℕ} {i : Fin n} (h : (i : ℕ) < t - i ∧ t - i < n) :
    (⟨t - i, h.2⟩ : Fin n) ≠ i :=
  fun e ↦ by have := congrArg Fin.val e; simp only at this; omega

/-- The controlled phase cells `(t - i, i)` at time `t`, by target `i`. -/
def rotationCells (t : ℕ) : List (geometry n).Cell :=
  (List.finRange n).filterMap fun i : Fin n ↦
    if h : (i : ℕ) < t - i ∧ t - i < n then some (.inr ⟨(⟨t - i, h.2⟩, i), rotation_ne h⟩)
    else none

/-- The Fourier cell at time `t`: the qudit `t / 2`, if `t` is even. -/
def fourierCells (t : ℕ) : List (geometry n).Cell :=
  if h : t % 2 = 0 ∧ t / 2 < n then [.inl ⟨t / 2, h.2⟩] else []

/-- The cells of the gates at time `t`, the Fourier cell last. -/
def timeCells (t : ℕ) : List (geometry n).Cell :=
  rotationCells t ++ fourierCells t

/-- The cells of the Fourier and controlled phase gates, in the order of their times. -/
def parCells (n : ℕ) : List (geometry n).Cell :=
  (List.range (2 * n - 1)).flatMap timeCells

/-- The time of the gate on a cell. -/
private def cellTime : (geometry n).Cell → ℕ
  | .inl a => 2 * a
  | .inr p => p.1.1 + p.1.2

private theorem mem_rotationCells {t : ℕ} {b : (geometry n).Cell} :
    b ∈ rotationCells t ↔ ∃ p : {p : Fin n × Fin n // p.1 ≠ p.2},
      b = .inr p ∧ p.1.2 < p.1.1 ∧ (p.1.1 : ℕ) + p.1.2 = t := by
  simp only [rotationCells, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : (i : ℕ) < t - i ∧ t - i < n
    · rw [dite_eq_left_of_eq_true (eq_true h)] at hi
      refine ⟨_, (Option.some.inj hi).symm, ?_, ?_⟩
      · change (i : ℕ) < t - i; exact h.1
      · change t - (i : ℕ) + i = t; omega
    · rw [dite_eq_right_of_eq_false (eq_false h)] at hi
      cases hi
  · rintro ⟨⟨⟨j, i⟩, hji⟩, rfl, hlt, ht⟩
    change (i : ℕ) < j at hlt
    change (j : ℕ) + i = t at ht
    have h : (i : ℕ) < t - i ∧ t - i < n := ⟨by omega, by omega⟩
    refine ⟨i, ?_⟩
    rw [dite_eq_left_of_eq_true (eq_true h)]
    have hj : (⟨t - i, h.2⟩ : Fin n) = j := Fin.ext (by change t - (i : ℕ) = j; omega)
    subst hj
    rfl

private theorem mem_timeCells {t : ℕ} {b : (geometry n).Cell} :
    b ∈ timeCells t ↔ b ∈ coreCells n ∧ cellTime b = t := by
  rw [timeCells, List.mem_append, mem_rotationCells]
  rcases b with a | p
  · simp only [reduceCtorEq, false_and, exists_false, false_or, fourierCells, coreCells,
      Finset.inl_mem_disjSum, Finset.mem_univ, true_and, cellTime]
    split_ifs with h
    · rw [List.mem_singleton, Sum.inl.injEq, Fin.ext_iff]
      change (a : ℕ) = t / 2 ↔ _
      omega
    · simp only [List.not_mem_nil, false_iff]
      have := a.2
      omega
  · have hh : Sum.inr p ∉ (fourierCells t : List (geometry n).Cell) := by
      unfold fourierCells; split_ifs <;> simp
    simp only [hh, or_false, Sum.inr.injEq, coreCells, Finset.inr_mem_disjSum, Finset.mem_filter,
      Finset.mem_univ, true_and, cellTime]
    exact ⟨fun ⟨p', hp, hlt, ht⟩ ↦ hp ▸ ⟨hlt, ht⟩, fun h ↦ ⟨p, rfl, h⟩⟩

private theorem cellTime_lt {b : (geometry n).Cell} (hb : b ∈ coreCells n) :
    cellTime b < 2 * n - 1 := by
  rcases b with a | ⟨⟨j, i⟩, h⟩
  · have := a.2
    change 2 * (a : ℕ) < 2 * n - 1
    omega
  · simp only [coreCells, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_univ,
      true_and] at hb
    have := j.2
    change (i : ℕ) < j at hb
    change (j : ℕ) + i < 2 * n - 1
    omega

private theorem timeCells_nodup (t : ℕ) : (timeCells (n := n) t).Nodup := by
  refine List.Nodup.append ?_ ?_ ?_
  · refine (List.nodup_finRange n).filterMap fun i i' b hb hb' ↦ ?_
    split_ifs at hb hb' <;>
      simp only [Option.mem_def, Option.some.injEq, reduceCtorEq] at hb hb'
    subst hb
    simp only [Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq] at hb'
    exact hb'.2.symm
  · unfold fourierCells; split_ifs <;> simp
  · intro b hb hb'
    obtain ⟨p, rfl, -⟩ := mem_rotationCells.mp hb
    unfold fourierCells at hb'
    split_ifs at hb' <;> simp at hb'

theorem parCells_nodup : (parCells n).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun t _ ↦ timeCells_nodup t, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun t _ t' _ htt' ↦ ?_
  exact List.disjoint_left.mpr fun b hb hb' ↦
    htt' ((mem_timeCells.mp hb).2.symm.trans (mem_timeCells.mp hb').2)

theorem toFinset_parCells : (parCells n).toFinset = coreCells n := by
  ext b
  rw [List.mem_toFinset, parCells, List.mem_flatMap]
  constructor
  · rintro ⟨t, -, hb⟩
    exact (mem_timeCells.mp hb).1
  · intro hb
    exact ⟨_, List.mem_range.mpr (cellTime_lt hb), mem_timeCells.mpr ⟨hb, rfl⟩⟩

/-- A list of controlled phase gates whose targets are transformed and controls are not. -/
private theorem isGateOrder_of_rotations (A : Finset (Fin n)) :
    (L : List (geometry n).Cell) → (∀ b ∈ L, ∃ p : {p : Fin n × Fin n // p.1 ≠ p.2},
      b = .inr p ∧ p.1.2 < p.1.1 ∧ p.1.2 ∈ A ∧ p.1.1 ∉ A) →
      IsGateOrder A L ∧ fourierAfter A L = A
  | [], _ => ⟨trivial, rfl⟩
  | b :: L, h => by
    obtain ⟨p, rfl, hp⟩ := h b List.mem_cons_self
    have ih := isGateOrder_of_rotations A L fun b' hb' ↦ h b' (List.mem_cons_of_mem _ hb')
    exact ⟨⟨hp.1, hp.2.1, hp.2.2, ih.1⟩, ih.2⟩

private theorem isGateOrder_timeCells (t : ℕ) :
    IsGateOrder (Finset.univ.filter fun a : Fin n ↦ 2 * (a : ℕ) < t) (timeCells t) ∧
      fourierAfter (Finset.univ.filter fun a : Fin n ↦ 2 * (a : ℕ) < t) (timeCells t) =
        Finset.univ.filter fun a : Fin n ↦ 2 * (a : ℕ) < t + 1 := by
  have hrot := isGateOrder_of_rotations (Finset.univ.filter fun a : Fin n ↦ 2 * (a : ℕ) < t)
    (rotationCells t) fun b hb ↦ by
      obtain ⟨p, rfl, hlt, ht⟩ := mem_rotationCells.mp hb
      refine ⟨p, rfl, hlt, ?_, ?_⟩ <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] <;>
        rw [Fin.lt_def] at hlt <;> omega
  rw [timeCells, isGateOrder_append, fourierAfter_append, hrot.2]
  refine ⟨⟨hrot.1, ?_⟩, ?_⟩ <;> unfold fourierCells <;> split_ifs with h
  · exact ⟨by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, trivial⟩
  · trivial
  · ext a
    simp only [fourierAfter, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.ext_iff]
    omega
  · ext a
    simp only [fourierAfter, Finset.mem_filter, Finset.mem_univ, true_and]
    have := a.2
    omega

theorem isGateOrder_parCells : IsGateOrder ∅ (parCells n) := by
  have key : ∀ m, IsGateOrder ∅ ((List.range m).flatMap (timeCells (n := n))) ∧
      fourierAfter ∅ ((List.range m).flatMap (timeCells (n := n))) =
        Finset.univ.filter fun a : Fin n ↦ 2 * (a : ℕ) < m := by
    intro m
    induction m with
    | zero => exact ⟨trivial, by simp [fourierAfter]⟩
    | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, isGateOrder_append,
        fourierAfter_append, ih.2]
      exact ⟨⟨ih.1, (isGateOrder_timeCells m).1⟩, (isGateOrder_timeCells m).2⟩
  exact (key _).1

/-! ### The layers -/

private theorem disjoint_cell_of_time {b b' : (geometry n).Cell} (hb : b ∈ coreCells n)
    (hb' : b' ∈ coreCells n) (ht : cellTime b = cellTime b') (hne : b ≠ b') :
    Disjoint ((geometry n).cell b) ((geometry n).cell b') := by
  refine Finset.disjoint_left.mpr fun v hv hv' ↦ hne ?_
  rcases b with a | ⟨⟨j, i⟩, h⟩ <;> rcases b' with a' | ⟨⟨j', i'⟩, h'⟩ <;>
    simp only [coreCells, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.lt_def] at hb hb' <;>
    simp only [Finset.mem_singleton, Finset.mem_union, Fin.ext_iff]
      at hv hv' <;>
    simp only [cellTime] at ht
  · exact congrArg _ (Fin.ext (by omega))
  · exfalso; change (i' : ℕ) < j' at hb'; omega
  · exfalso; change (i : ℕ) < j at hb; omega
  · change (i : ℕ) < j at hb
    change (i' : ℕ) < j' at hb'
    have h₁ : (j : ℕ) = j' := by omega
    have h₂ : (i : ℕ) = i' := by omega
    exact congrArg Sum.inr (Subtype.ext (Prod.ext (Fin.ext h₁) (Fin.ext h₂)))

private theorem timeCells_pairwiseDisjoint (t : ℕ) :
    (((timeCells (n := n) t).toFinset : Finset (geometry n).Cell) : Set (geometry n).Cell
      ).PairwiseDisjoint (geometry n).cell := by
  intro b hb b' hb' hne
  rw [Finset.mem_coe, List.mem_toFinset, mem_timeCells] at hb hb'
  exact disjoint_cell_of_time hb.1 hb'.1 (hb.2.trans hb'.2.symm) hne

private theorem swapCells_pairwiseDisjoint :
    (((swapCells n).toFinset : Finset (geometry n).Cell) : Set (geometry n).Cell
      ).PairwiseDisjoint (geometry n).cell := by
  intro b hb b' hb' hne
  rw [Finset.mem_coe, List.mem_toFinset, swapCells, List.mem_ofFn] at hb hb'
  obtain ⟨k, rfl⟩ := hb
  obtain ⟨k', rfl⟩ := hb'
  refine Finset.disjoint_left.mpr fun v hv hv' ↦ hne ?_
  simp only [Finset.mem_singleton, Finset.mem_union, Fin.ext_iff,
    Fin.val_rev] at hv hv'
  have hk : (k : ℕ) = k' := by have := k.2; have := k'.2; omega
  rw [Fin.ext hk]

/-- The layer of the gates on a list of cells with pairwise disjoint cells. -/
noncomputable def listLayer (d : ℕ) (L : List (geometry n).Cell)
    (h : ((L.toFinset : Finset (geometry n).Cell) : Set (geometry n).Cell).PairwiseDisjoint
      (geometry n).cell) : Layer (geometry n) KrausGate (Qudits (Fin n) d) (Qudits (Fin n) d) :=
  Layer.ofCells L.toFinset h fun c ↦ qftGate d c.1

private theorem kraus_listLayer {L : List (geometry n).Cell} (hnd : L.Nodup)
    (h : ((L.toFinset : Finset (geometry n).Cell) : Set (geometry n).Cell).PairwiseDisjoint
      (geometry n).cell) (i : (listLayer d L h).Index) :
    (listLayer d L h).kraus KrausGate.ev i = (L.map (gateOp d)).reverse.prod := by
  let l : List L.toFinset := L.reverse.attach.map fun c ↦
    ⟨c.1, List.mem_toFinset.mpr (List.mem_reverse.mp c.2)⟩
  have hl : l.Nodup := (List.nodup_reverse.mpr hnd).attach.map fun c c' e ↦ by
    apply Subtype.ext
    simpa using e
  have hall : ∀ c, c ∈ l := fun c ↦ List.mem_map.mpr
    ⟨⟨c.1, List.mem_reverse.mpr (List.mem_toFinset.mp c.2)⟩, List.mem_attach _ _, rfl⟩
  refine (Layer.kraus_ofCells KrausGate.ev _ h _ l hl hall i).trans ?_
  rw [List.map_map]
  change (L.reverse.attach.map fun c ↦ (gateOp d) c.1).prod = _
  rw [List.attach_map_val, List.map_reverse]

/-- The gates at time `t`. -/
noncomputable def timeLayer (d t : ℕ) :
    Layer (geometry n) KrausGate (Qudits (Fin n) d) (Qudits (Fin n) d) :=
  listLayer d (timeCells t) (timeCells_pairwiseDisjoint t)

/-- The swaps of the qudits `k` and `n - 1 - k`, for `k < n / 2`. -/
noncomputable def swapLayer (d n : ℕ) :
    Layer (geometry n) KrausGate (Qudits (Fin n) d) (Qudits (Fin n) d) :=
  listLayer d (swapCells n) swapCells_pairwiseDisjoint

/-- The layers of the Fourier transform in linear depth: the gates at the times
`0, …, 2n - 2`, then the swaps. -/
noncomputable def parLayers (d n : ℕ) :
    List (Layer (geometry n) KrausGate (Qudits (Fin n) d) (Qudits (Fin n) d)) :=
  (List.range (2 * n - 1)).map (timeLayer d) ++ [swapLayer d n]

/-- The Fourier transform in `2n` layers. -/
noncomputable def qftPar (d n : ℕ) :
    Circuit (geometry n) KrausGate (Qudits (Fin n) d) (Qudits (Fin n) d) :=
  Circuit.seq (parLayers d n)

private theorem reverse_prod_flatMap (f : ℕ → List (geometry n).Cell) :
    (l : List ℕ) → (l.map fun t ↦ ((f t).map (gateOp d)).reverse.prod).reverse.prod =
      ((l.flatMap f).map (gateOp d)).reverse.prod
  | [] => rfl
  | t :: l => by
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton,
      reverse_prod_flatMap f l, List.flatMap_cons, List.map_append, List.reverse_append,
      List.prod_append]

/-- The Fourier transform in linear depth has the matrix of the Fourier transform. -/
theorem kraus_qftPar (d n : ℕ) (p : (qftPar d n).Index) :
    (qftPar d n).kraus KrausGate.ev p = dft d n := by
  have h : List.Forall₂
      (fun (M : Layer (geometry n) KrausGate (Qudits (Fin n) d) (Qudits (Fin n) d)) U ↦
        ∀ i, M.kraus KrausGate.ev i = U) (parLayers d n)
      ((List.range (2 * n - 1)).map (fun t ↦ ((timeCells t).map (gateOp d)).reverse.prod) ++
        [((swapCells n).map (gateOp d)).reverse.prod]) := by
    refine List.rel_append ?_ (List.Forall₂.cons (kraus_listLayer swapCells_nodup _) .nil)
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun t _ ↦ kraus_listLayer (timeCells_nodup t) _
  rw [show (qftPar d n).kraus KrausGate.ev p = _ from Circuit.kraus_seq KrausGate.ev h p,
    List.reverse_append, List.prod_append, List.reverse_singleton, List.prod_singleton,
    reverse_prod_flatMap, ← List.prod_append, ← List.reverse_append, ← List.map_append,
    ← parCells, prod_gateOp_eq_dft isGateOrder_parCells parCells_nodup toFinset_parCells]

theorem isUnbranched_qftPar (d n : ℕ) : (qftPar d n).IsUnbranched :=
  Circuit.isUnbranched_seq _

theorem forall_isUnitary_qftPar (d n : ℕ) :
    (qftPar d n).Forall KrausGate.ev KrausFamily.IsUnitary := by
  refine Circuit.forall_seq _ _ fun M hM ↦ ?_
  simp only [parLayers, List.mem_append, List.mem_map, List.mem_singleton] at hM
  obtain ⟨t, -, rfl⟩ | rfl := hM <;>
    exact Layer.forall_ofCells _ (KrausFamily.isUnitary_single (one_mem _)) _ _ _
      fun c ↦ isUnitary_qftGate c.1

private theorem gateCount_listLayer {L : List (geometry n).Cell} (hnd : L.Nodup)
    (h : ((L.toFinset : Finset (geometry n).Cell) : Set (geometry n).Cell).PairwiseDisjoint
      (geometry n).cell) : (listLayer d L h).gateCount = L.length := by
  have hcost : ∀ b : (geometry n).Cell, (geometry n).cost b = 1 := fun b ↦ by
    rcases b with a | p <;> rfl
  rw [Layer.gateCount_eq_sum]
  change ∑ b ∈ L.toFinset, (geometry n).cost b = _
  rw [Finset.sum_congr rfl fun b _ ↦ hcost b, Finset.sum_const, smul_eq_mul, mul_one,
    List.toFinset_card_of_nodup hnd]

/-- The Fourier transform in linear depth uses the gates of `qft d n`. -/
theorem gateCount_qftPar (d n : ℕ) : (qftPar d n).gateCount = (qft d n).gateCount := by
  rw [gateCount_qft d, ← length_seqCells, ← List.toFinset_card_of_nodup seqCells_nodup,
    toFinset_seqCells, ← toFinset_parCells, List.toFinset_card_of_nodup parCells_nodup,
    qftPar, Circuit.gateCount, Circuit.total_seq _ _ fun M hM ↦ by
      simp only [parLayers, List.mem_append, List.mem_map, List.mem_singleton] at hM
      obtain ⟨t, -, rfl⟩ | rfl := hM <;>
        exact Layer.nonempty_index_ofCells _ _ _ fun _ ↦ ⟨()⟩]
  simp only [parLayers, List.map_append, List.map_map, List.map_singleton, List.sum_append,
    List.sum_singleton, Function.comp_def]
  have hT : ∀ t, (timeLayer (n := n) d t).gateCount = (timeCells t).length :=
    fun t ↦ gateCount_listLayer (timeCells_nodup t) _
  have hS : (swapLayer d n).gateCount = (swapCells n).length :=
    gateCount_listLayer swapCells_nodup _
  rw [List.map_congr_left fun t _ ↦ hT t, hS, parCells,
    List.length_flatMap, swapCells, List.length_ofFn]

theorem depth_qftPar_le (d n : ℕ) : (qftPar d n).depth ≤ 2 * n := by
  refine (Circuit.depth_seq_le _).trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [parLayers, Layer.depth, swapLayer, listLayer, Layer.ofCells, swapCells]
  calc ((parLayers d n).map Layer.depth).sum ≤ ((parLayers d n).map fun _ ↦ 1).sum :=
        List.sum_le_sum fun M _ ↦ Layer.depth_le_one M
    _ ≤ 2 * n := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul, mul_one, parLayers, List.length_append,
        List.length_map, List.length_range, List.length_singleton]
      omega

end Qudit

namespace Qubit

/-- The quantum Fourier transform on `n` qubits in `2n` layers. -/
noncomputable abbrev qftPar (n : ℕ) :
    Circuit (geometry n) KrausGate (Qudits (Fin n) 2) (Qudits (Fin n) 2) :=
  Qudit.qftPar 2 n

theorem kraus_qftPar (n : ℕ) (p : (qftPar n).Index) : (qftPar n).kraus KrausGate.ev p = dft n :=
  Qudit.kraus_qftPar 2 n p

theorem gateCount_qftPar (n : ℕ) : (qftPar n).gateCount = (qft n).gateCount :=
  Qudit.gateCount_qftPar 2 n

theorem depth_qftPar_le (n : ℕ) : (qftPar n).depth ≤ 2 * n :=
  Qudit.depth_qftPar_le 2 n

end Qubit

end QuantumCircuit
