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

/-! ### The branches and the number of calls -/

variable {t m}

/-- The local property of having a unique Kraus index. -/
private abbrev UniqueIndex {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (K : KrausFamily α β) : Prop :=
  Nonempty (Unique K.Index)

private theorem uniqueIndex_relabel {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (K : KrausFamily α β) {ι : Type} [Fintype ι] (u : ι ≃ K.Index)
    (h : UniqueIndex K) : UniqueIndex (⟨ι, fun i ↦ K.op (u i)⟩ : KrausFamily α β) :=
  haveI := h.some
  ⟨u.unique⟩

private theorem uniqueIndex_single {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (V : Matrix β α ℂ) : UniqueIndex (KrausFamily.single V) :=
  ⟨inferInstanceAs (Unique Unit)⟩

private theorem forall_uniqueIndex_hadamards (ev : Interpretation (Gate t m)) :
    ∀ L ∈ (List.finRange t).map (hadamardLayer t m), L.Forall ev UniqueIndex := by
  intro L hL
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hL
  exact Layer.forall_single ev (uniqueIndex_single 1) _ _ ⟨inferInstanceAs (Unique Unit)⟩

private theorem mem_queryLayers {L : Layer (geometry t) (Gate t m) (system t m) (system t m)}
    (hL : L ∈ (List.finRange t).reverse.flatMap fun j : Fin t ↦
      List.replicate (2 ^ (t - 1 - (j : ℕ))) (queryLayer t m j)) :
    ∃ j, L = queryLayer t m j := by
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hL
  exact ⟨j, List.eq_of_mem_replicate hj⟩

private theorem forall_uniqueIndex_queries (ev : Interpretation (Gate t m)) :
    ∀ L ∈ (List.finRange t).reverse.flatMap (fun j : Fin t ↦
      List.replicate (2 ^ (t - 1 - (j : ℕ))) (queryLayer t m j)), L.Forall ev UniqueIndex := by
  intro L hL
  obtain ⟨j, rfl⟩ := mem_queryLayers hL
  exact Layer.forall_single ev (uniqueIndex_single 1) _ _ ⟨inferInstanceAs (Unique Unit)⟩

private theorem forall_uniqueIndex_adjoint {X Y : Fin t → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    {L : Layer (Qubit.geometry t) KrausGate X Y} (h : L.Forall KrausGate.ev UniqueIndex) :
    L.adjoint.Forall KrausGate.ev UniqueIndex :=
  ⟨fun b ↦ h.1 b, fun s ↦ h.2 s⟩

private theorem forall_uniqueIndex_qftInv (V : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ) :
    (qftInv t m).Forall (Interpretation.sum KrausGate.ev (Oracle.ev V)) UniqueIndex := by
  refine Circuit.forall_mapGate _ _ (GateMorphism.isCompatible_inl _ _)
    (fun K _ _ u hK ↦ uniqueIndex_relabel K u hK) ?_
  refine Circuit.forall_mapSites _ _ _ _ (KrausGate.isCompatible_transport _ _)
    (fun K u _ _ hK ↦ ⟨@Equiv.unique _ _ hK.some u⟩) (uniqueIndex_single 1) ?_
  refine Circuit.forall_seq _ _ fun L hL ↦ ?_
  rw [List.mem_map] at hL
  obtain ⟨L, hL, rfl⟩ := hL
  rw [List.mem_reverse, gateLayers, List.mem_map] at hL
  obtain ⟨b, -, rfl⟩ := hL
  exact forall_uniqueIndex_adjoint
    (Layer.forall_single _ (uniqueIndex_single 1) b _ (uniqueIndex_single _))

private theorem forall_uniqueIndex_unitary (V : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ) :
    (unitary t m).Forall (Interpretation.sum KrausGate.ev (Oracle.ev V)) UniqueIndex :=
  ((Circuit.forall_seq _ _ (forall_uniqueIndex_hadamards _)).comp _
    (Circuit.forall_seq _ _ (forall_uniqueIndex_queries _))).comp _
    (forall_uniqueIndex_qftInv V)

/-- The unitary part has one branch. -/
private theorem unique_index_unitary : Nonempty (Unique (unitary t m).Index) :=
  Circuit.nonempty_unique_index _ (forall_uniqueIndex_unitary 0)

private theorem isUnbranched_unitary : (unitary t m).IsUnbranched :=
  ((Circuit.isUnbranched_seq _).comp (Circuit.isUnbranched_seq _)).comp
    (Circuit.isUnbranched_mapGate _ _
      (Circuit.isUnbranched_mapSites _ _ _ _ (Circuit.isUnbranched_seq _)))

/-- A cost vanishing on every layer vanishes on every circuit. -/
private theorem total_eq_zero {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
    {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]
    {f : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ} (hf : ∀ ⦃X Y : S → Type⦄ (L : Layer Γ G X Y),
      f L = 0) : {X Z : S → Type} → (c : Circuit Γ G X Z) → c.total f = 0
  | _, _, Circuit.done _ => rfl
  | _, _, Circuit.step L next => by
    change f L + Finset.univ.sup (fun i ↦ (next i).total f) = 0
    simp only [hf L, total_eq_zero hf, zero_add]
    exact Nat.eq_zero_of_le_zero (Finset.sup_le fun _ _ ↦ le_rfl)

private theorem forall_uniqueIndex_seqHadamards (ev : Interpretation (Gate t m)) :
    (Circuit.seq ((List.finRange t).map (hadamardLayer t m))).Forall ev UniqueIndex :=
  Circuit.forall_seq _ _ (forall_uniqueIndex_hadamards ev)

private theorem forall_uniqueIndex_seqQueries (ev : Interpretation (Gate t m)) :
    (Circuit.seq ((List.finRange t).reverse.flatMap fun j : Fin t ↦
      List.replicate (2 ^ (t - 1 - (j : ℕ))) (queryLayer t m j))).Forall ev UniqueIndex :=
  Circuit.forall_seq _ _ (forall_uniqueIndex_queries ev)

private theorem sum_two_pow_sub (t : ℕ) : ∑ j : Fin t, 2 ^ (t - 1 - (j : ℕ)) = 2 ^ t - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ 2 ^ (t - 1 - j)), Finset.sum_range_reflect
    (fun j ↦ 2 ^ j) t, Nat.geomSum_eq le_rfl, Nat.div_one]

private theorem callCount_ndrec_inl {X Y : Fin t ⊕ Unit → Type} {D D' : Finset (Fin t ⊕ Unit)}
    (hD : D = D') (g : KrausGate D X Y) :
    Oracle.callCount (Eq.ndrec (motive := fun D ↦ Gate t m D X Y) (Sum.inl g) hD) = 0 := by
  subst hD; rfl

/-- Phase estimation calls the oracle `∑_{j < t} 2^{t-1-j} = 2^t - 1` times. -/
theorem queryCount_circuit : (circuit t m).queryCount = 2 ^ t - 1 := by
  have hne : ∀ {X Z : Fin t ⊕ Unit → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      {c : Circuit (geometry t) (Gate t m) X Z},
      c.Forall (Interpretation.sum KrausGate.ev (Oracle.ev 0)) UniqueIndex → Nonempty c.Index :=
    fun h ↦ ⟨(Circuit.nonempty_unique_index _ h).some.default⟩
  have hseq : ∀ {Ls : List (Layer (geometry t) (Gate t m) (system t m) (system t m))},
      (∀ L ∈ Ls, L.Forall (Interpretation.sum KrausGate.ev (Oracle.ev 0)) UniqueIndex) →
      ∀ L ∈ Ls, Nonempty L.Index := fun h L hL ↦
    ⟨(Circuit.nonempty_unique_index (c := .step L fun _ ↦ .done _) _
      ⟨h L hL, fun _ ↦ trivial⟩).some.default.1⟩
  rw [Circuit.queryCount, circuit,
    Circuit.total_comp_of_isUnbranched _ isUnbranched_unitary (hne (forall_uniqueIndex_unitary 0)),
    unitary, Circuit.total_comp_of_isUnbranched _
      ((Circuit.isUnbranched_seq _).comp (Circuit.isUnbranched_seq _))
      (hne ((forall_uniqueIndex_seqHadamards _).comp _ (forall_uniqueIndex_seqQueries _))),
    Circuit.total_comp_of_isUnbranched _ (Circuit.isUnbranched_seq _)
      (hne (forall_uniqueIndex_seqHadamards _)),
    Circuit.total_seq _ _ (hseq (forall_uniqueIndex_hadamards _)),
    Circuit.total_seq _ _ (hseq (forall_uniqueIndex_queries _))]
  have hq : (qftInv t m).total (fun _ _ L ↦ L.cellCost fun _ _ _ g ↦ Oracle.callCount g) = 0 :=
    Nat.eq_zero_of_le_zero ((Circuit.total_mapLayers_le _ (fun _ _ _ ↦ 0) _
      (fun _ _ _ _ _ _ L ↦ by
        unfold Layer.cellCost
        exact Nat.le_zero.mpr (Finset.sum_eq_zero fun _ _ ↦ callCount_ndrec_inl _ _)) _).trans
        (total_eq_zero (fun _ _ _ ↦ rfl) _).le)
  have hm : (Circuit.step (measureLayer t m) fun _ ↦ Circuit.done (system t m)).total
      (fun _ _ L ↦ L.cellCost fun _ _ _ g ↦ Oracle.callCount g) = 0 := by
    change (measureLayer t m).cellCost _ + Finset.univ.sup (fun _ ↦ 0) = 0
    simp [Layer.cellCost, measureLayer]
  have hH : (((List.finRange t).map (hadamardLayer t m)).map fun L ↦
      L.cellCost fun _ _ _ g ↦ Oracle.callCount g).sum = 0 := by
    refine List.sum_eq_zero fun x hx ↦ ?_
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hL
    exact Layer.cellCost_single _ _ _
  have hQ : (((List.finRange t).reverse.flatMap fun j : Fin t ↦
      List.replicate (2 ^ (t - 1 - (j : ℕ))) (queryLayer t m j)).map fun L ↦
        L.cellCost fun _ _ _ g ↦ Oracle.callCount g).sum = 2 ^ t - 1 := by
    rw [List.map_congr_left fun L hL ↦ show L.cellCost (fun _ _ _ g ↦ Oracle.callCount g) = 1 by
      obtain ⟨j, rfl⟩ := mem_queryLayers hL
      exact Layer.cellCost_single _ _ _, List.map_const', List.sum_replicate, smul_eq_mul,
      mul_one, List.length_flatMap, List.map_reverse, List.sum_reverse, ← sum_two_pow_sub t, Fin.sum_univ_def]
    simp only [List.length_replicate]
  rw [hq, hm, hH, hQ, zero_add, add_zero, add_zero]

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
