/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Algorithm.QFT
import QICLean.Circuit.Core.Oracle
import QICLean.Circuit.Core.Outcome
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

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
open scoped Kronecker
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
noncomputable abbrev qftInv : Circuit (geometry t) (Gate t m) (system t m) (system t m) :=
  ((Circuit.seqAdjoint (gateLayers (seqCells t ++ swapCells t))).mapSites
    (Equiv.refl (Fin t ⊕ Unit)) (fun _ : Unit ↦ Fin m) (geometryHom t)
    (KrausGate.transport _ _)).mapGate (Geometry.Hom.refl _) GateMorphism.inl

/-- The unitary part of phase estimation (Nielsen–Chuang, Fig. 5.2 followed by the inverse
Fourier transform): the Hadamard gates, the controlled calls `U^{2^{t-1-j}}` for
`j = t - 1, …, 0`, and the inverse Fourier transform. -/
noncomputable abbrev unitary : Circuit (geometry t) (Gate t m) (system t m) (system t m) :=
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
noncomputable abbrev circuit : Circuit (geometry t) (Gate t m) (system t m) (system t m) :=
  (unitary t m).comp (.step (measureLayer t m) fun _ ↦ .done _)

/-- The outcomes of the measurement of the control register. -/
def measured (i : (measureLayer t m).Index) : Config (Q t) :=
  fun j ↦ i.2 ⟨.inl j, by simp [measureLayer]⟩

/-- The measured integer of a branch: the outcomes of the measurement of the control register,
the qubit `0` most significant. -/
noncomputable def readout (p : (circuit t m).Index) : Fin (2 ^ t) :=
  encode t (measured t m
    (((unitary t m).compIndexEquiv _ p).2 : Σ _ : (measureLayer t m).Index, Unit).1)

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

/-! ### The state along the circuit -/

/-- Products of matrices along a list, the first on the right, applied to a vector. -/
private theorem reverse_prod_mulVec {ι n : Type} [Fintype n] [DecidableEq n] (V : ι → Matrix n n ℂ)
    (l : List ι) (v : n → ℂ) : (l.map V).reverse.prod *ᵥ v = l.foldl (fun w a ↦ V a *ᵥ w) v := by
  induction l generalizing v with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, ← mulVec_mulVec,
      ih, List.foldl_cons]

/-- The state `f(x) u(a)` of the register, `x` the control register and `a` the target. -/
private def tensorState (u : Fin m → ℂ) (f : Config (Q t) → ℂ) : Config (system t m) → ℂ :=
  fun σ ↦ f (control t m σ) * u (σ (.inr ()))

/-- The configuration with the control register `x` and the target `a`. -/
private def glue (x : Config (Q t)) (a : Fin m) : Config (system t m)
  | .inl i => x i
  | .inr () => a

private theorem input_eq (u : Fin m → ℂ) :
    input t m u = tensorState u fun x ↦ if x = 0 then 1 else 0 :=
  rfl

/-- The configuration glued from `a` on a region and `σ` elsewhere, read on the register. -/
private theorem cut_eq_glue {D : Finset (Fin t ⊕ Unit)} (σ : Config (system t m))
    (a : RegionConfig (system t m) D) (x : Config (Q t)) (b : Fin m)
    (hx : ∀ i, (cutEquiv (system t m) D).symm (a, (cutEquiv (system t m) D σ).2) (.inl i) = x i)
    (hb : (cutEquiv (system t m) D).symm (a, (cutEquiv (system t m) D σ).2) (.inr ()) = b) :
    (cutEquiv (system t m) D).symm (a, (cutEquiv (system t m) D σ).2) = glue x b := by
  funext s
  rcases s with i | ⟨⟩
  · exact hx i
  · exact hb

/-- The control register after the Hadamard gates on the qubits of `A`. -/
private noncomputable def hadamardState (A : Finset (Fin t)) (x : Config (Q t)) : ℂ :=
  invSqrtTwo ^ A.card * if ∀ j ∉ A, x j = 0 then 1 else 0

private theorem hadamard_mulVec (u : Fin m → ℂ) {A : Finset (Fin t)} {j : Fin t} (hj : j ∉ A) :
    place {Sum.inl j} (hadamard.submatrix (siteEquiv (system t m) (.inl j))
      (siteEquiv (system t m) (.inl j))) *ᵥ tensorState u (hadamardState A) =
      tensorState u (hadamardState (insert j A)) := by
  funext σ
  rw [place_mulVec_apply, ← (siteEquiv (system t m) (.inl j)).symm.sum_comp]
  have hcut : ∀ b : Fin 2, (cutEquiv (system t m) {Sum.inl j}).symm
      ((siteEquiv (system t m) (.inl j)).symm b, (cutEquiv (system t m) {Sum.inl j} σ).2) =
      glue (Function.update (control t m σ) j b) (σ (.inr ())) := fun b ↦ by
    refine cut_eq_glue _ _ _ _ (fun i ↦ ?_) ?_
    · by_cases hij : i = j
      · subst hij
        rw [cutEquiv_symm_apply_mem _ _ (Finset.mem_singleton_self _)]
        exact (Function.update_self i b (control t m σ)).symm
      · rw [cutEquiv_symm_apply_not_mem _ _ (by simpa using hij)]
        exact (Function.update_of_ne hij b (control t m σ)).symm
    · rw [cutEquiv_symm_apply_not_mem _ _ (by simp)]
      rfl
  change ∑ b : Fin 2, hadamard (σ (.inl j)) b * tensorState u (hadamardState A)
    ((cutEquiv (system t m) {Sum.inl j}).symm
      ((siteEquiv (system t m) (.inl j)).symm b, (cutEquiv (system t m) {Sum.inl j} σ).2)) = _
  simp only [hcut, Fin.sum_univ_two, tensorState]
  change hadamard (control t m σ j) 0 * (hadamardState A (Function.update (control t m σ) j 0) *
      u (σ (.inr ()))) + hadamard (control t m σ j) 1 *
      (hadamardState A (Function.update (control t m σ) j 1) * u (σ (.inr ()))) = _
  have h1 : ¬ ∀ i ∉ A, Function.update (control t m σ) j 1 i = 0 :=
    fun h ↦ by simpa using h j hj
  have h0 : (∀ i ∉ A, Function.update (control t m σ) j 0 i = 0) ↔
      ∀ i ∉ insert j A, control t m σ i = 0 := by
    refine ⟨fun h i hi ↦ ?_, fun h i hi ↦ ?_⟩
    · rw [Finset.mem_insert, not_or] at hi
      simpa [Function.update_of_ne hi.1] using h i hi.2
    · by_cases hij : i = j
      · subst hij; simp
      · rw [Function.update_of_ne hij]
        exact h i (by simp [hij, hi])
  have hH : hadamard (control t m σ j) 0 = invSqrtTwo := by
    change invSqrtTwo * (-1) ^ (((control t m σ j : Fin 2) : ℕ) * 0) = _
    rw [mul_zero, pow_zero, mul_one]
  simp only [hadamardState, h1, h0, ite_false, mul_zero,
    Finset.card_insert_of_notMem hj, hH, pow_succ]
  ring

private theorem foldl_hadamard (u : Fin m → ℂ) :
    ∀ (l : List (Fin t)) (A : Finset (Fin t)), l.Nodup → (∀ j ∈ l, j ∉ A) →
      l.foldl (fun w j ↦ place {Sum.inl j} (hadamard.submatrix (siteEquiv (system t m) (.inl j))
        (siteEquiv (system t m) (.inl j))) *ᵥ w) (tensorState u (hadamardState A)) =
        tensorState u (hadamardState (A ∪ l.toFinset))
  | [], A, _, _ => by simp
  | j :: l, A, hnd, hA => by
    rw [List.foldl_cons, hadamard_mulVec u (hA j List.mem_cons_self)]
    rw [List.nodup_cons] at hnd
    rw [foldl_hadamard u l (insert j A) hnd.2 fun i hi ↦ by
      rw [Finset.mem_insert, not_or]
      exact ⟨fun e ↦ hnd.1 (e ▸ hi), hA i (List.mem_cons_of_mem j hi)⟩]
    congr 2
    ext i
    simp

/-- The control qubit `j` and the target are distinct sites. -/
private theorem inlNeInr (j : Fin t) : (Sum.inl j : Fin t ⊕ Unit) ≠ .inr () :=
  Sum.inl_ne_inr

/-- A call controlled by the qubit `j` multiplies by the eigenvalue when the qubit is `1`. -/
private theorem query_mulVec {U : Matrix (Fin m) (Fin m) ℂ} {u : Fin m → ℂ} {c : ℂ}
    (hu : U *ᵥ u = c • u) (j : Fin t) (f : Config (Q t) → ℂ) :
    place ({Sum.inl j} ∪ {Sum.inr ()}) ((controlled U).submatrix
      (pairEquiv (system t m) (inlNeInr j)) (pairEquiv (system t m) (inlNeInr j))) *ᵥ
      tensorState u f = tensorState u fun x ↦ c ^ (x j : ℕ) * f x := by
  funext σ
  rw [place_mulVec_apply, ← (pairEquiv (system t m) (inlNeInr j)).symm.sum_comp]
  have hcut : ∀ q : system t m (.inl j) × system t m (.inr ()),
      (cutEquiv (system t m) ({Sum.inl j} ∪ {Sum.inr ()})).symm
      ((pairEquiv (system t m) (inlNeInr j)).symm q,
        (cutEquiv (system t m) ({Sum.inl j} ∪ {Sum.inr ()}) σ).2) =
      glue (Function.update (control t m σ) j q.1) q.2 := fun q ↦ by
    refine cut_eq_glue _ _ _ _ (fun i ↦ ?_) ?_
    · by_cases hij : i = j
      · subst hij
        rw [cutEquiv_symm_apply_mem _ _ (by simp)]
        exact (pairEquiv_symm_apply_left (system t m) Sum.inl_ne_inr q).trans
          (Function.update_self i q.1 (control t m σ)).symm
      · rw [cutEquiv_symm_apply_not_mem _ _ (by simp [hij])]
        exact (Function.update_of_ne hij q.1 (control t m σ)).symm
    · rw [cutEquiv_symm_apply_mem _ _ (by simp)]
      exact pairEquiv_symm_apply_right (system t m) Sum.inl_ne_inr q
  have hq : ∀ q : system t m (.inl j) × system t m (.inr ()), (controlled U).submatrix (pairEquiv (system t m) (inlNeInr j))
      (pairEquiv (system t m) (inlNeInr j)) (fun v ↦ σ v)
        ((pairEquiv (system t m) (inlNeInr j)).symm q) =
      controlled U (control t m σ j, σ (.inr ())) q := fun q ↦
    congrArg (controlled U (control t m σ j, σ (.inr ())))
      (Equiv.apply_symm_apply (pairEquiv (system t m) (inlNeInr j)) q)
  simp only [hq, hcut, tensorState]
  change ∑ q : Fin 2 × Fin m, controlled U (control t m σ j, σ (.inr ())) q *
    (f (Function.update (control t m σ) j q.1) * u q.2) =
      c ^ (control t m σ j : ℕ) * f (control t m σ) * u (σ (.inr ()))
  have hU : ∀ a, ∑ b, U a b * u b = c * u a := fun a ↦ by
    simpa [mulVec, dotProduct] using congrFun hu a
  generalize control t m σ = x
  refine (?_ : ∀ a : Fin m, ∑ q : Fin 2 × Fin m, controlled U (x j, a) q *
    (f (Function.update x j q.1) * u q.2) = c ^ (x j : ℕ) * f x * u a) _
  intro a
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases Fin.exists_fin_two.mp ⟨x j, rfl⟩ with h | h
  · have hx : Function.update x j 0 = x := h ▸ Function.update_eq_self j x
    simp only [Qubit.controlled_apply, h, hx, ite_true, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
      ite_false, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul,
      one_apply, ite_mul, mul_comm (f x), ← mul_assoc]
    rw [Finset.sum_ite_eq]
    simp
  · have hx : Function.update x j 1 = x := h ▸ Function.update_eq_self j x
    simp only [Qubit.controlled_apply, h, hx, ite_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
      ite_false, zero_mul, Finset.sum_const_zero, zero_add, Fin.val_one, pow_one]
    rw [show ∑ b, U a b * (f x * u b) = f x * ∑ b, U a b * u b by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ ↦ by ring, hU]
    ring

/-- The outcomes of the measurement layer are the configurations of the control register. -/
private def measuredEquiv : (measureLayer t m).Index ≃ Config (Q t) where
  toFun := measured t m
  invFun x := (fun b ↦ absurd b.2 (Finset.notMem_empty _), fun
    | ⟨.inl j, _⟩ => x j
    | ⟨.inr _, _⟩ => ())
  left_inv i := by
    refine Prod.ext (funext fun b ↦ absurd b.2 (Finset.notMem_empty _)) (funext fun s ↦ ?_)
    rcases s with ⟨j | u, h⟩
    · rfl
    · rfl
  right_inv x := rfl

private theorem measure_entry (ev : Interpretation (Gate t m)) (i : (measureLayer t m).Index)
    (y x : Config (system t m)) : (measureLayer t m).kraus ev i y x =
      if y = x ∧ control t m y = measured t m i then 1 else 0 := by
  have hcells : ∀ b : (measureLayer t m).cells, False := fun b ↦ Finset.notMem_empty _ b.2
  rw [Layer.kraus, Fintype.prod_eq_one _ fun b ↦ (hcells b).elim, one_mul]
  have hfree : ∀ v, v ∉ (measureLayer t m).cells.biUnion (geometry t).cell := by
    simp [measureLayer]
  have hinl : ∀ j, ((measureLayer t m).onsite ⟨.inl j, hfree _⟩).op (i.2 ⟨.inl j, hfree _⟩)
      (y (.inl j)) (x (.inl j)) = if measured t m i j = control t m y j ∧
        measured t m i j = control t m x j then 1 else 0 := fun j ↦
    Matrix.single_apply ..
  have hinr : ((measureLayer t m).onsite ⟨.inr (), hfree _⟩).op (i.2 ⟨.inr (), hfree _⟩)
      (y (.inr ())) (x (.inr ())) = if y (.inr ()) = x (.inr ()) then 1 else 0 :=
    one_apply
  split_ifs with h
  · obtain ⟨rfl, hy⟩ := h
    refine Fintype.prod_eq_one _ fun s ↦ ?_
    obtain ⟨j | ⟨⟩, hs⟩ := s
    · rw [hinl, ite_eq_left (And.intro (congrFun hy.symm j) (congrFun hy.symm j))]
    · rw [hinr, ite_eq_left rfl]
  · refine Finset.prod_eq_zero_iff.mpr ?_
    by_cases hyx : y = x
    · subst hyx
      have : ∃ j, measured t m i j ≠ control t m y j := by
        by_contra hc
        push Not at hc
        exact h ⟨rfl, funext fun j ↦ (hc j).symm⟩
      obtain ⟨j, hj⟩ := this
      exact ⟨⟨.inl j, hfree _⟩, Finset.mem_univ _, by rw [hinl, ite_eq_right fun e ↦ hj e.1]⟩
    · obtain ⟨v, hv⟩ := Function.ne_iff.mp hyx
      rcases v with j | ⟨⟩
      · exact ⟨⟨.inl j, hfree _⟩, Finset.mem_univ _, by
          rw [hinl, ite_eq_right fun e ↦ hv (e.1.symm.trans e.2)]⟩
      · exact ⟨⟨.inr (), hfree _⟩, Finset.mem_univ _, by rw [hinr, ite_eq_right hv]⟩

private theorem measure_mulVec (ev : Interpretation (Gate t m)) (i : (measureLayer t m).Index)
    (ψ : Config (system t m) → ℂ) :
    (measureLayer t m).kraus ev i *ᵥ ψ =
      fun σ ↦ if control t m σ = measured t m i then ψ σ else 0 := by
  funext σ
  simp only [mulVec, dotProduct, measure_entry, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- A matrix on the control register, tensored with the identity on the target. -/
private theorem kron_one_mulVec (A : Matrix (Config (Q t)) (Config (Q t)) ℂ) (u : Fin m → ℂ) (f : Config (Q t) → ℂ) :
    (A ⊗ₖ (1 : Matrix (Unit → Fin m) (Unit → Fin m) ℂ)).submatrix
      (extendConfigEquiv (Equiv.refl (Fin t ⊕ Unit)) (fun _ : Unit ↦ Fin m) (Q t))
      (extendConfigEquiv (Equiv.refl (Fin t ⊕ Unit)) (fun _ : Unit ↦ Fin m) (Q t)) *ᵥ
        tensorState u f = tensorState u (A *ᵥ f) := by
  set E := extendConfigEquiv (Equiv.refl (Fin t ⊕ Unit)) (fun _ : Unit ↦ Fin m) (Q t)
  have h1 : ∀ τ, control t m τ = (E τ).1 := fun _ ↦ rfl
  have h2 : ∀ τ : Config (system t m), τ (.inr ()) = (E τ).2 () := fun _ ↦ rfl
  funext σ
  simp only [tensorState, mulVec, dotProduct, h1, h2]
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp only [submatrix_apply, Equiv.apply_symm_apply, kroneckerMap_apply, one_apply, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

/-- The amplitude `2^{-t} ∑_{j < 2^t} e^{2πi j (φ - k/2^t)}` of the outcome `k` (Nielsen–Chuang,
eq. (5.24)). -/
noncomputable def amplitude (t : ℕ) (φ : ℝ) (k : Fin (2 ^ t)) : ℂ :=
  (2 ^ t : ℂ)⁻¹ * ∑ j : Fin (2 ^ t), exp (2 * Real.pi * I * j * (φ - k / 2 ^ t))

private theorem dft_conjTranspose_mulVec (φ : ℝ) (y : Config (Q t)) :
    ((dft t)ᴴ *ᵥ fun x ↦ invSqrtTwo ^ t * exp (2 * Real.pi * I * φ) ^ (encode t x : ℕ)) y =
      amplitude t φ (encode t y) := by
  rw [mulVec, dotProduct, amplitude, ← (encode t).symm.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hstar : star (invSqrtTwo ^ t) = invSqrtTwo ^ t := by simp
  simp only [conjTranspose_apply, dft, of_apply, star_mul', hstar, Equiv.apply_symm_apply,
    Complex.star_def, ← Complex.exp_conj, ← Complex.exp_nat_mul]
  rw [mul_mul_mul_comm, ← Complex.exp_add, ← mul_pow, invSqrtTwo_mul_self, inv_pow]
  congr 2
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_pow,
    map_natCast]
  ring

private theorem ofReal_sum_norm_sq {n : Type} [Fintype n] (w : n → ℂ) :
    ((∑ y, ‖w y‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
  rw [dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem sum_norm_sq_mulVec {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : Mᴴ * M = 1) (v : n → ℂ) : ∑ y, ‖(M *ᵥ v) y‖ ^ 2 = ∑ x, ‖v x‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [ofReal_sum_norm_sq, ofReal_sum_norm_sq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    hM, one_mulVec]

private theorem norm_invSqrtTwo_sq : ‖invSqrtTwo‖ ^ 2 = 2⁻¹ := by
  rw [invSqrtTwo, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num)]

/-- The probabilities of the outcomes sum to `1`. -/
theorem sum_norm_sq_amplitude (φ : ℝ) : ∑ k, ‖amplitude t φ k‖ ^ 2 = 1 := by
  have hU : ((dft t)ᴴ)ᴴ * (dft t)ᴴ = 1 := by
    rw [conjTranspose_conjTranspose]
    exact mem_unitaryGroup_iff.mp (Qubit.dft_mem_unitaryGroup t)
  rw [← (encode t).sum_comp]
  simp only [← dft_conjTranspose_mulVec]
  rw [sum_norm_sq_mulVec hU]
  have h : ∀ x : Config (Q t), ‖invSqrtTwo ^ t * exp (2 * Real.pi * I * φ) ^ (encode t x : ℕ)‖ ^ 2
      = (2 ^ t : ℝ)⁻¹ := fun x ↦ by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    rw [show ((2 * Real.pi - 0 * 0) * 0 - (2 * 0 + 0 * Real.pi) * 1) * φ -
      ((2 * Real.pi - 0 * 0) * 1 + (2 * 0 + 0 * Real.pi) * 0) * 0 = 0 by ring, Real.exp_zero, one_pow, mul_one, ← pow_mul, mul_comm t 2, pow_mul, norm_invSqrtTwo_sq,
      inv_pow]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ]
  push_cast
  exact mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero)
private theorem foldl_query {U : Matrix (Fin m) (Fin m) ℂ} {u : Fin m → ℂ} {c : ℂ}
    (hu : U *ᵥ u = c • u) : ∀ (l : List (Fin t)) (g : Config (Q t) → ℂ),
      l.foldl (fun w j ↦ place ({Sum.inl j} ∪ {Sum.inr ()}) ((controlled U).submatrix
        (pairEquiv (system t m) (inlNeInr j)) (pairEquiv (system t m) (inlNeInr j))) *ᵥ w)
        (tensorState u g) =
        tensorState u fun x ↦ c ^ (l.map fun j ↦ (x j : ℕ)).sum * g x
  | [], g => by simp
  | j :: l, g => by
    rw [List.foldl_cons, query_mulVec hu, foldl_query hu l]
    congr 1
    funext x
    rw [List.map_cons, List.sum_cons, pow_add]
    ring

/-- The control qubit `j` is called `2^{t-1-j}` times, so the exponents add up to `⟨x⟩`. -/
private theorem sum_queries (x : Config (Q t)) :
    (((List.finRange t).reverse.flatMap fun j : Fin t ↦ List.replicate (2 ^ (t - 1 - (j : ℕ))) j).map
      fun j ↦ (x j : ℕ)).sum = encode t x := by
  have h : ∀ l : List (Fin t), ((l.flatMap fun j : Fin t ↦
      List.replicate (2 ^ (t - 1 - (j : ℕ))) j).map
      fun j ↦ (x j : ℕ)).sum = (l.map fun j ↦ (x j : ℕ) * 2 ^ (t - 1 - (j : ℕ))).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons j l ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_replicate,
        List.sum_replicate, smul_eq_mul, List.map_cons, List.sum_cons, mul_comm]
  rw [h, Qubit.encode_apply, List.map_reverse, List.sum_reverse, ← Fin.sum_univ_def]

private theorem queries_eq :
    ((List.finRange t).reverse.flatMap fun j : Fin t ↦
      List.replicate (2 ^ (t - 1 - (j : ℕ))) (queryLayer t m j)) =
      ((List.finRange t).reverse.flatMap fun j : Fin t ↦
        List.replicate (2 ^ (t - 1 - (j : ℕ))) j).map (queryLayer t m) := by
  rw [List.map_flatMap]
  simp only [List.map_replicate]

/-- The Kraus operator of the inverse Fourier transform on the register. -/
private theorem kraus_qftInv (V : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ)
    (p : (qftInv t m).Index) :
    (qftInv t m).kraus (Interpretation.sum KrausGate.ev (Oracle.ev V)) p =
      ((dft t)ᴴ ⊗ₖ (1 : Matrix (Unit → Fin m) (Unit → Fin m) ℂ)).submatrix
        (extendConfigEquiv (Equiv.refl (Fin t ⊕ Unit)) (fun _ : Unit ↦ Fin m) (Q t))
        (extendConfigEquiv (Equiv.refl (Fin t ⊕ Unit)) (fun _ : Unit ↦ Fin m) (Q t)) := by
  rw [Circuit.kraus_mapGate _ _ (GateMorphism.isCompatible_inl _ _),
    Circuit.kraus_mapSites _ _ _ _ (KrausGate.isCompatible_transport _ _)]
  congr 2
  rw [Circuit.kraus_seqAdjoint (Us := (seqCells t ++ swapCells t).map Qubit.gateOp),
    Qubit.prod_gateOp_eq_dft Qubit.isGateOrder_seqCells Qubit.seqCells_nodup
      Qubit.toFinset_seqCells]
  rw [gateLayers, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun b _ i ↦ Layer.kraus_single KrausGate.ev b (Qubit.qftGate b) i

/-- The unitary part maps `|0…0⟩ ⊗ u` to `(∑ₖ αₖ |k⟩) ⊗ u`. -/
private theorem kraus_unitary_mulVec {U : Matrix (Fin m) (Fin m) ℂ} {u : Fin m → ℂ} {φ : ℝ}
    (huφ : U *ᵥ u = exp (2 * Real.pi * I * φ) • u) (p : (unitary t m).Index) :
    (unitary t m).kraus (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U))) p *ᵥ
      input t m u = tensorState u fun x ↦ amplitude t φ (encode t x) := by
  rw [Circuit.kraus_comp, Circuit.kraus_comp, ← mulVec_mulVec, ← mulVec_mulVec,
    Circuit.kraus_seq_map _ (hadamardLayer t m)
      (fun j ↦ place {Sum.inl j} (hadamard.submatrix (siteEquiv (system t m) (.inl j))
        (siteEquiv (system t m) (.inl j)))) _ (fun j _ i ↦ Layer.kraus_single _ _ _ i),
    reverse_prod_mulVec, input_eq]
  rw [show (tensorState u fun x ↦ if x = 0 then 1 else 0) = tensorState u (hadamardState ∅) by
    congr 1; funext x; simp [hadamardState, funext_iff], foldl_hadamard u _ ∅
      (List.nodup_finRange t) fun _ _ ↦ Finset.notMem_empty _]
  have hq := Circuit.kraus_seq_map (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U)))
    (queryLayer t m) (fun j ↦ place ({Sum.inl j} ∪ {Sum.inr ()}) ((controlled U).submatrix
      (pairEquiv (system t m) (inlNeInr j)) (pairEquiv (system t m) (inlNeInr j))))
    ((List.finRange t).reverse.flatMap fun j : Fin t ↦ List.replicate (2 ^ (t - 1 - (j : ℕ))) j)
    (fun j _ i ↦ Layer.kraus_single _ _ _ i)
  rw [← queries_eq] at hq
  rw [hq, reverse_prod_mulVec, show tensorState u (hadamardState (∅ ∪ (List.finRange t).toFinset))
    = tensorState u fun _ ↦ invSqrtTwo ^ t by
      congr 1; funext x; simp [hadamardState], foldl_query huφ, kraus_qftInv,
    kron_one_mulVec]
  congr 1
  funext y
  rw [← dft_conjTranspose_mulVec]
  congr 1
  funext x
  rw [sum_queries, mul_comm]

/-- The probability of a branch is the squared amplitude of its readout. -/
private theorem prob_eq {U : Matrix (Fin m) (Fin m) ℂ} {u : Fin m → ℂ} (hu : star u ⬝ᵥ u = 1)
    {φ : ℝ} (huφ : U *ᵥ u = exp (2 * Real.pi * I * φ) • u) (p : (circuit t m).Index) :
    (circuit t m).prob (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U)))
      (vecMulVec (input t m u) (star (input t m u))) p = ‖amplitude t φ (readout t m p)‖ ^ 2 := by
  rw [Circuit.prob_vecMulVec, Circuit.kraus_comp, ← mulVec_mulVec,
    kraus_unitary_mulVec huφ]
  rw [readout]
  generalize ((unitary t m).compIndexEquiv _ p).2 = q
  obtain ⟨i, j⟩ := q
  rw [Circuit.kraus_step, Circuit.kraus_done, Matrix.one_mul, measure_mulVec]
  set E := extendConfigEquiv (Equiv.refl (Fin t ⊕ Unit)) (fun _ : Unit ↦ Fin m) (Q t)
  have h1 : ∀ τ, control t m τ = (E τ).1 := fun _ ↦ rfl
  have h2 : ∀ τ : Config (system t m), τ (.inr ()) = (E τ).2 () := fun _ ↦ rfl
  have hu' : ∑ b, ‖u b‖ ^ 2 = 1 := Complex.ofReal_injective (by
    rw [ofReal_sum_norm_sq, hu, Complex.ofReal_one])
  simp only [tensorState, h1, h2]
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single (measured t m i) (fun x _ hx ↦ by simp [hx]) (by simp)]
  simp only [ite_true, norm_mul, mul_pow]
  rw [← Finset.mul_sum, ← (Equiv.funUnique Unit (Fin m)).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const]
  rw [hu', mul_one]

/-- The readout is a bijection from the branches onto the integers below `2^t`. -/
private theorem readout_bijective : Function.Bijective (readout t m) := by
  obtain ⟨hu⟩ := unique_index_unitary (t := t) (m := m)
  let e : (circuit t m).Index ≃ Fin (2 ^ t) :=
    ((unitary t m).compIndexEquiv _).trans ((Equiv.uniqueProd _ _).trans
      ((Equiv.sigmaEquivProd (measureLayer t m).Index Unit).trans
        ((Equiv.prodPUnit _).trans (measuredEquiv.trans (encode t)))))
  exact (show readout t m = e from rfl) ▸ e.bijective

/-- The probability of the outcome `k` is `|αₖ|²` with
`αₖ = 2^{-t} ∑_{j < 2^t} e^{2πi j (φ - k/2^t)}` (Nielsen–Chuang, eq. (5.24)). It needs only the
eigenvector equation and not that `U` is unitary; without unitarity the circuit is in general not
trace-preserving, but on this input the probabilities still sum to `1`. -/
theorem outcomeProb_eq {U : Matrix (Fin m) (Fin m) ℂ} {u : Fin m → ℂ} (hu : star u ⬝ᵥ u = 1)
    {φ : ℝ} (huφ : U *ᵥ u = exp (2 * Real.pi * I * φ) • u) (k : Fin (2 ^ t)) :
    (circuit t m).outcomeProb (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U)))
      (readout t m) (vecMulVec (input t m u) (star (input t m u))) k =
      ‖amplitude t φ k‖ ^ 2 := by
  rw [Circuit.outcomeProb, Finset.sum_filter]
  simp only [prob_eq hu huφ]
  rw [Fintype.sum_bijective _ readout_bijective
    (fun p ↦ if readout t m p = k then ‖amplitude t φ (readout t m p)‖ ^ 2 else 0)
    (fun k' ↦ if k' = k then ‖amplitude t φ k'‖ ^ 2 else 0) fun _ ↦ rfl, Finset.sum_ite_eq']
  simp

/-- Jordan's inequality on the circle: `|e^{2πix} - 1| ≥ 4|x - r|` when `|x - r| ≤ 1/2`. -/
private theorem four_mul_le_norm (x : ℝ) (r : ℤ) (hr : |x - r| ≤ 1 / 2) :
    4 * |x - r| ≤ ‖exp (2 * Real.pi * I * x) - 1‖ := by
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * x)
  rw [show I * ((2 * Real.pi * x : ℝ) : ℂ) = 2 * Real.pi * I * x by push_cast; ring] at h
  rw [h, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two,
    show 2 * Real.pi * x / 2 = Real.pi * (x - r) + r * Real.pi by ring, Real.sin_add_int_mul_pi,
    abs_mul, abs_neg_one_zpow, one_mul]
  have hy : |Real.sin (Real.pi * (x - r))| = Real.sin (Real.pi * |x - r|) := by
    rcases le_total 0 (x - r) with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
        (by positivity) (by nlinarith [Real.pi_pos, abs_of_nonneg h0 ▸ hr]))]
    · rw [abs_of_nonpos h0, show Real.pi * (x - r) = -(Real.pi * -(x - r)) by ring,
        Real.sin_neg, abs_neg, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos, abs_of_nonpos h0 ▸ hr]))]
  rw [hy]
  have := Real.mul_le_sin (x := Real.pi * |x - r|) (by positivity)
    (by nlinarith [Real.pi_pos])
  rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ Real.pi_ne_zero] at this
  linarith

/-- The geometric series bound `|αₖ| ≤ 1/(2^{t+1} |φ - k/2^t - r|)` (Nielsen–Chuang, eq. (5.29)). -/
private theorem norm_amplitude_le (t : ℕ) (φ : ℝ) (k : Fin (2 ^ t)) (r : ℤ)
    (hr : |φ - k / 2 ^ t - r| ≤ 1 / 2) (hpos : 0 < |φ - k / 2 ^ t - r|) :
    ‖amplitude t φ k‖ ≤ 1 / (2 * 2 ^ t * |φ - k / 2 ^ t - r|) := by
  set x : ℝ := φ - k / 2 ^ t
  set z := exp (2 * Real.pi * I * x)
  have hz : 4 * |x - r| ≤ ‖z - 1‖ := four_mul_le_norm x r hr
  have hz1 : z ≠ 1 := fun h ↦ by
    rw [h, sub_self, norm_zero] at hz; linarith
  have hnorm : ‖z‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hsum : ∑ j : Fin (2 ^ t), exp (2 * Real.pi * I * j * (φ - k / 2 ^ t)) =
      ∑ j ∈ Finset.range (2 ^ t), z ^ j := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ exp (2 * Real.pi * I * j * (φ - k / 2 ^ t)))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [x]
    push_cast
    ring
  rw [amplitude, hsum, geom_sum_eq hz1, norm_mul, norm_div, norm_inv, norm_pow, Complex.norm_two]
  have hnum : ‖z ^ 2 ^ t - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_pow, hnorm]; simp; norm_num)
  have hden : 0 < ‖z - 1‖ := by linarith
  calc (2 ^ t)⁻¹ * (‖z ^ 2 ^ t - 1‖ / ‖z - 1‖) ≤ (2 ^ t)⁻¹ * (2 / (4 * |x - r|)) := by
        gcongr
    _ = 1 / (2 * 2 ^ t * |x - r|) := by field_simp; ring

/-- `∑ 1/a² ≤ 1/(M-1)` over finitely many integers `a ≥ M`. -/
private theorem sum_inv_sq_le {M : ℤ} (hM : 2 ≤ M) (S : Finset ℤ) (hS : ∀ a ∈ S, M ≤ a) :
    ∑ a ∈ S, 1 / (a : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) := by
  have hM' : (1 : ℝ) ≤ M - 1 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  suffices h : ∀ c : ℤ, M - 1 ≤ c → (∀ a ∈ S, a ≤ c) →
      ∑ a ∈ S, 1 / (a : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) - 1 / c by
    have hc : M - 1 ≤ M - 1 + ∑ a ∈ S, |a| :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    have hpos : (0 : ℝ) < ((M - 1 + ∑ a ∈ S, |a| : ℤ) : ℝ) := by
      have : ((M - 1 : ℤ) : ℝ) ≤ ((M - 1 + ∑ a ∈ S, |a| : ℤ) : ℝ) := by exact_mod_cast hc
      push_cast at this ⊢
      linarith
    refine (h _ hc fun a ha ↦ ?_).trans (sub_le_self _ (by positivity))
    have h1 : a ≤ ∑ a ∈ S, |a| :=
      (le_abs_self a).trans (Finset.single_le_sum (f := fun a ↦ |a|)
        (fun _ _ ↦ abs_nonneg _) ha)
    linarith
  induction S using Finset.induction_on_max with
  | empty =>
    intro c hc _
    have : ((M : ℝ) - 1) ≤ c := by exact_mod_cast hc
    rw [Finset.sum_empty, sub_nonneg]
    exact one_div_le_one_div_of_le (by linarith) this
  | insert a S ha ih =>
    intro c hc hle
    have haM : M ≤ a := hS a (Finset.mem_insert_self a S)
    have hac : a ≤ c := hle a (Finset.mem_insert_self a S)
    have ih' := ih (fun x hx ↦ hS x (Finset.mem_insert_of_mem hx)) (a - 1) (by omega)
      fun x hx ↦ by have := ha x hx; omega
    rw [Finset.sum_insert fun h ↦ lt_irrefl a (ha a h)]
    have ha1 : (1 : ℝ) ≤ (a : ℝ) - 1 := by
      have : (M : ℝ) ≤ a := by exact_mod_cast haM
      linarith
    have hac' : (a : ℝ) ≤ c := by exact_mod_cast hac
    push_cast at ih'
    have key : 1 / (a : ℝ) ^ 2 ≤ 1 / ((a : ℝ) - 1) - 1 / a := by
      rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by nlinarith)
        (by nlinarith)]
      nlinarith
    have : 1 / (c : ℝ) ≤ 1 / a := one_div_le_one_div_of_le (by linarith) hac'
    linarith

/-- The outcomes farther than `2^{-n}` from `φ` modulo `1` have total probability at most
`1/(2(2^{t-n} - 1))` (Nielsen–Chuang, eqs. (5.30)–(5.34)). -/
private theorem sum_bad_le (t n : ℕ) (hn : n ≤ t) (hM : 2 ≤ 2 ^ (t - n)) (φ : ℝ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin (2 ^ t) ↦
        ¬ |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n),
      ‖amplitude t φ k‖ ^ 2 ≤ 1 / (2 * ((2 : ℝ) ^ (t - n) - 1)) := by
  set bad := Finset.univ.filter (fun k : Fin (2 ^ t) ↦
    ¬ |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n)
  have hN : (0 : ℝ) < 2 ^ t := by positivity
  set δ := Int.fract ((2 : ℝ) ^ t * φ)
  have hδ0 : 0 ≤ δ := Int.fract_nonneg _
  have hδ1 : δ < 1 := Int.fract_lt_one _
  set R : Fin (2 ^ t) → ℤ := fun k ↦ round ((k : ℝ) / 2 ^ t - φ)
  set m : Fin (2 ^ t) → ℤ := fun k ↦ (k : ℤ) - ⌊(2 : ℝ) ^ t * φ⌋ - 2 ^ t * R k
  have hm : ∀ k : Fin (2 ^ t), (2 : ℝ) ^ t * ((k : ℝ) / 2 ^ t - φ - R k) = m k - δ := by
    intro k
    simp only [m, δ, Int.fract]
    push_cast
    field_simp
    ring
  set M : ℝ := (2 : ℝ) ^ (t - n)
  have hMN : (2 : ℝ) ^ t / 2 ^ n = M := by
    rw [div_eq_iff (by positivity), ← pow_add, Nat.sub_add_cancel hn]
  have hbad : ∀ k ∈ bad, M < |(m k : ℝ) - δ| := by
    intro k hk
    have hk := (Finset.mem_filter.mp hk).2
    push Not at hk
    rw [← hm, abs_mul, abs_of_pos hN, ← hMN]
    rw [div_eq_mul_one_div]
    exact mul_lt_mul_of_pos_left hk hN
  have hamp : ∀ k ∈ bad, ‖amplitude t φ k‖ ^ 2 ≤ 1 / (4 * ((m k : ℝ) - δ) ^ 2) := by
    intro k hk
    have hd : |φ - k / 2 ^ t - ((-R k : ℤ) : ℝ)| = |(k : ℝ) / 2 ^ t - φ - R k| := by
      rw [← abs_neg]; push_cast; ring_nf
    have hd2 : |(k : ℝ) / 2 ^ t - φ - R k| ≤ 1 / 2 := abs_sub_round _
    have hMpos : 0 < M := by positivity
    have hdpos : 0 < |(k : ℝ) / 2 ^ t - φ - R k| := by
      have := hbad k hk
      rw [← hm, abs_mul, abs_of_pos hN] at this
      exact pos_of_mul_pos_right (hMpos.trans this) hN.le
    have h := norm_amplitude_le t φ k (-R k) (hd ▸ hd2) (hd ▸ hdpos)
    rw [hd, mul_assoc, ← abs_of_pos hN, ← abs_mul, abs_of_pos hN, hm] at h
    calc ‖amplitude t φ k‖ ^ 2 ≤ (1 / (2 * |(m k : ℝ) - δ|)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = 1 / (4 * ((m k : ℝ) - δ) ^ 2) := by
          rw [div_pow, mul_pow, sq_abs]; norm_num
  have hinj : Set.InjOn m bad := by
    intro k hk k' hk' h
    have h' : ((k : ℕ) : ℤ) - k' = 2 ^ t * (R k - R k') := by
      simp only [m] at h; linarith
    have hk1 : ((k : ℕ) : ℤ) < 2 ^ t := by exact_mod_cast k.2
    have hk2 : ((k' : ℕ) : ℤ) < 2 ^ t := by exact_mod_cast k'.2
    have hk3 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := by positivity
    have hk4 : (0 : ℤ) ≤ ((k' : ℕ) : ℤ) := by positivity
    have hlt : |((k : ℕ) : ℤ) - k'| < 2 ^ t := by
      rw [abs_lt]; constructor <;> linarith
    have hzero : R k - R k' = 0 := by
      by_contra hne
      have : (2 : ℤ) ^ t ≤ |((k : ℕ) : ℤ) - k'| := by
        rw [h', abs_mul, abs_of_pos (by positivity)]
        exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hne)
      linarith
    rw [hzero, mul_zero, sub_eq_zero] at h'
    exact Fin.ext (by exact_mod_cast h')
  set T := bad.image m
  have hT : ∀ ℓ ∈ T, M < |(ℓ : ℝ) - δ| := by
    intro ℓ hℓ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hℓ
    exact hbad k hk
  have hMint : (2 : ℤ) ≤ 2 ^ (t - n) := by exact_mod_cast hM
  have hMcast : ((2 ^ (t - n) : ℤ) : ℝ) = M := by push_cast; rfl
  have hpos : ∀ ℓ ∈ T.filter (1 ≤ ·), 2 ^ (t - n) ≤ ℓ - 1 ∧
      1 / (4 * ((ℓ : ℝ) - δ) ^ 2) ≤ 1 / 4 * (1 / (((ℓ - 1 : ℤ) : ℝ)) ^ 2) := by
    intro ℓ hℓ
    obtain ⟨hℓT, hℓ1⟩ := Finset.mem_filter.mp hℓ
    have h := hT ℓ hℓT
    have hℓ1' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
    rw [abs_of_pos (by linarith)] at h
    have hlt : ((2 ^ (t - n) : ℤ) : ℝ) < ℓ := by rw [hMcast]; linarith
    have hlt' : (2 : ℤ) ^ (t - n) < ℓ := by exact_mod_cast hlt
    refine ⟨by omega, ?_⟩
    have h2 : (2 : ℝ) ≤ ((ℓ - 1 : ℤ) : ℝ) := by
      have : (2 : ℤ) ≤ ℓ - 1 := by omega
      exact_mod_cast this
    push_cast at h2 ⊢
    rw [one_div_mul_one_div]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by norm_num))
  have hneg : ∀ ℓ ∈ T.filter (¬ 1 ≤ ·), 2 ^ (t - n) ≤ -ℓ ∧
      1 / (4 * ((ℓ : ℝ) - δ) ^ 2) ≤ 1 / 4 * (1 / (((-ℓ : ℤ) : ℝ)) ^ 2) := by
    intro ℓ hℓ
    obtain ⟨hℓT, hℓ0⟩ := Finset.mem_filter.mp hℓ
    have h := hT ℓ hℓT
    have hℓ0' : (ℓ : ℝ) ≤ 0 := by exact_mod_cast (show ℓ ≤ 0 by omega)
    rw [abs_of_nonpos (by linarith)] at h
    have hlt : ((2 ^ (t - n) : ℤ) : ℝ) - 1 < ((-ℓ : ℤ) : ℝ) := by
      rw [hMcast]; push_cast; linarith
    have hlt' : (2 : ℤ) ^ (t - n) - 1 < -ℓ := by exact_mod_cast hlt
    refine ⟨by omega, ?_⟩
    have h2 : (2 : ℝ) ≤ ((-ℓ : ℤ) : ℝ) := by
      have : (2 : ℤ) ≤ -ℓ := by omega
      exact_mod_cast this
    push_cast at h2 ⊢
    rw [one_div_mul_one_div]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left
      (by nlinarith) (by norm_num))
  have hsub : ∀ ℓ ∈ T.filter (1 ≤ ·), ∀ ℓ' ∈ T.filter (1 ≤ ·), ℓ - 1 = ℓ' - 1 → ℓ = ℓ' :=
    fun _ _ _ _ h ↦ by omega
  have hnegi : ∀ ℓ ∈ T.filter (¬ 1 ≤ ·), ∀ ℓ' ∈ T.filter (¬ 1 ≤ ·), -ℓ = -ℓ' → ℓ = ℓ' :=
    fun _ _ _ _ h ↦ by omega
  have hP := sum_inv_sq_le hMint ((T.filter (1 ≤ ·)).image (· - 1)) fun a ha ↦ by
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp ha
    exact (hpos ℓ hℓ).1
  have hQ := sum_inv_sq_le hMint ((T.filter (¬ 1 ≤ ·)).image (- ·)) fun a ha ↦ by
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp ha
    exact (hneg ℓ hℓ).1
  rw [Finset.sum_image hsub] at hP
  rw [Finset.sum_image hnegi] at hQ
  rw [hMcast] at hP hQ
  calc ∑ k ∈ bad, ‖amplitude t φ k‖ ^ 2 ≤ ∑ k ∈ bad, 1 / (4 * ((m k : ℝ) - δ) ^ 2) :=
        Finset.sum_le_sum hamp
    _ = ∑ ℓ ∈ T, 1 / (4 * ((ℓ : ℝ) - δ) ^ 2) :=
        (Finset.sum_image (f := fun ℓ : ℤ ↦ 1 / (4 * ((ℓ : ℝ) - δ) ^ 2)) hinj).symm
    _ = ∑ ℓ ∈ T.filter (1 ≤ ·), 1 / (4 * ((ℓ : ℝ) - δ) ^ 2) +
        ∑ ℓ ∈ T.filter (¬ 1 ≤ ·), 1 / (4 * ((ℓ : ℝ) - δ) ^ 2) :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ ∑ ℓ ∈ T.filter (1 ≤ ·), 1 / 4 * (1 / (((ℓ - 1 : ℤ) : ℝ)) ^ 2) +
        ∑ ℓ ∈ T.filter (¬ 1 ≤ ·), 1 / 4 * (1 / (((-ℓ : ℤ) : ℝ)) ^ 2) :=
        add_le_add (Finset.sum_le_sum fun ℓ hℓ ↦ (hpos ℓ hℓ).2)
          (Finset.sum_le_sum fun ℓ hℓ ↦ (hneg ℓ hℓ).2)
    _ ≤ 1 / 4 * (1 / (M - 1)) + 1 / 4 * (1 / (M - 1)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        gcongr
    _ = 1 / (2 * (M - 1)) := by
        have : M - 1 ≠ 0 := by
          have : (2 : ℝ) ≤ M := by rw [← hMcast]; exact_mod_cast hMint
          linarith
        field_simp
        ring

/-- If `2^t φ` is an integer congruent to `k` modulo `2^t`, the outcome `k` has probability `1`
(Nielsen–Chuang, §5.2.1). -/
theorem outcomeProb_eq_one_of_exact {U : Matrix (Fin m) (Fin m) ℂ} {u : Fin m → ℂ}
    (hu : star u ⬝ᵥ u = 1) {φ : ℝ} (huφ : U *ᵥ u = exp (2 * Real.pi * I * φ) • u)
    {k : Fin (2 ^ t)} (hk : ∃ q : ℤ, (2 : ℝ) ^ t * φ = k + 2 ^ t * q) :
    (circuit t m).outcomeProb (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U)))
      (readout t m) (vecMulVec (input t m u) (star (input t m u))) k = 1 := by
  obtain ⟨q, hq⟩ := hk
  have hφ : (φ : ℂ) - k / 2 ^ t = q := by
    have : φ - k / 2 ^ t = q := by
      field_simp
      linarith
    have h := congrArg (fun x : ℝ ↦ (x : ℂ)) this
    push_cast at h
    exact h
  have hone : ∀ j : Fin (2 ^ t), exp (2 * Real.pi * I * j * (φ - k / 2 ^ t)) = 1 := fun j ↦ by
    rw [mul_assoc, hφ, Complex.exp_eq_one_iff]
    exact ⟨j * q, by push_cast; ring⟩
  rw [outcomeProb_eq hu huφ, amplitude, Finset.sum_congr rfl fun j _ ↦ hone j,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow,
    Nat.cast_ofNat, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), norm_one, one_pow]

/-- Phase estimation with `t = n + ⌈log₂(2 + 1/(2ε))⌉` control qubits, on the input
`|0…0⟩ ⊗ |u⟩` for an eigenvector `U u = e^{2πiφ} u` of norm `1`, returns an integer `k` with
`k / 2^t` within `2^{-n}` of `φ` modulo `1` with probability at least `1 - ε`
(Nielsen–Chuang, §5.2.1, eq. (5.35)). The statement needs only the eigenvector and not that `U`
is unitary; without unitarity the circuit is in general not trace-preserving. -/
theorem accurate_prob_ge (U : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → ℂ) (hu : star u ⬝ᵥ u = 1)
    (φ : ℝ) (huφ : U *ᵥ u = exp (2 * Real.pi * I * φ) • u) (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (ht : t = n + ⌈Real.logb 2 (2 + 1 / (2 * ε))⌉₊) :
    1 - ε ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin (2 ^ t) ↦
        |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n),
      (circuit t m).outcomeProb (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U)))
        (readout t m) (vecMulVec (input t m u) (star (input t m u))) k := by
  set p := ⌈Real.logb 2 (2 + 1 / (2 * ε))⌉₊
  have hp : 2 + 1 / (2 * ε) ≤ (2 : ℝ) ^ p := by
    have hy : 0 < 2 + 1 / (2 * ε) := by positivity
    calc 2 + 1 / (2 * ε) = (2 : ℝ) ^ Real.logb 2 (2 + 1 / (2 * ε)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hy).symm
      _ ≤ (2 : ℝ) ^ (p : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = 2 ^ p := Real.rpow_natCast _ _
  have htn : t - n = p := by omega
  have hM : 2 ≤ 2 ^ (t - n) := by
    rw [htn]
    have : (2 : ℝ) < 2 ^ p := by
      have : 0 < 1 / (2 * ε) := by positivity
      linarith
    exact_mod_cast this.le
  have hbad := sum_bad_le t n (by omega) hM φ
  have hε' : 1 / (2 * ((2 : ℝ) ^ (t - n) - 1)) ≤ ε := by
    rw [htn, div_le_iff₀ (by nlinarith [show 0 < 1 / (2 * ε) by positivity])]
    have : 1 / (2 * ε) * (2 * ε) = 1 := by field_simp
    nlinarith
  have hall := sum_norm_sq_amplitude (t := t) φ
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin (2 ^ t) ↦
    |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n)] at hall
  simp only [outcomeProb_eq hu huφ]
  linarith

end PhaseEstimation

end QuantumCircuit
