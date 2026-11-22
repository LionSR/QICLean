/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Model.Unitary

/-!
# Unitary circuits inside a region, in series and in parallel

A layer acts *inside* the region `R` when every cell it uses lies in `R` and every onsite family
at a site outside `R` has the Kraus operator `1`; a unitary circuit acts inside `R` when all its
layers do (`UnitaryCircuit.IsIn`). This is a restriction of the circuit, read off its layers, and
its operator is then supported on `R`. A matrix `U` is a unitary circuit of depth `T` inside `R`
(`IsUnitaryCircuitOn`) when some unitary circuit of depth at most `T` inside `R` has operator `U`.

Circuits inside one region compose in series with additive depth. Two circuits inside disjoint
regions, on a geometry whose cells are nonempty, run in parallel (`UnitaryCircuit.par`): the
layers are merged greedily, a layer of depth `0` at the head of either circuit being emitted
alone and two layers of depth `1` being merged into one layer acting by each on its own cells
and sites. The result acts inside the union, its operator is the product of the two operators
(they commute, being supported on disjoint regions), its depth is at most the larger depth and
its gate count is the sum of the gate counts. These are the two ways of composing circuits used
in the preparation of arXiv:2307.01696: the unitaries `U_i` of eq. (10) act on disjoint blocks
and each "can be implemented in `T=O(q)`" (paragraph before "The sequential-RG circuit").

The cells must be nonempty for the parallel composition: a gate on an empty cell is a phase, and
two circuits inside disjoint regions may both use such a cell.

The declarations restate `BondLayer.IsIn`, `BondLayer.union`, `IsBondCircuitOn`,
`IsCircuitOn` and their API of `TNLean/Circuit/Composition.lean` at commit `414a18fb88`
(Apache-2.0). The changes: any geometry and any finite basis at each site; depth at most `T` in
place of exactly `T` layers, so that circuits of different depths run in parallel without
padding, and the merge of layers is greedy because a layer of cost-`0` cells or onsite unitaries
has depth `0`; one-site unitaries are onsite families, which must be `1` outside the region.

## Main definitions

* `QuantumCircuit.Layer.IsIn`, `QuantumCircuit.UnitaryCircuit.IsIn` — acting inside a region.
* `QuantumCircuit.IsUnitaryCircuitOn` — a unitary circuit of depth at most `T` inside `R`.
* `QuantumCircuit.Layer.par`, `QuantumCircuit.UnitaryCircuit.par` — two layers, or two circuits,
  inside disjoint regions run in parallel.

## Main results

* `QuantumCircuit.UnitaryCircuit.op_mem_supportedOperators` — the operator of a circuit inside
  `R` is supported on `R`.
* `QuantumCircuit.UnitaryCircuit.op_par`, `QuantumCircuit.UnitaryCircuit.depth_par_le`,
  `QuantumCircuit.UnitaryCircuit.gateCount_par` — the parallel composition.
* `QuantumCircuit.IsUnitaryCircuitOn.mul` — circuits in series.
* `QuantumCircuit.IsUnitaryCircuitOn.par`, `QuantumCircuit.IsUnitaryCircuitOn.finset_noncommProd`,
  `QuantumCircuit.IsUnitaryCircuitOn.list_prod` — circuits in parallel.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S} {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-! ### Layers inside a region -/

namespace Layer

section IsIn

variable {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

/-- A layer acts inside the region `R` when every cell it uses lies in `R` and every onsite
family at a site outside `R` has the Kraus operator `1`.

Source: arXiv:2307.01696, paragraph "The sequential-RG circuit" (the unitaries `U_i` of eq. (10)
act on blocks of sites). -/
def IsIn (L : Layer Γ G X X) (R : Finset S) : Prop :=
  (∀ b ∈ L.cells, Γ.cell b ⊆ R) ∧ ∀ s : L.Free, s.1 ∉ R → ∀ i, (L.onsite s).op i = 1

variable {L : Layer Γ G X X} {R R' : Finset S}

omit [Fintype S] [∀ s, Fintype (X s)] [GateFamily G] in
theorem IsIn.mono (h : L.IsIn R) (hR : R ⊆ R') : L.IsIn R' :=
  ⟨fun b hb ↦ (h.1 b hb).trans hR, fun s hs ↦ h.2 s fun hsR ↦ hs (hR hsR)⟩

omit [Fintype S] [∀ s, Fintype (X s)] [GateFamily G] in
/-- A site outside the region of a layer inside it is met by no cell. -/
theorem IsIn.not_mem_biUnion (h : L.IsIn R) {v : S} (hv : v ∉ R) :
    v ∉ L.cells.biUnion Γ.cell := fun hm ↦ by
  obtain ⟨b, hb, hvb⟩ := Finset.mem_biUnion.mp hm
  exact hv (h.1 b hb hvb)

/-- The Kraus operators of a layer inside `R` are supported on `R`. -/
theorem kraus_mem_supportedOperators (ev : Interpretation G) (h : L.IsIn R) (i : L.Index) :
    L.kraus ev i ∈ supportedOperators X R := by
  refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  · rw [kraus_apply]
    refine mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_univ ⟨v, h.not_mem_biUnion hv⟩) ?_)
    rw [h.2 ⟨v, h.not_mem_biUnion hv⟩ hv, one_apply_ne hne]
  · rw [kraus_apply, kraus_apply]
    congr 1
    · refine Finset.prod_congr rfl fun b _ ↦ ?_
      rw [show (fun v : {v // v ∈ Γ.cell b} ↦ σ v) = fun v : {v // v ∈ Γ.cell b} ↦ σ' v from
          funext fun v ↦ h1 v (h.1 b b.2 v.2),
        show (fun v : {v // v ∈ Γ.cell b} ↦ τ v) = fun v : {v // v ∈ Γ.cell b} ↦ τ' v from
          funext fun v ↦ h2 v (h.1 b b.2 v.2)]
    · refine Finset.prod_congr rfl fun s _ ↦ ?_
      by_cases hs : s.1 ∈ R
      · rw [h1 s hs, h2 s hs]
      · rw [h.2 s hs, h3 s hs, h4 s hs, one_apply_eq, one_apply_eq]

omit [Fintype S] [∀ s, Fintype (X s)] [GateFamily G] in
/-- A layer of one gate on a cell inside `R` acts inside `R`. -/
theorem isIn_single (b : Γ.Cell) (g : G (Γ.cell b) X X) (hb : Γ.cell b ⊆ R) :
    (single b g).IsIn R :=
  ⟨fun _ hc ↦ (Finset.mem_singleton.mp hc) ▸ hb, fun _ _ _ ↦ rfl⟩

omit [Fintype S] [∀ s, Fintype (X s)] [GateFamily G] in
/-- A layer with no cells acts inside `R` when its onsite families outside `R` are `1`. -/
theorem isIn_ofOnsite (o : (s : S) → KrausFamily (X s) (X s))
    (ho : ∀ s ∉ R, ∀ i, (o s).op i = 1) : (ofOnsite (Γ := Γ) (G := G) o).IsIn R :=
  ⟨fun b hb ↦ absurd hb (Finset.notMem_empty b), fun s hs ↦ ho s.1 hs⟩

end IsIn

omit [Fintype S] [∀ s, Fintype (X s)] in
/-- The adjoint of a layer inside `R` acts inside `R`. -/
theorem IsIn.adjoint {L : Layer Γ KrausGate X X} {R : Finset S} (h : L.IsIn R) :
    L.adjoint.IsIn R :=
  ⟨h.1, fun s hs i ↦ by
    change ((L.onsite s).op i)ᴴ = 1
    exact (congrArg conjTranspose (h.2 s hs i)).trans conjTranspose_one⟩

end Layer

/-! ### Unitary circuits inside a region -/

namespace UnitaryCircuit

/-- The unitary circuit of all layers of `c` but the first. -/
def tail (c : UnitaryCircuit Γ X) : UnitaryCircuit Γ X :=
  ⟨c.layers.tail, fun L hL ↦ c.isUnitary L (List.mem_of_mem_tail hL)⟩

/-- The operator of a unitary circuit whose first layer is `L` is the operator of the remaining
layers times the operator of `L`. -/
theorem op_eq_tail_op_mul {c : UnitaryCircuit Γ X} {L : Layer Γ KrausGate X X}
    {Ls : List (Layer Γ KrausGate X X)} (h : c.layers = L :: Ls) (i : L.Index) :
    c.op = c.tail.op * L.kraus KrausGate.ev i := by
  obtain ⟨Ls', hLs'⟩ := c
  subst h
  exact (op_comp (ofLayer L (hLs' L List.mem_cons_self)) ⟨Ls, _⟩).trans
    (congrArg _ (op_ofLayer _ _ i))

/-- A unitary circuit without layers has operator `1`. -/
theorem op_eq_one {c : UnitaryCircuit Γ X} (h : c.layers = []) : c.op = 1 := by
  obtain ⟨Ls, hLs⟩ := c
  subst h
  rfl

/-- A unitary circuit acts inside the region `R` when every layer does.

Source: arXiv:2307.01696, main text before Theorem 1 ("depth-`T` local quantum circuits"),
restricted to gates inside `R` as in the parallel application of the block unitaries in the
paragraph "The sequential-RG circuit". -/
def IsIn (c : UnitaryCircuit Γ X) (R : Finset S) : Prop :=
  ∀ L ∈ c.layers, L.IsIn R

variable {c c' : UnitaryCircuit Γ X} {R R' : Finset S}

omit [Fintype S] in
theorem IsIn.mono (h : c.IsIn R) (hR : R ⊆ R') : c.IsIn R' :=
  fun L hL ↦ (h L hL).mono hR

omit [Fintype S] in
theorem IsIn.tail (h : c.IsIn R) : c.tail.IsIn R :=
  fun L hL ↦ h L (List.mem_of_mem_tail hL)

omit [Fintype S] in
theorem isIn_id (R : Finset S) : (id Γ X).IsIn R :=
  fun _ hL ↦ absurd hL List.not_mem_nil

omit [Fintype S] in
theorem IsIn.comp (h : c.IsIn R) (h' : c'.IsIn R) : (c.comp c').IsIn R :=
  fun L hL ↦ (List.mem_append.mp hL).elim (h L) (h' L)

omit [Fintype S] in
theorem IsIn.adjoint (h : c.IsIn R) : c.adjoint.IsIn R := fun L hL ↦ by
  obtain ⟨L', hL', rfl⟩ := List.mem_map.mp hL
  exact (h L' (List.mem_reverse.mp hL')).adjoint

omit [Fintype S] in
/-- A gate on a cell inside `R` acts inside `R`. -/
theorem isIn_gate (b : Γ.Cell)
    (V : Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ)
    (hV : V ∈ unitaryGroup _ ℂ) (hb : Γ.cell b ⊆ R) : (gate b V hV).IsIn R :=
  fun _ hL ↦ (List.mem_singleton.mp hL) ▸ Layer.isIn_single b _ hb

omit [Fintype S] in
/-- One-site unitaries equal to `1` outside `R` act inside `R`. -/
theorem isIn_onsite (u : (s : S) → Matrix (X s) (X s) ℂ) (hu : ∀ s, u s ∈ unitaryGroup (X s) ℂ)
    (h1 : ∀ s ∉ R, u s = 1) : (onsite (Γ := Γ) u hu).IsIn R :=
  fun _ hL ↦ (List.mem_singleton.mp hL) ▸ Layer.isIn_ofOnsite _ fun s hs _ ↦ h1 s hs

/-- The operator of a unitary circuit inside `R` is supported on `R`. -/
theorem op_mem_supportedOperators (h : c.IsIn R) : c.op ∈ supportedOperators X R := by
  obtain ⟨Ls, hLs⟩ := c
  induction Ls with
  | nil => exact one_mem _
  | cons L Ls ih =>
    obtain ⟨i⟩ := (Layer.nonempty_unique_index_of_forall_isUnitary
      (hLs L List.mem_cons_self)).map fun u ↦ u.default
    rw [op_eq_tail_op_mul rfl i]
    exact mul_mem (ih _ fun L' hL' ↦ h L' (List.mem_cons_of_mem L hL'))
      (Layer.kraus_mem_supportedOperators _ (h L List.mem_cons_self) i)

end UnitaryCircuit

/-! ### Unitary circuits of bounded depth inside a region -/

variable (Γ) in
/-- `U` is a unitary circuit of depth at most `T` on the geometry `Γ` inside the region `R`: the
operator of a unitary circuit of depth at most `T` all of whose layers act inside `R`.

Source: arXiv:2307.01696, main text before Theorem 1 ("depth-`T` local quantum circuits"),
restricted to gates inside `R` as in the parallel application of the block unitaries in the
paragraph "The sequential-RG circuit". -/
def IsUnitaryCircuitOn (R : Finset S) (T : ℕ) (U : Matrix (Config X) (Config X) ℂ) : Prop :=
  ∃ c : UnitaryCircuit Γ X, c.IsIn R ∧ c.depth ≤ T ∧ c.op = U

namespace IsUnitaryCircuitOn

variable {R R' : Finset S} {T T' : ℕ} {U V : Matrix (Config X) (Config X) ℂ}

theorem isUnitaryCircuit (h : IsUnitaryCircuitOn Γ R T U) : IsUnitaryCircuit Γ T U :=
  let ⟨c, _, hc, hU⟩ := h
  ⟨c, hc, hU⟩

theorem mem_unitaryGroup (h : IsUnitaryCircuitOn Γ R T U) : U ∈ unitaryGroup (Config X) ℂ := by
  obtain ⟨c, -, -, rfl⟩ := h
  exact c.op_mem_unitaryGroup

theorem mem_supportedOperators (h : IsUnitaryCircuitOn Γ R T U) : U ∈ supportedOperators X R := by
  obtain ⟨c, hc, -, rfl⟩ := h
  exact c.op_mem_supportedOperators hc

theorem mono_set (h : IsUnitaryCircuitOn Γ R T U) (hR : R ⊆ R') : IsUnitaryCircuitOn Γ R' T U :=
  let ⟨c, hcR, hc, hU⟩ := h
  ⟨c, hcR.mono hR, hc, hU⟩

theorem mono (h : IsUnitaryCircuitOn Γ R T U) (hT : T ≤ T') : IsUnitaryCircuitOn Γ R T' U :=
  let ⟨c, hcR, hc, hU⟩ := h
  ⟨c, hcR, hc.trans hT, hU⟩

variable (Γ X) in
theorem one (R : Finset S) (T : ℕ) :
    IsUnitaryCircuitOn Γ R T (1 : Matrix (Config X) (Config X) ℂ) :=
  ⟨UnitaryCircuit.id Γ X, UnitaryCircuit.isIn_id R, Nat.zero_le T, rfl⟩

/-- **Circuits in series.** Applying `V` and then `U` inside `R` is a circuit inside `R` of depth
at most the sum. -/
theorem mul (hU : IsUnitaryCircuitOn Γ R T U) (hV : IsUnitaryCircuitOn Γ R T' V) :
    IsUnitaryCircuitOn Γ R (T + T') (U * V) := by
  obtain ⟨c, hcR, hc, rfl⟩ := hU
  obtain ⟨c', hcR', hc', rfl⟩ := hV
  exact ⟨c'.comp c, hcR'.comp hcR, by rw [UnitaryCircuit.depth_comp]; omega,
    UnitaryCircuit.op_comp _ _⟩

/-- The adjoint of a circuit inside `R` is a circuit inside `R` of the same depth. -/
theorem conjTranspose (h : IsUnitaryCircuitOn Γ R T U) : IsUnitaryCircuitOn Γ R T Uᴴ := by
  obtain ⟨c, hcR, hc, rfl⟩ := h
  exact ⟨c.adjoint, hcR.adjoint, c.depth_adjoint.trans_le hc, c.op_adjoint⟩

/-- A unitary placed on a cell inside `R` is a circuit inside `R` of depth at most `1`. -/
theorem place {b : Γ.Cell}
    {V : Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ}
    (hb : Γ.cell b ⊆ R) (hV : V ∈ unitaryGroup _ ℂ) :
    IsUnitaryCircuitOn Γ R 1 (ManyBody.place (Γ.cell b) V) :=
  ⟨UnitaryCircuit.gate b V hV, UnitaryCircuit.isIn_gate b V hV hb,
    UnitaryCircuit.depth_gate_le b V hV, UnitaryCircuit.op_gate b V hV⟩

/-- A unitary supported on a cell inside `R` is a circuit inside `R` of depth at most `1`. -/
theorem of_mem_supportedOperators {b : Γ.Cell} {Z : Matrix (Config X) (Config X) ℂ}
    (hb : Γ.cell b ⊆ R) (hZu : Z ∈ unitaryGroup (Config X) ℂ)
    (hZ : Z ∈ supportedOperators X (Γ.cell b)) : IsUnitaryCircuitOn Γ R 1 Z := by
  by_cases hne : ∀ s, Nonempty (X s)
  · obtain ⟨V, rfl⟩ := exists_eq_place_of_mem_supportedOperators hZ
    exact place hb (place_mem_unitaryGroup_iff.mp hZu)
  · push Not at hne
    obtain ⟨s, hs⟩ := hne
    have : IsEmpty (Config X) := ⟨fun σ ↦ hs.false (σ s)⟩
    rw [Subsingleton.elim Z (ManyBody.place (Γ.cell b) 1)]
    exact place hb (one_mem _)

/-- One-site unitaries equal to `1` outside `R` form a circuit inside `R` of depth `0`. -/
theorem piKronecker {u : (s : S) → Matrix (X s) (X s) ℂ} (hu : ∀ s, u s ∈ unitaryGroup (X s) ℂ)
    (h1 : ∀ s ∉ R, u s = 1) (T : ℕ) : IsUnitaryCircuitOn Γ R T (Matrix.piKronecker u) :=
  ⟨UnitaryCircuit.onsite u hu, UnitaryCircuit.isIn_onsite u hu h1,
    (UnitaryCircuit.depth_onsite u hu).trans_le (Nat.zero_le T), UnitaryCircuit.op_onsite u hu⟩

end IsUnitaryCircuitOn

/-! ### Two layers in parallel -/

namespace Layer

variable {R₁ R₂ : Finset S}

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
private theorem not_mem_biUnion_left {L₁ L₂ : Layer Γ KrausGate X X} {s : S}
    (hs : s ∉ (L₁.cells ∪ L₂.cells).biUnion Γ.cell) : s ∉ L₁.cells.biUnion Γ.cell :=
  fun h ↦ hs (Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_left h)

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
private theorem not_mem_biUnion_right {L₁ L₂ : Layer Γ KrausGate X X} {s : S}
    (hs : s ∉ (L₁.cells ∪ L₂.cells).biUnion Γ.cell) : s ∉ L₂.cells.biUnion Γ.cell :=
  fun h ↦ hs (Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_right h)

omit [Fintype S] [∀ s, Fintype (X s)] in
/-- Two layers inside disjoint regions, run as one layer: the cells of both with the gates of
each, and at a site met by no cell the onsite family of the first layer inside `R₁` and of the
second elsewhere. -/
def par (L₁ L₂ : Layer Γ KrausGate X X) (h₁ : L₁.IsIn R₁) (h₂ : L₂.IsIn R₂)
    (hR : Disjoint R₁ R₂) : Layer Γ KrausGate X X where
  cells := L₁.cells ∪ L₂.cells
  pairwiseDisjoint b hb b' hb' hbb' := by
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hb) with hb | hb <;>
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hb') with hb' | hb'
    · exact L₁.pairwiseDisjoint hb hb' hbb'
    · exact hR.mono (h₁.1 b hb) (h₂.1 b' hb')
    · exact (hR.mono (h₁.1 b' hb') (h₂.1 b hb)).symm
    · exact L₂.pairwiseDisjoint hb hb' hbb'
  gate b := if hb : b.1 ∈ L₁.cells then L₁.gate ⟨b.1, hb⟩
    else L₂.gate ⟨b.1, (Finset.mem_union.mp b.2).resolve_left hb⟩
  onsite s := if s.1 ∈ R₁ then L₁.onsite ⟨s.1, not_mem_biUnion_left s.2⟩
    else L₂.onsite ⟨s.1, not_mem_biUnion_right s.2⟩

variable {L₁ L₂ : Layer Γ KrausGate X X}

omit [Fintype S] [∀ s, Fintype (X s)] in
/-- On a geometry whose cells are nonempty, layers inside disjoint regions use disjoint sets of
cells. -/
theorem disjoint_cells (hne : ∀ b, (Γ.cell b).Nonempty) (h₁ : L₁.IsIn R₁) (h₂ : L₂.IsIn R₂)
    (hR : Disjoint R₁ R₂) : Disjoint L₁.cells L₂.cells := by
  rw [Finset.disjoint_left]
  intro b hb hb'
  obtain ⟨v, hv⟩ := hne b
  exact Finset.disjoint_left.mp hR (h₁.1 b hb hv) (h₂.1 b hb' hv)

omit [Fintype S] in
theorem forall_isUnitary_par (h₁ : L₁.IsIn R₁) (h₂ : L₂.IsIn R₂) (hR : Disjoint R₁ R₂)
    (hu₁ : L₁.Forall KrausGate.ev KrausFamily.IsUnitary)
    (hu₂ : L₂.Forall KrausGate.ev KrausFamily.IsUnitary) :
    (par L₁ L₂ h₁ h₂ hR).Forall KrausGate.ev KrausFamily.IsUnitary := by
  refine ⟨fun b ↦ ?_, fun s ↦ ?_⟩
  · by_cases hb : b.1 ∈ L₁.cells
    · have key : ∀ K, K = L₁.gate ⟨b.1, hb⟩ → KrausFamily.IsUnitary K := by
        rintro K rfl
        exact hu₁.1 _
      exact key _ (dite_eq_left hb)
    · have key : ∀ K, K = L₂.gate ⟨b.1, (Finset.mem_union.mp b.2).resolve_left hb⟩ →
          KrausFamily.IsUnitary K := by
        rintro K rfl
        exact hu₂.1 _
      exact key _ (dite_eq_right hb)
  · by_cases hs : s.1 ∈ R₁
    · have key : ∀ K, K = L₁.onsite ⟨s.1, not_mem_biUnion_left s.2⟩ →
          KrausFamily.IsUnitary K := by
        rintro K rfl
        exact hu₁.2 _
      exact key _ (ite_eq_left hs)
    · have key : ∀ K, K = L₂.onsite ⟨s.1, not_mem_biUnion_right s.2⟩ →
          KrausFamily.IsUnitary K := by
        rintro K rfl
        exact hu₂.2 _
      exact key _ (ite_eq_right hs)

omit [Fintype S] [∀ s, Fintype (X s)] in
omit [Fintype S] in
theorem isIn_par (h₁ : L₁.IsIn R₁) (h₂ : L₂.IsIn R₂) (hR : Disjoint R₁ R₂) :
    (par L₁ L₂ h₁ h₂ hR).IsIn (R₁ ∪ R₂) := by
  refine ⟨fun b hb ↦ ?_, fun s hs ↦ ?_⟩
  · rcases Finset.mem_union.mp hb with hb | hb
    · exact (h₁.1 b hb).trans Finset.subset_union_left
    · exact (h₂.1 b hb).trans Finset.subset_union_right
  · rw [Finset.mem_union, not_or] at hs
    have key : ∀ K, K = L₂.onsite ⟨s.1, not_mem_biUnion_right s.2⟩ → ∀ i, K.op i = 1 := by
      rintro K rfl
      exact h₂.2 _ hs.2
    exact key _ (ite_eq_right hs.1)

omit [Fintype S] [∀ s, Fintype (X s)] in
/-- A product over the cells of two layers run in parallel, when their sets of cells are
disjoint. -/
private theorem prod_cells_par {L₁ L₂ : Layer Γ KrausGate X X} (h₁ : L₁.IsIn R₁) (h₂ : L₂.IsIn R₂)
    (hR : Disjoint R₁ R₂) (hcells : Disjoint L₁.cells L₂.cells)
    (f : (par L₁ L₂ h₁ h₂ hR).cells → ℂ) :
    ∏ b, f b = (∏ b : L₁.cells, f ⟨b.1, Finset.mem_union_left _ b.2⟩) *
      ∏ b : L₂.cells, f ⟨b.1, Finset.mem_union_right _ b.2⟩ :=
  ((Equiv.Finset.union _ _ hcells).prod_comp f).symm.trans (Fintype.prod_sum_type _)

/-- **Two layers in parallel.** On a geometry whose cells are nonempty, the Kraus operator of two
unitary layers inside disjoint regions run as one layer is the product of their Kraus
operators. -/
theorem kraus_par (hne : ∀ b, (Γ.cell b).Nonempty) (h₁ : L₁.IsIn R₁) (h₂ : L₂.IsIn R₂)
    (hR : Disjoint R₁ R₂) (hu₁ : L₁.Forall KrausGate.ev KrausFamily.IsUnitary)
    (hu₂ : L₂.Forall KrausGate.ev KrausFamily.IsUnitary) (i : (par L₁ L₂ h₁ h₂ hR).Index)
    (i₁ : L₁.Index) (i₂ : L₂.Index) :
    (par L₁ L₂ h₁ h₂ hR).kraus KrausGate.ev i =
      L₁.kraus KrausGate.ev i₁ * L₂.kraus KrausGate.ev i₂ := by
  ext y x
  rw [mul_apply_of_mem_supportedOperators_of_disjoint (kraus_mem_supportedOperators _ h₁ i₁)
    (kraus_mem_supportedOperators _ h₂ i₂) hR]
  set z : Config X := fun v ↦ if v ∈ R₁ then x v else y v with hz
  have hcells := disjoint_cells hne h₁ h₂ hR
  simp only [kraus_apply]
  rw [mul_mul_mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [prod_cells_par h₁ h₂ hR hcells]
    refine congrArg₂ (· * ·) (Fintype.prod_congr _ _ fun b ↦ ?_)
      (Fintype.prod_congr _ _ fun b ↦ ?_)
    · rw [show (fun v : {v // v ∈ Γ.cell b} ↦ z v) = fun v : {v // v ∈ Γ.cell b} ↦ x v from
        funext fun v ↦ ite_eq_left (h₁.1 b b.2 v.2)]
      exact congrFun (congrFun ((hu₁.1 b).op_eq_of_eq (dite_eq_left b.2) _ _) _) _
    · have hb : b.1 ∉ L₁.cells := Finset.disjoint_right.mp hcells b.2
      rw [show (fun v : {v // v ∈ Γ.cell b} ↦ z v) = fun v : {v // v ∈ Γ.cell b} ↦ y v from
        funext fun v ↦ ite_eq_right fun hv ↦ Finset.disjoint_left.mp hR hv (h₂.1 b b.2 v.2)]
      exact congrFun (congrFun ((hu₂.1 b).op_eq_of_eq (dite_eq_right hb) _ _) _) _
  · rw [prod_free, prod_free, prod_free, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ ↦ ?_
    dsimp only
    by_cases hs : s ∈ R₁
    · have hsR₂ : s ∉ R₂ := Finset.disjoint_left.mp hR hs
      have hs₂ := h₂.not_mem_biUnion hsR₂
      rw [dite_eq_right hs₂, h₂.2 ⟨s, hs₂⟩ hsR₂, show z s = x s from ite_eq_left hs, one_apply_eq,
        mul_one]
      by_cases hs₁ : s ∈ L₁.cells.biUnion Γ.cell
      · have hs' : s ∈ (par L₁ L₂ h₁ h₂ hR).cells.biUnion Γ.cell :=
          Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_left hs₁
        rw [dite_eq_left hs', dite_eq_left hs₁]
      · have hs' : s ∉ (par L₁ L₂ h₁ h₂ hR).cells.biUnion Γ.cell := by
          change s ∉ (L₁.cells ∪ L₂.cells).biUnion Γ.cell
          rw [Finset.union_biUnion, Finset.mem_union]
          exact fun h ↦ h.elim hs₁ hs₂
        rw [dite_eq_right hs', dite_eq_right hs₁]
        exact congrFun (congrFun ((hu₁.2 _).op_eq_of_eq (ite_eq_left hs) _ _) _) _
    · have hs₁ := h₁.not_mem_biUnion hs
      rw [dite_eq_right hs₁, h₁.2 ⟨s, hs₁⟩ hs, show z s = y s from ite_eq_right hs, one_apply_eq,
        one_mul]
      by_cases hs₂ : s ∈ L₂.cells.biUnion Γ.cell
      · have hs' : s ∈ (par L₁ L₂ h₁ h₂ hR).cells.biUnion Γ.cell :=
          Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_right hs₂
        rw [dite_eq_left hs', dite_eq_left hs₂]
      · have hs' : s ∉ (par L₁ L₂ h₁ h₂ hR).cells.biUnion Γ.cell := by
          change s ∉ (L₁.cells ∪ L₂.cells).biUnion Γ.cell
          rw [Finset.union_biUnion, Finset.mem_union]
          exact fun h ↦ h.elim hs₁ hs₂
        rw [dite_eq_right hs', dite_eq_right hs₂]
        exact congrFun (congrFun ((hu₂.2 _).op_eq_of_eq (ite_eq_right hs) _ _) _) _

omit [Fintype S] [∀ s, Fintype (X s)] in
/-- Two layers run as one layer use the cells of both, at the sum of the costs. -/
theorem gateCount_par (hne : ∀ b, (Γ.cell b).Nonempty) (h₁ : L₁.IsIn R₁) (h₂ : L₂.IsIn R₂)
    (hR : Disjoint R₁ R₂) :
    (par L₁ L₂ h₁ h₂ hR).gateCount = L₁.gateCount + L₂.gateCount := by
  rw [gateCount_eq_sum, gateCount_eq_sum, gateCount_eq_sum]
  exact Finset.sum_union (disjoint_cells hne h₁ h₂ hR)

end Layer

/-! ### Two circuits in parallel -/

namespace UnitaryCircuit

variable {R₁ R₂ : Finset S}

/-- The layers of two circuits inside disjoint regions run in parallel, merged greedily: a layer
of depth `0` at the head of either list is emitted alone, and two layers of depth `1` at the
heads are run as one layer. -/
def parLayers (hR : Disjoint R₁ R₂) : (Ls₁ Ls₂ : List (Layer Γ KrausGate X X)) →
    (∀ L ∈ Ls₁, L.IsIn R₁) → (∀ L ∈ Ls₂, L.IsIn R₂) → List (Layer Γ KrausGate X X)
  | [], Ls₂, _, _ => Ls₂
  | L₁ :: Ls₁, [], _, _ => L₁ :: Ls₁
  | L₁ :: Ls₁, L₂ :: Ls₂, h₁, h₂ =>
    if L₁.depth = 0 then
      L₁ :: parLayers hR Ls₁ (L₂ :: Ls₂) (fun L hL ↦ h₁ L (List.mem_cons_of_mem L₁ hL)) h₂
    else if L₂.depth = 0 then
      L₂ :: parLayers hR (L₁ :: Ls₁) Ls₂ h₁ (fun L hL ↦ h₂ L (List.mem_cons_of_mem L₂ hL))
    else
      Layer.par L₁ L₂ (h₁ L₁ List.mem_cons_self) (h₂ L₂ List.mem_cons_self) hR ::
        parLayers hR Ls₁ Ls₂ (fun L hL ↦ h₁ L (List.mem_cons_of_mem L₁ hL))
          (fun L hL ↦ h₂ L (List.mem_cons_of_mem L₂ hL))

variable (hR : Disjoint R₁ R₂)

omit [Fintype S] in
/-- The layers run in parallel are unitary and act inside the union of the regions. -/
theorem forall_parLayers : (Ls₁ Ls₂ : List (Layer Γ KrausGate X X)) →
    (h₁ : ∀ L ∈ Ls₁, L.IsIn R₁) → (h₂ : ∀ L ∈ Ls₂, L.IsIn R₂) →
    (∀ L ∈ Ls₁, L.Forall KrausGate.ev KrausFamily.IsUnitary) →
    (∀ L ∈ Ls₂, L.Forall KrausGate.ev KrausFamily.IsUnitary) →
    ∀ L ∈ parLayers hR Ls₁ Ls₂ h₁ h₂,
      L.Forall KrausGate.ev KrausFamily.IsUnitary ∧ L.IsIn (R₁ ∪ R₂)
  | [], Ls₂, _, h₂, _, u₂ => by
    rw [parLayers]
    exact fun L hL ↦ ⟨u₂ L hL, (h₂ L hL).mono Finset.subset_union_right⟩
  | L₁ :: Ls₁, [], h₁, _, u₁, _ => by
    rw [parLayers]
    exact fun L hL ↦ ⟨u₁ L hL, (h₁ L hL).mono Finset.subset_union_left⟩
  | L₁ :: Ls₁, L₂ :: Ls₂, h₁, h₂, u₁, u₂ => by
    have h₁' : ∀ L ∈ Ls₁, L.IsIn R₁ := fun L hL ↦ h₁ L (List.mem_cons_of_mem L₁ hL)
    have h₂' : ∀ L ∈ Ls₂, L.IsIn R₂ := fun L hL ↦ h₂ L (List.mem_cons_of_mem L₂ hL)
    have u₁' := fun L hL ↦ u₁ L (List.mem_cons_of_mem L₁ hL)
    have u₂' := fun L hL ↦ u₂ L (List.mem_cons_of_mem L₂ hL)
    rw [parLayers]
    split_ifs
    · exact List.forall_mem_cons.mpr ⟨⟨u₁ L₁ List.mem_cons_self,
        (h₁ L₁ List.mem_cons_self).mono Finset.subset_union_left⟩,
        forall_parLayers Ls₁ (L₂ :: Ls₂) h₁' h₂ u₁' u₂⟩
    · exact List.forall_mem_cons.mpr ⟨⟨u₂ L₂ List.mem_cons_self,
        (h₂ L₂ List.mem_cons_self).mono Finset.subset_union_right⟩,
        forall_parLayers (L₁ :: Ls₁) Ls₂ h₁ h₂' u₁ u₂'⟩
    · exact List.forall_mem_cons.mpr ⟨⟨Layer.forall_isUnitary_par _ _ hR
        (u₁ L₁ List.mem_cons_self) (u₂ L₂ List.mem_cons_self), Layer.isIn_par _ _ hR⟩,
        forall_parLayers Ls₁ Ls₂ h₁' h₂' u₁' u₂'⟩

omit [Fintype S] [∀ s, Fintype (X s)] in
/-- The depth of the layers run in parallel is at most the larger of the two depths. -/
theorem sum_depth_parLayers_le : (Ls₁ Ls₂ : List (Layer Γ KrausGate X X)) →
    (h₁ : ∀ L ∈ Ls₁, L.IsIn R₁) → (h₂ : ∀ L ∈ Ls₂, L.IsIn R₂) →
    ((parLayers hR Ls₁ Ls₂ h₁ h₂).map Layer.depth).sum ≤
      max (Ls₁.map Layer.depth).sum (Ls₂.map Layer.depth).sum
  | [], Ls₂, _, _ => by rw [parLayers]; simp
  | L₁ :: Ls₁, [], _, _ => by rw [parLayers]; simp
  | L₁ :: Ls₁, L₂ :: Ls₂, h₁, h₂ => by
    have h₁' : ∀ L ∈ Ls₁, L.IsIn R₁ := fun L hL ↦ h₁ L (List.mem_cons_of_mem L₁ hL)
    have h₂' : ∀ L ∈ Ls₂, L.IsIn R₂ := fun L hL ↦ h₂ L (List.mem_cons_of_mem L₂ hL)
    rw [parLayers]
    split_ifs with hd₁ hd₂
    · have := sum_depth_parLayers_le Ls₁ (L₂ :: Ls₂) h₁' h₂
      simp only [List.map_cons, List.sum_cons] at this ⊢
      omega
    · have := sum_depth_parLayers_le (L₁ :: Ls₁) Ls₂ h₁ h₂'
      simp only [List.map_cons, List.sum_cons] at this ⊢
      omega
    · have := sum_depth_parLayers_le Ls₁ Ls₂ h₁' h₂'
      have := L₁.depth_le_one
      have := L₂.depth_le_one
      have :=
        (Layer.par L₁ L₂ (h₁ L₁ List.mem_cons_self) (h₂ L₂ List.mem_cons_self) hR).depth_le_one
      simp only [List.map_cons, List.sum_cons] at *
      omega

omit [Fintype S] [∀ s, Fintype (X s)] in
/-- On a geometry whose cells are nonempty, the gate count of the layers run in parallel is the
sum of the two gate counts. -/
theorem sum_gateCount_parLayers (hne : ∀ b, (Γ.cell b).Nonempty) :
    (Ls₁ Ls₂ : List (Layer Γ KrausGate X X)) →
    (h₁ : ∀ L ∈ Ls₁, L.IsIn R₁) → (h₂ : ∀ L ∈ Ls₂, L.IsIn R₂) →
    ((parLayers hR Ls₁ Ls₂ h₁ h₂).map Layer.gateCount).sum =
      (Ls₁.map Layer.gateCount).sum + (Ls₂.map Layer.gateCount).sum
  | [], Ls₂, _, _ => by rw [parLayers]; simp
  | L₁ :: Ls₁, [], _, _ => by rw [parLayers]; simp
  | L₁ :: Ls₁, L₂ :: Ls₂, h₁, h₂ => by
    have h₁' : ∀ L ∈ Ls₁, L.IsIn R₁ := fun L hL ↦ h₁ L (List.mem_cons_of_mem L₁ hL)
    have h₂' : ∀ L ∈ Ls₂, L.IsIn R₂ := fun L hL ↦ h₂ L (List.mem_cons_of_mem L₂ hL)
    rw [parLayers]
    split_ifs with hd₁ hd₂
    · have := sum_gateCount_parLayers hne Ls₁ (L₂ :: Ls₂) h₁' h₂
      simp only [List.map_cons, List.sum_cons] at this ⊢
      omega
    · have := sum_gateCount_parLayers hne (L₁ :: Ls₁) Ls₂ h₁ h₂'
      simp only [List.map_cons, List.sum_cons] at this ⊢
      omega
    · have := sum_gateCount_parLayers hne Ls₁ Ls₂ h₁' h₂'
      have := Layer.gateCount_par hne (h₁ L₁ List.mem_cons_self) (h₂ L₂ List.mem_cons_self) hR
      simp only [List.map_cons, List.sum_cons] at *
      omega

private theorem op_eq_op_of_layers_eq {c c' : UnitaryCircuit Γ X} (h : c.layers = c'.layers) :
    c.op = c'.op := by
  obtain ⟨Ls, _⟩ := c
  obtain ⟨Ls', _⟩ := c'
  subst h
  rfl

/-- On a geometry whose cells are nonempty, the operator of the layers of two unitary circuits
inside disjoint regions run in parallel is the product of their operators. -/
theorem op_parLayers (hne : ∀ b, (Γ.cell b).Nonempty) :
    (Ls₁ Ls₂ : List (Layer Γ KrausGate X X)) →
    (h₁ : ∀ L ∈ Ls₁, L.IsIn R₁) → (h₂ : ∀ L ∈ Ls₂, L.IsIn R₂) →
    (c c₁ c₂ : UnitaryCircuit Γ X) → c₁.layers = Ls₁ → c₂.layers = Ls₂ →
    c.layers = parLayers hR Ls₁ Ls₂ h₁ h₂ → c.op = c₁.op * c₂.op
  | [], Ls₂, _, _, c, c₁, c₂, e₁, e₂, e => by
    rw [parLayers] at e
    rw [op_eq_one e₁, Matrix.one_mul]
    exact op_eq_op_of_layers_eq (e.trans e₂.symm)
  | L₁ :: Ls₁, [], _, _, c, c₁, c₂, e₁, e₂, e => by
    rw [parLayers] at e
    rw [op_eq_one e₂, Matrix.mul_one]
    exact op_eq_op_of_layers_eq (e.trans e₁.symm)
  | L₁ :: Ls₁, L₂ :: Ls₂, h₁, h₂, c, c₁, c₂, e₁, e₂, e => by
    have h₁' : ∀ L ∈ Ls₁, L.IsIn R₁ := fun L hL ↦ h₁ L (List.mem_cons_of_mem L₁ hL)
    have h₂' : ∀ L ∈ Ls₂, L.IsIn R₂ := fun L hL ↦ h₂ L (List.mem_cons_of_mem L₂ hL)
    have hc₂ : c₂.IsIn R₂ := fun L hL ↦ h₂ L (e₂ ▸ hL)
    have hu₁ := c₁.isUnitary L₁ (e₁ ▸ List.mem_cons_self)
    have hu₂ := c₂.isUnitary L₂ (e₂ ▸ List.mem_cons_self)
    obtain ⟨i₁⟩ := (Layer.nonempty_unique_index_of_forall_isUnitary hu₁).map fun u ↦ u.default
    obtain ⟨i₂⟩ := (Layer.nonempty_unique_index_of_forall_isUnitary hu₂).map fun u ↦ u.default
    have hL₁ := Layer.kraus_mem_supportedOperators KrausGate.ev (h₁ L₁ List.mem_cons_self) i₁
    rw [parLayers] at e
    split_ifs at e with hd₁ hd₂
    · rw [op_eq_tail_op_mul e i₁, op_parLayers hne Ls₁ (L₂ :: Ls₂) h₁' h₂ c.tail c₁.tail c₂
        (congrArg List.tail e₁) e₂ (congrArg List.tail e), op_eq_tail_op_mul e₁ i₁,
        Matrix.mul_assoc, Matrix.mul_assoc,
        (commute_of_mem_supportedOperators_of_disjoint hL₁ (op_mem_supportedOperators hc₂)
          hR).eq]
    · rw [op_eq_tail_op_mul e i₂, op_parLayers hne (L₁ :: Ls₁) Ls₂ h₁ h₂' c.tail c₁ c₂.tail
        e₁ (congrArg List.tail e₂) (congrArg List.tail e), op_eq_tail_op_mul e₂ i₂,
        Matrix.mul_assoc]
    · obtain ⟨ip⟩ := (Layer.nonempty_unique_index_of_forall_isUnitary
        (Layer.forall_isUnitary_par (h₁ L₁ List.mem_cons_self) (h₂ L₂ List.mem_cons_self) hR
          hu₁ hu₂)).map fun u ↦ u.default
      rw [op_eq_tail_op_mul e ip, op_parLayers hne Ls₁ Ls₂ h₁' h₂' c.tail c₁.tail c₂.tail
        (congrArg List.tail e₁) (congrArg List.tail e₂) (congrArg List.tail e),
        Layer.kraus_par hne _ _ hR hu₁ hu₂ ip i₁ i₂, op_eq_tail_op_mul e₁ i₁,
        op_eq_tail_op_mul e₂ i₂, Matrix.mul_assoc, ← Matrix.mul_assoc c₂.tail.op,
        ← (commute_of_mem_supportedOperators_of_disjoint hL₁
          (op_mem_supportedOperators hc₂.tail) hR).eq]
      simp only [Matrix.mul_assoc]

/-- **Two circuits in parallel.** Two unitary circuits inside disjoint regions, run in parallel:
their layers merged greedily by `parLayers`. -/
def par (c₁ c₂ : UnitaryCircuit Γ X) (h₁ : c₁.IsIn R₁) (h₂ : c₂.IsIn R₂)
    (hR : Disjoint R₁ R₂) : UnitaryCircuit Γ X :=
  ⟨parLayers hR c₁.layers c₂.layers h₁ h₂, fun L hL ↦
    (forall_parLayers hR _ _ h₁ h₂ c₁.isUnitary c₂.isUnitary L hL).1⟩

variable {c₁ c₂ : UnitaryCircuit Γ X} (h₁ : c₁.IsIn R₁) (h₂ : c₂.IsIn R₂)

omit [Fintype S] in
theorem isIn_par : (c₁.par c₂ h₁ h₂ hR).IsIn (R₁ ∪ R₂) := fun L hL ↦
  (forall_parLayers hR _ _ h₁ h₂ c₁.isUnitary c₂.isUnitary L hL).2

/-- Two circuits run in parallel have depth at most the larger of their depths. -/
theorem depth_par_le : (c₁.par c₂ h₁ h₂ hR).depth ≤ max c₁.depth c₂.depth := by
  simp only [depth_eq_sum]
  exact sum_depth_parLayers_le hR _ _ h₁ h₂

/-- On a geometry whose cells are nonempty, two circuits run in parallel have the sum of their
gate counts. -/
theorem gateCount_par (hne : ∀ b, (Γ.cell b).Nonempty) :
    (c₁.par c₂ h₁ h₂ hR).gateCount = c₁.gateCount + c₂.gateCount := by
  simp only [gateCount_eq_sum]
  exact sum_gateCount_parLayers hR hne _ _ h₁ h₂

/-- **Circuits in parallel.** On a geometry whose cells are nonempty, the operator of two unitary
circuits inside disjoint regions run in parallel is the product of their operators. -/
theorem op_par (hne : ∀ b, (Γ.cell b).Nonempty) : (c₁.par c₂ h₁ h₂ hR).op = c₁.op * c₂.op :=
  op_parLayers hR hne _ _ h₁ h₂ _ c₁ c₂ rfl rfl rfl

end UnitaryCircuit

namespace IsUnitaryCircuitOn

variable {R₁ R₂ : Finset S} {T T₁ T₂ : ℕ} {U₁ U₂ : Matrix (Config X) (Config X) ℂ}

/-- **Circuits in parallel.** On a geometry whose cells are nonempty, two circuits inside
disjoint regions run in the same layers: their product is a circuit inside the union, of depth
at most the larger depth. -/
theorem par (hne : ∀ b, (Γ.cell b).Nonempty) (hR : Disjoint R₁ R₂)
    (h₁ : IsUnitaryCircuitOn Γ R₁ T₁ U₁) (h₂ : IsUnitaryCircuitOn Γ R₂ T₂ U₂) :
    IsUnitaryCircuitOn Γ (R₁ ∪ R₂) (max T₁ T₂) (U₁ * U₂) := by
  obtain ⟨c₁, hc₁, hd₁, rfl⟩ := h₁
  obtain ⟨c₂, hc₂, hd₂, rfl⟩ := h₂
  exact ⟨c₁.par c₂ hc₁ hc₂ hR, UnitaryCircuit.isIn_par hR hc₁ hc₂,
    (UnitaryCircuit.depth_par_le hR hc₁ hc₂).trans (max_le_max hd₁ hd₂),
    UnitaryCircuit.op_par hR hc₁ hc₂ hne⟩

/-- **Circuits in parallel.** On a geometry whose cells are nonempty, a family of pairwise
commuting circuits of depth `T` inside pairwise disjoint regions is a circuit of depth `T`
inside the union. -/
theorem finset_noncommProd (hne : ∀ b, (Γ.cell b).Nonempty) {κ : Type*} (s : Finset κ)
    (R : κ → Finset S) (hR : (s : Set κ).PairwiseDisjoint R)
    (U : κ → Matrix (Config X) (Config X) ℂ) (hU : ∀ i ∈ s, IsUnitaryCircuitOn Γ (R i) T (U i))
    (hcomm : (s : Set κ).Pairwise (Function.onFun Commute U)) :
    IsUnitaryCircuitOn Γ (s.biUnion R) T (s.noncommProd U hcomm) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one Γ X (∅ : Finset S) T
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    have hdisj : Disjoint (R a) (s.biUnion R) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hR (by simp) (by simp [hi]) (fun h ↦ ha (h ▸ hi))
    have := (hU a (by simp)).par hne hdisj
      (ih (hR.subset (by simp)) (fun i hi ↦ hU i (by simp [hi])) (hcomm.mono (by simp)))
    rw [max_self] at this
    simpa [Finset.biUnion_insert] using this

/-- **Circuits in parallel.** On a geometry whose cells are nonempty, the product along a list of
circuits of depth `T` inside pairwise disjoint regions is a circuit of depth `T` inside the union
of the regions. -/
theorem list_prod (hne : ∀ b, (Γ.cell b).Nonempty) {κ : Type*} [DecidableEq κ]
    (R : κ → Finset S) (U : κ → Matrix (Config X) (Config X) ℂ) :
    (l : List κ) → l.Pairwise (Function.onFun Disjoint R) →
      (∀ i ∈ l, IsUnitaryCircuitOn Γ (R i) T (U i)) →
      IsUnitaryCircuitOn Γ (l.toFinset.biUnion R) T (l.map U).prod
  | [], _, _ => by simpa using one Γ X (∅ : Finset S) T
  | i :: l, hl, hU => by
    rw [List.pairwise_cons] at hl
    have hdisj : Disjoint (R i) (l.toFinset.biUnion R) := by
      rw [Finset.disjoint_biUnion_right]
      exact fun j hj ↦ hl.1 j (List.mem_toFinset.mp hj)
    have := (hU i List.mem_cons_self).par hne hdisj
      (list_prod hne R U l hl.2 fun j hj ↦ hU j (List.mem_cons_of_mem i hj))
    rw [max_self] at this
    simpa [List.toFinset_cons, Finset.biUnion_insert] using this

end IsUnitaryCircuitOn

end QuantumCircuit
