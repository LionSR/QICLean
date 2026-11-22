/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Model.Unitary
import QICLean.Circuit.Protocol.Teleportation.Hop

/-!
# Teleportation along chains of hops in one round

A list of hops (`QuantumCircuit.TeleportHop`), the most recent first, is *valid* when every hop
`h` meets the hops `hs` before it only through its site `c`, which may be the site `f` of an
earlier hop: the sites `e` and `f` of `h` are not sites of `hs`, and its site `c` is not a site
`c` or `e` of `hs`. The hops then form chains `c₀ → f₀ = c₁ → f₁ = c₂ → ⋯`, any number of them.

The *teleportation round* of a valid list, after a unitary circuit `u`, applies `u`, the first
gates of all hops in one layer, the second gates of all hops in one layer, measures the sites `c`
and `e` of every hop, and corrects by the inverse of the one-site unitaries that the hops leave.
On the vectors `v` such that `u v` has `|0⟩` at the sites `e` and `f` of every hop, it implements
`P u`, `P` the permutation of sites `S_{h_1} ⋯ S_{h_H}`, `S_h` exchanging the sites `c` and `f` of
`h`, with the scalar `d^{-H}` on every branch
(`QuantumCircuit.TeleportHop.isImplementationOn_round`).
The two layers have depth at most `2` whatever the lengths of the chains: this is the
constant-depth teleportation of arXiv:2307.01696, paragraph "Tree-RG circuit with measurements".

## Main definitions

* `QuantumCircuit.Layer.ofList` — the layer of gates on pairwise disjoint cells given by a list.
* `QuantumCircuit.TeleportHop.Valid`, `QuantumCircuit.TeleportHop.pairSites`,
  `QuantumCircuit.TeleportHop.measuredSites`.
* `QuantumCircuit.TeleportHop.sitePerm` — the permutation of sites of a list of hops.
* `QuantumCircuit.TeleportHop.chainFrame`, `QuantumCircuit.TeleportHop.chainPre`.
* `QuantumCircuit.TeleportHop.round` — the teleportation round, a measurement circuit.

## Main results

* `QuantumCircuit.Layer.kraus_ofList` — the Kraus operator of a layer given by a list is the
  product of its gates along the list.
* `QuantumCircuit.sitePermOp_mul_piKronecker` — moving one-site operators across a permutation of
  sites.
* `QuantumCircuit.TeleportHop.chainPre_mulVec` — the chains of hops before the correction.
* `QuantumCircuit.TeleportHop.depth_round_le`, `QuantumCircuit.TeleportHop.forall_round`,
  `QuantumCircuit.TeleportHop.isImplementationOn_round`.

The declarations restate `TNLean/Circuit/Teleportation/Round.lean` at commit `414a18fb88`
(Apache-2.0). The changes: any finite type of sites and any geometry; the layers are core
layers of plain gates on the cells of the hops, `Layer.ofList` replacing `layerOfList`; the round
is a circuit of the circuit core, the unitary circuit before it a `UnitaryCircuit`, its
measurement and correction `Circuit.measureCorrect`, its depth bounded by `≤`; the permutation
matrix of a list of hops is `ManyBody.sitePermOp (sitePerm hs)`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Tree-RG circuit with measurements".
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [DecidableEq S] {Γ : Geometry S}

/-! ### Layers given by lists -/

namespace Layer

section OfList

variable [Fintype S] {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] {ι : Type}
  (l : List ι) (key : ι → Γ.Cell) (G : ι → Matrix (Config X) (Config X) ℂ)
  (hl : l.Pairwise fun i j ↦ Disjoint (Γ.cell (key i)) (Γ.cell (key j)))
  (hne : ∀ i ∈ l, (Γ.cell (key i)).Nonempty)
  (hG : ∀ i ∈ l, G i ∈ supportedOperators X (Γ.cell (key i)))

omit [Fintype S] [DecidableEq S] in
include hl hne in
private theorem eq_of_key_eq {i j : ι} (hi : i ∈ l) (hj : j ∈ l) (h : key i = key j) : i = j := by
  by_contra hij
  have : Std.Symm fun i j : ι ↦ Disjoint (Γ.cell (key i)) (Γ.cell (key j)) :=
    ⟨fun _ _ h ↦ h.symm⟩
  obtain ⟨x, hx⟩ := hne i hi
  exact Finset.disjoint_left.mp (hl.forall hi hj hij) hx (h ▸ hx)

omit [Fintype S] [DecidableEq S] in
private theorem exists_of_mem_cells {b : Γ.Cell} (hb : b ∈ (l.map key).toFinset) :
    ∃ i ∈ l, key i = b :=
  List.mem_map.mp (List.mem_toFinset.mp hb)

omit [Fintype S] [DecidableEq S] in
include hl in
private theorem pairwiseDisjoint_toFinset :
    (((l.map key).toFinset : Finset Γ.Cell) : Set Γ.Cell).PairwiseDisjoint Γ.cell := by
  intro b hb b' hb' hbb'
  obtain ⟨i, hi, rfl⟩ := exists_of_mem_cells l key (Finset.mem_coe.mp hb)
  obtain ⟨j, hj, rfl⟩ := exists_of_mem_cells l key (Finset.mem_coe.mp hb')
  have : Std.Symm fun i j : ι ↦ Disjoint (Γ.cell (key i)) (Γ.cell (key j)) :=
    ⟨fun _ _ h ↦ h.symm⟩
  exact hl.forall hi hj fun h ↦ hbb' (h ▸ rfl)

/-- The member of the list whose cell is `b`. -/
private noncomputable def index (b : (l.map key).toFinset) : ι :=
  (exists_of_mem_cells l key b.2).choose

omit [Fintype S] [DecidableEq S] in
private theorem index_mem (b : (l.map key).toFinset) : index l key b ∈ l :=
  (exists_of_mem_cells l key b.2).choose_spec.1

omit [Fintype S] [DecidableEq S] in
private theorem key_index (b : (l.map key).toFinset) : key (index l key b) = b :=
  (exists_of_mem_cells l key b.2).choose_spec.2

include hG in
private theorem mem_supportedOperators_index (b : (l.map key).toFinset) :
    G (index l key b) ∈ supportedOperators X (Γ.cell b) :=
  key_index l key b ▸ hG _ (index_mem l key b)

/-- The matrix on the cell `b` whose placement is the gate of the list on `b`. -/
private noncomputable def cellMatrix (b : (l.map key).toFinset) :
    Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ :=
  (exists_eq_place_of_mem_supportedOperators (mem_supportedOperators_index l key G hG b)).choose

private theorem place_cellMatrix (b : (l.map key).toFinset) :
    place (Γ.cell b) (cellMatrix l key G hG b) = G (index l key b) :=
  (exists_eq_place_of_mem_supportedOperators
    (mem_supportedOperators_index l key G hG b)).choose_spec.symm

/-- The layer of the gates `G i` on the cells `key i`, for `i` in the list `l`, the cells being
pairwise disjoint, with the identity elsewhere. -/
noncomputable def ofList : Layer Γ KrausGate X X :=
  ofCells (l.map key).toFinset (pairwiseDisjoint_toFinset l key hl) fun b ↦
    KrausFamily.single (cellMatrix l key G hG b)

include hne in
/-- **A layer given by a list.** Every Kraus operator of the layer is the product of its gates
along the list. -/
theorem kraus_ofList (i : (ofList l key G hl hG).Index) :
    (ofList l key G hl hG).kraus KrausGate.ev i = (l.map G).prod := by
  have hmem : ∀ j ∈ l, key j ∈ (l.map key).toFinset :=
    fun j hj ↦ List.mem_toFinset.mpr (List.mem_map_of_mem hj)
  let l' : List (l.map key).toFinset := l.pmap (fun j hj ↦ ⟨key j, hmem j hj⟩) fun _ h ↦ h
  have hnodup : l.Nodup := hl.imp_of_mem fun hi _ hd heq ↦ by
    subst heq
    obtain ⟨x, hx⟩ := hne _ hi
    exact Finset.disjoint_left.mp hd hx hx
  have hl' : l'.Nodup := hnodup.pmap fun a ha b hb h ↦
    eq_of_key_eq l key hl hne ha hb (congrArg Subtype.val h)
  have hall : ∀ c, c ∈ l' := fun ⟨b, hb⟩ ↦ by
    obtain ⟨j, hj, rfl⟩ := exists_of_mem_cells l key hb
    exact List.mem_pmap.mpr ⟨j, hj, rfl⟩
  refine (kraus_ofCells KrausGate.ev _ _ _ l' hl' hall i).trans ?_
  rw [List.map_pmap]
  refine congrArg List.prod ((List.pmap_congr_left l fun j hj _ _ ↦ ?_).trans
    (List.pmap_eq_map (p := fun j ↦ j ∈ l) (f := G) fun _ h ↦ h))
  exact (place_cellMatrix l key G hG _).trans
    (congrArg G (eq_of_key_eq l key hl hne (index_mem l key _) hj (key_index l key _)))

private theorem cellMatrix_mem_unitaryGroup [∀ s, Nonempty (X s)]
    (hu : ∀ i ∈ l, G i ∈ unitaryGroup (Config X) ℂ) (b : (l.map key).toFinset) :
    cellMatrix l key G hG b ∈ unitaryGroup _ ℂ := by
  refine (place_mem_unitaryGroup_iff (D := Γ.cell b)).mp ?_
  rw [place_cellMatrix l key G hG b]
  exact hu _ (index_mem l key b)

/-- A layer given by a list of unitaries is unitary. -/
theorem forall_isUnitary_ofList [∀ s, Nonempty (X s)]
    (hu : ∀ i ∈ l, G i ∈ unitaryGroup (Config X) ℂ) :
    (ofList l key G hl hG).Forall KrausGate.ev KrausFamily.IsUnitary :=
  forall_ofCells KrausGate.ev (KrausFamily.isUnitary_single (one_mem _)) _ _ _
    fun b ↦ KrausFamily.isUnitary_single (cellMatrix_mem_unitaryGroup l key G hG hu b)

end OfList

end Layer

/-! ### Permutations of sites and product operators -/

/-- **Moving one-site operators across a permutation of sites.** -/
theorem sitePermOp_mul_piKronecker [Fintype S] {α : Type} [Fintype α] [DecidableEq α]
    (π : Equiv.Perm S) (g : S → Matrix α α ℂ) :
    sitePermOp π * piKronecker (ι := fun _ ↦ α) g =
      piKronecker (ι := fun _ ↦ α) (fun i ↦ g (π.symm i)) * sitePermOp π := by
  refine ext_iff_mulVec.mpr fun v ↦ funext fun y ↦ ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, sitePermOp_mulVec, sitePermOp_mulVec]
  simp only [mulVec, dotProduct, piKronecker_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr π (Equiv.refl α)) _ _ fun x ↦ ?_
  have hx : (Equiv.arrowCongr π (Equiv.refl α) x) ∘ π = x := by
    funext s
    simp [Equiv.arrowCongr_apply]
  rw [hx]
  congr 1
  refine Fintype.prod_equiv π _ _ fun s ↦ ?_
  simp [Equiv.arrowCongr_apply]

/-! ### Lists of hops -/

namespace TeleportHop

/-- The sites `c`, `e`, `f` of a hop. -/
def sites (h : TeleportHop Γ) : Finset S := {h.c, h.e, h.f}

/-- The sites of all hops of a list. -/
def allSites : List (TeleportHop Γ) → Finset S
  | [] => ∅
  | h :: hs => h.sites ∪ allSites hs

/-- The sites `e` and `f` of all hops of a list, which carry `|0⟩` before the round. -/
def pairSites : List (TeleportHop Γ) → Finset S
  | [] => ∅
  | h :: hs => {h.e, h.f} ∪ pairSites hs

/-- The sites `c` and `e` of all hops of a list, measured in the round. -/
def measuredSites : List (TeleportHop Γ) → Finset S
  | [] => ∅
  | h :: hs => {h.c, h.e} ∪ measuredSites hs

/-- A list of hops, the most recent first, is *valid* when every hop meets the earlier ones only
through its site `c`, which is not a site `c` or `e` of an earlier hop.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" (registers teleported
along chains of nearest-neighbour entangled pairs). -/
def Valid : List (TeleportHop Γ) → Prop
  | [] => True
  | h :: hs => Valid hs ∧ h.e ∉ allSites hs ∧ h.f ∉ allSites hs ∧
      ∀ h' ∈ hs, h.c ≠ h'.c ∧ h.c ≠ h'.e

theorem valid_nil : Valid ([] : List (TeleportHop Γ)) :=
  trivial

theorem mem_allSites {hs : List (TeleportHop Γ)} {i : S} :
    i ∈ allSites hs ↔ ∃ h ∈ hs, i ∈ h.sites := by
  induction hs with
  | nil => simp [allSites]
  | cons h hs ih => simp [allSites, ih]

theorem measuredSites_subset_allSites (hs : List (TeleportHop Γ)) :
    measuredSites hs ⊆ allSites hs := by
  induction hs with
  | nil => simp [measuredSites]
  | cons h hs ih =>
    intro i hi
    simp only [measuredSites, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with (rfl | rfl) | hi
    · simp [allSites, sites]
    · simp [allSites, sites]
    · exact Finset.mem_union_right _ (ih hi)

/-- The sites `c` and `e` of the hops of a valid list are not the sites `c`, `e`, `f` of a later
hop. -/
theorem disjoint_measuredSites {h : TeleportHop Γ} {hs : List (TeleportHop Γ)}
    (hv : Valid (h :: hs)) : Disjoint (measuredSites hs) h.sites := by
  rw [Finset.disjoint_right]
  intro i hmem₀ hi
  simp only [sites, Finset.mem_insert, Finset.mem_singleton] at hmem₀
  rcases hmem₀ with rfl | rfl | rfl
  · obtain ⟨-, -, -, hc⟩ := hv
    induction hs with
    | nil => simp [measuredSites] at hi
    | cons h' hs ih =>
      simp only [measuredSites, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with (hi | hi) | hi
      · exact (hc h' List.mem_cons_self).1 hi
      · exact (hc h' List.mem_cons_self).2 hi
      · exact ih hi fun h'' hh ↦ hc h'' (List.mem_cons_of_mem _ hh)
  · exact hv.2.1 (measuredSites_subset_allSites hs hi)
  · exact hv.2.2.1 (measuredSites_subset_allSites hs hi)

/-! ### The layers of a list of hops -/

theorem pairwise_disjoint_one : ∀ {hs : List (TeleportHop Γ)}, Valid hs →
    hs.Pairwise fun h h' ↦ Disjoint (Γ.cell h.b₁) (Γ.cell h'.b₁)
  | [], _ => List.Pairwise.nil
  | h :: hs, ⟨hv, he, hf, _⟩ => by
    refine List.Pairwise.cons (fun h' hh' ↦ ?_) (pairwise_disjoint_one hv)
    rw [h.cell_b₁, h'.cell_b₁, Finset.disjoint_left]
    intro i hmem₀ hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem₀
    rcases hmem₀ with rfl | rfl
    · exact he (mem_allSites.mpr ⟨h', hh', by
        simp only [sites, Finset.mem_insert, Finset.mem_singleton] at hi ⊢; tauto⟩)
    · exact hf (mem_allSites.mpr ⟨h', hh', by
        simp only [sites, Finset.mem_insert, Finset.mem_singleton] at hi ⊢; tauto⟩)

theorem pairwise_disjoint_two : ∀ {hs : List (TeleportHop Γ)}, Valid hs →
    hs.Pairwise fun h h' ↦ Disjoint (Γ.cell h.b₂) (Γ.cell h'.b₂)
  | [], _ => List.Pairwise.nil
  | h :: hs, ⟨hv, he, _, hc⟩ => by
    refine List.Pairwise.cons (fun h' hh' ↦ ?_) (pairwise_disjoint_two hv)
    rw [h.cell_b₂, h'.cell_b₂, Finset.disjoint_left]
    intro i hmem₀ hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem₀
    rcases hmem₀ with rfl | rfl
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi
      · exact (hc h' hh').1 hi
      · exact (hc h' hh').2 hi
    · exact he (mem_allSites.mpr ⟨h', hh', by
        simp only [sites, Finset.mem_insert, Finset.mem_singleton] at hi ⊢; tauto⟩)

/-- The permutation of sites of a list of hops: the product of the exchanges of the sites `c`
and `f`, the most recent leftmost. -/
def sitePerm : List (TeleportHop Γ) → Equiv.Perm S
  | [] => 1
  | h :: hs => Equiv.swap h.c h.f * sitePerm hs

theorem sitePerm_apply_of_notMem {hs : List (TeleportHop Γ)} {i : S}
    (hi : i ∉ allSites hs) : sitePerm hs i = i := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    have hi' : i ∉ h.sites := fun h' ↦ hi (Finset.mem_union_left _ h')
    simp only [sites, Finset.mem_insert, Finset.mem_singleton, not_or] at hi'
    rw [sitePerm, Equiv.Perm.mul_apply, ih fun h' ↦ hi (Finset.mem_union_right _ h'),
      Equiv.swap_apply_of_ne_of_ne hi'.1 hi'.2.2]

variable {d : ℕ} [NeZero d]

/-- The one-site unitaries left by a list of hops, for the outcome `z`. -/
noncomputable def chainFrame : List (TeleportHop Γ) → Config (Qudits S d) →
    S → Matrix (Fin d) (Fin d) ℂ
  | [], _ => fun _ ↦ 1
  | h :: hs, z => fun i ↦ Function.update (chainFrame hs z) h.c 1 i * h.frame z i *
      Function.update (1 : S → Matrix (Fin d) (Fin d) ℂ) h.f (chainFrame hs z h.c) i

theorem chainFrame_mem_unitaryGroup (hs : List (TeleportHop Γ)) (z : Config (Qudits S d))
    (i : S) : chainFrame hs z i ∈ unitaryGroup (Fin d) ℂ := by
  induction hs generalizing i with
  | nil => exact one_mem _
  | cons h hs ih =>
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ (h.frame_mem_unitaryGroup z i)) ?_
    · simp only [Function.update_apply]; split_ifs
      · exact one_mem _
      · exact ih i
    · simp only [Function.update_apply]; split_ifs
      · exact ih _
      · exact one_mem _

theorem chainFrame_of_notMem (hs : List (TeleportHop Γ)) (z : Config (Qudits S d)) {i : S}
    (hi : i ∉ allSites hs) : chainFrame hs z i = 1 := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    have hi' : i ∉ h.sites := fun h' ↦ hi (Finset.mem_union_left _ h')
    have hrest : i ∉ allSites hs := fun h' ↦ hi (Finset.mem_union_right _ h')
    simp only [sites, Finset.mem_insert, Finset.mem_singleton, not_or] at hi'
    simp only [chainFrame, Function.update_of_ne hi'.1, Function.update_of_ne hi'.2.2,
      ih hrest, h.frame_of_ne z hi'.1 hi'.2.1 hi'.2.2, Pi.one_apply, mul_one]

variable [Fintype S]

/-- The first layer of a valid list of hops: the gates preparing the entangled pairs. -/
noncomputable def layerOne (hs : List (TeleportHop Γ)) (hv : Valid hs) :
    Layer Γ KrausGate (Qudits S d) (Qudits S d) :=
  Layer.ofList hs TeleportHop.b₁ (fun h ↦ h.gate₁) (pairwise_disjoint_one hv)
    fun h _ ↦ h.gate₁_mem_supportedOperators

/-- The second layer of a valid list of hops: the gates of the measurements in the basis of
maximally entangled pairs. -/
noncomputable def layerTwo (hs : List (TeleportHop Γ)) (hv : Valid hs) :
    Layer Γ KrausGate (Qudits S d) (Qudits S d) :=
  Layer.ofList hs TeleportHop.b₂ (fun h ↦ h.gate₂) (pairwise_disjoint_two hv)
    fun h _ ↦ h.gate₂_mem_supportedOperators

theorem forall_isUnitary_layerOne (hs : List (TeleportHop Γ)) (hv : Valid hs) :
    (layerOne (d := d) hs hv).Forall KrausGate.ev KrausFamily.IsUnitary :=
  Layer.forall_isUnitary_ofList _ _ _ _ _ fun h _ ↦ h.gate₁_mem_unitaryGroup

theorem forall_isUnitary_layerTwo (hs : List (TeleportHop Γ)) (hv : Valid hs) :
    (layerTwo (d := d) hs hv).Forall KrausGate.ev KrausFamily.IsUnitary :=
  Layer.forall_isUnitary_ofList _ _ _ _ _ fun h _ ↦ h.gate₂_mem_unitaryGroup

omit [NeZero d] in
theorem kraus_layerOne (hs : List (TeleportHop Γ)) (hv : Valid hs)
    (i : (layerOne (d := d) hs hv).Index) :
    (layerOne hs hv).kraus KrausGate.ev i = (hs.map fun h ↦ h.gate₁ (d := d)).prod :=
  Layer.kraus_ofList _ _ _ (pairwise_disjoint_one hv)
    (fun h _ ↦ h.cell_b₁ ▸ Finset.insert_nonempty _ _) _ i

omit [NeZero d] in
theorem kraus_layerTwo (hs : List (TeleportHop Γ)) (hv : Valid hs)
    (i : (layerTwo (d := d) hs hv).Index) :
    (layerTwo hs hv).kraus KrausGate.ev i = (hs.map fun h ↦ h.gate₂ (d := d)).prod :=
  Layer.kraus_ofList _ _ _ (pairwise_disjoint_two hv)
    (fun h _ ↦ h.cell_b₂ ▸ Finset.insert_nonempty _ _) _ i

/-! ### Chains of hops before the correction -/

/-- The permutation of sites of the hops keeps `|0⟩` at the sites of `D` when no hop meets
`D`. -/
theorem _root_.QuantumCircuit.IsZeroOn.sitePermOp_sitePerm_mulVec {D : Finset S}
    {v : Config (Qudits S d) → ℂ} (hD : IsZeroOn D v) {hs : List (TeleportHop Γ)}
    (hdisj : Disjoint D (allSites hs)) : IsZeroOn D (sitePermOp (sitePerm hs) *ᵥ v) := by
  refine hD.sitePermOp_mulVec_of_mapsTo fun x hx hx' ↦ hx ?_
  have hfix := sitePerm_apply_of_notMem (Finset.disjoint_left.mp hdisj hx')
  rwa [(sitePerm hs).injective hfix] at hx'

/-- The operator of a list of hops before the correction, for the outcome `z`: the two layers
followed by the projection onto `z` at the measured sites. -/
noncomputable def chainPre (hs : List (TeleportHop Γ)) (z : Config (Qudits S d)) :
    Matrix (Config (Qudits S d)) (Config (Qudits S d)) ℂ :=
  place (measuredSites hs) (single (fun i ↦ z i) (fun i ↦ z i) 1) *
    (hs.map fun h ↦ h.gate₂ (d := d)).prod * (hs.map fun h ↦ h.gate₁ (d := d)).prod

omit [NeZero d] in
theorem prod_gate₂_mem_supportedOperators (hs : List (TeleportHop Γ)) :
    (hs.map fun h ↦ h.gate₂ (d := d)).prod ∈ supportedOperators (Qudits S d) (allSites hs) := by
  refine list_prod_mem fun A hA ↦ ?_
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hA
  refine supportedOperators_mono ?_ h.gate₂_mem_supportedOperators
  rw [h.cell_b₂]
  intro i hmem₀
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem₀
  rcases hmem₀ with rfl | rfl <;> exact mem_allSites.mpr ⟨h, hh, by simp [sites]⟩

omit [NeZero d] in
theorem pre_mem_supportedOperators (h : TeleportHop Γ) (z : Config (Qudits S d)) :
    h.pre z ∈ supportedOperators (Qudits S d) h.sites := by
  refine mul_mem (mul_mem ?_ ?_) ?_ <;>
    exact supportedOperators_mono (by intro i; simp [sites]; tauto)
      (place_mem_supportedOperators _)

omit [NeZero d] in
/-- One more hop factors off the operator of a valid list. -/
theorem chainPre_cons {h : TeleportHop Γ} {hs : List (TeleportHop Γ)} (hv : Valid (h :: hs))
    (z : Config (Qudits S d)) : chainPre (h :: hs) z = h.pre z * chainPre hs z := by
  have hdisj : Disjoint (Γ.cell h.b₁) (allSites hs) := by
    rw [h.cell_b₁, Finset.disjoint_left]
    intro i hmem₀
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem₀
    rcases hmem₀ with rfl | rfl
    · exact hv.2.1
    · exact hv.2.2.1
  have h1 : Commute (h.gate₁ (d := d)) (hs.map fun h ↦ h.gate₂ (d := d)).prod :=
    commute_of_mem_supportedOperators_of_disjoint h.gate₁_mem_supportedOperators
      (prod_gate₂_mem_supportedOperators hs) hdisj
  have h2 : Commute (place (measuredSites hs) (single (fun i ↦ z i) (fun i ↦ z i) 1))
      (h.pre z) :=
    commute_of_mem_supportedOperators_of_disjoint (place_mem_supportedOperators _)
      (pre_mem_supportedOperators h z) (disjoint_measuredSites hv)
  have hP : place (measuredSites (h :: hs)) (single (fun i ↦ z i) (fun i ↦ z i) (1 : ℂ)) =
      place {h.c, h.e} (single (fun i ↦ z i) (fun i ↦ z i) 1) *
        place (measuredSites hs) (single (fun i ↦ z i) (fun i ↦ z i) 1) :=
    place_single_union _ _ z
  rw [chainPre, hP, (commute_place_single _ _ z).eq]
  simp only [List.map_cons, List.prod_cons]
  calc place (measuredSites hs) (single (fun i ↦ z i) (fun i ↦ z i) 1) *
        place {h.c, h.e} (single (fun i ↦ z i) (fun i ↦ z i) 1) *
        (h.gate₂ * (hs.map fun h ↦ h.gate₂ (d := d)).prod) *
        (h.gate₁ * (hs.map fun h ↦ h.gate₁ (d := d)).prod)
      = place (measuredSites hs) (single (fun i ↦ z i) (fun i ↦ z i) 1) * h.pre z *
          (hs.map fun h ↦ h.gate₂ (d := d)).prod * (hs.map fun h ↦ h.gate₁ (d := d)).prod := by
        simp only [pre, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (hs.map fun h ↦ h.gate₂ (d := d)).prod, ← h1.eq, Matrix.mul_assoc]
    _ = h.pre z * chainPre hs z := by
        rw [h2.eq]; simp only [chainPre, Matrix.mul_assoc]

/-- **Chains of hops before the correction.** For a valid list of `H` hops and a vector with
`|0⟩` at the sites `e` and `f` of every hop, the operator of the hops for the outcome `z` is
`d^{-H}` times the permutation of sites of the list followed by the one-site unitaries that
the hops leave for the outcome `z`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("performing
simultaneous measurements"). -/
theorem chainPre_mulVec : ∀ {hs : List (TeleportHop Γ)}, Valid hs → ∀ (z : Config (Qudits S d))
    {v : Config (Qudits S d) → ℂ}, IsZeroOn (pairSites hs) v →
    chainPre hs z *ᵥ v = ((d : ℂ) ^ hs.length)⁻¹ •
      (piKronecker (chainFrame hs z) *ᵥ (sitePermOp (sitePerm hs) *ᵥ v))
  | [], _, z, v, _ => by
    have hP : place (measuredSites ([] : List (TeleportHop Γ)))
        (single (fun i ↦ z i) (fun i ↦ z i) (1 : ℂ)) = 1 :=
      ext_iff_mulVec.mpr fun w ↦ funext fun σ ↦ by
        rw [place_single_self_mulVec_apply, one_mulVec]
        simp [measuredSites]
    rw [chainPre, hP]
    simp [chainFrame, sitePerm, sitePermOp_one]
  | h :: hs, hv, z, v, hz => by
    have hzhs : IsZeroOn (pairSites hs) v := hz.mono Finset.subset_union_right
    have hef : Disjoint ({h.e, h.f} : Finset S) (allSites hs) :=
      Finset.disjoint_left.mpr fun i hi ↦ by
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hv.2.1
        · rw [Finset.mem_singleton.mp hi]; exact hv.2.2.1
    have hc : h.c ∉ ({h.e, h.f} : Finset S) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h.c_ne_e, h.c_ne_f⟩
    set g := chainFrame hs z
    set U := g h.c
    set w := sitePermOp (sitePerm hs) *ᵥ v
    have hge : g h.e = 1 := chainFrame_of_notMem hs z hv.2.1
    have hgf : g h.f = 1 := chainFrame_of_notMem hs z hv.2.2.1
    -- Split off the unitary at `c`.
    have hsplit : piKronecker g = piKronecker (Function.update g h.c 1) *
        piKronecker (Function.update (fun _ ↦ (1 : Matrix (Fin d) (Fin d) ℂ)) h.c U) := by
      rw [piKronecker_mul]
      congr 1
      funext i
      by_cases hi : i = h.c
      · subst hi; simp [U]
      · simp [Function.update_of_ne hi]
    have hcomm : Commute (h.pre z) (piKronecker (Function.update g h.c 1)) := by
      refine commute_of_mem_supportedOperators_of_disjoint (pre_mem_supportedOperators h z)
        (piKronecker_mem_supportedOperators fun i hi ↦ ?_) disjoint_compl_right
      simp only [Finset.mem_compl, not_not, sites, Finset.mem_insert,
        Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact Function.update_self ..
      · rw [Function.update_of_ne h.c_ne_e.symm, hge]
      · rw [Function.update_of_ne h.c_ne_f.symm, hgf]
    have hw : IsZeroOn {h.e, h.f} w :=
      (hz.mono Finset.subset_union_left).sitePermOp_sitePerm_mulVec hef
    have hw' : IsZeroOn {h.e, h.f}
        (piKronecker (Function.update (fun _ ↦ (1 : Matrix (Fin d) (Fin d) ℂ)) h.c U) *ᵥ w) :=
      hw.piKronecker_update_one_mulVec hc U
    have hswap : sitePermOp (Equiv.swap h.c h.f) *
        piKronecker (Function.update (fun _ ↦ (1 : Matrix (Fin d) (Fin d) ℂ)) h.c U) =
        piKronecker (Function.update (fun _ ↦ (1 : Matrix (Fin d) (Fin d) ℂ)) h.f U) *
          sitePermOp (Equiv.swap h.c h.f) := by
      rw [sitePermOp_mul_piKronecker]
      congr 2
      funext i
      rw [Equiv.symm_swap]
      by_cases hi : i = h.f
      · subst hi; simp
      · by_cases hi' : i = h.c
        · subst hi'
          rw [Equiv.swap_apply_left, Function.update_of_ne h.c_ne_f.symm,
            Function.update_of_ne hi]
        · rw [Equiv.swap_apply_of_ne_of_ne hi' hi, Function.update_of_ne hi',
            Function.update_of_ne hi]
    have hframe : piKronecker (Function.update g h.c 1) * (piKronecker (h.frame z) *
        piKronecker (Function.update (fun _ ↦ (1 : Matrix (Fin d) (Fin d) ℂ)) h.f U)) =
          piKronecker (chainFrame (h :: hs) z) := by
      rw [piKronecker_mul, piKronecker_mul]
      congr 1
      funext i
      simp only [chainFrame, Matrix.mul_assoc]
      rfl
    rw [chainPre_cons hv, ← mulVec_mulVec, chainPre_mulVec hv.1 z hzhs, mulVec_smul, hsplit,
      ← mulVec_mulVec, mulVec_mulVec (M := h.pre z), hcomm.eq, ← mulVec_mulVec,
      h.pre_mulVec z hw', mulVec_smul, mulVec_mulVec (M := sitePermOp (Equiv.swap h.c h.f)),
      hswap, ← mulVec_mulVec, mulVec_mulVec (M := piKronecker (h.frame z)),
      mulVec_mulVec (M := piKronecker _), hframe, smul_smul, sitePerm, ← sitePermOp_mul,
      ← mulVec_mulVec, List.length_cons, pow_succ, mul_inv]

/-! ### The teleportation round -/

/-- The unitary part of the teleportation round: the circuit `u`, the first layer and the second
layer of the hops. -/
noncomputable def roundUnitary (u : UnitaryCircuit Γ (Qudits S d)) (hs : List (TeleportHop Γ))
    (hv : Valid hs) : UnitaryCircuit Γ (Qudits S d) :=
  (u.comp (UnitaryCircuit.ofLayer (layerOne hs hv) (forall_isUnitary_layerOne hs hv))).comp
    (UnitaryCircuit.ofLayer (layerTwo hs hv) (forall_isUnitary_layerTwo hs hv))

/-- The outcome of the measured sites of a list of hops, extended by `0` to a configuration. -/
def extendOutcome (hs : List (TeleportHop Γ))
    (m : RegionConfig (Qudits S d) (measuredSites hs)) : Config (Qudits S d) :=
  fun i ↦ if hi : i ∈ measuredSites hs then m ⟨i, hi⟩ else 0

/-- The *teleportation round* of a valid list of hops after the unitary circuit `u`: the circuit
`u`, the first layer and the second layer of the hops, the measurement of the sites `c` and `e`
of every hop, and the correction by the inverse of the one-site unitaries left by the hops.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("creating
nearest-neighbor entangled pairs, then performing simultaneous measurements, and correcting
(without postselection) based on the measurement outcomes"). -/
noncomputable def round (u : UnitaryCircuit Γ (Qudits S d)) (hs : List (TeleportHop Γ))
    (hv : Valid hs) : Circuit Γ KrausGate (Qudits S d) (Qudits S d) :=
  (roundUnitary u hs hv).toCircuit.comp (Circuit.measureCorrect (measuredSites hs)
    fun m i ↦ star (chainFrame hs (extendOutcome hs m) i))

theorem op_roundUnitary (u : UnitaryCircuit Γ (Qudits S d)) (hs : List (TeleportHop Γ))
    (hv : Valid hs) : (roundUnitary u hs hv).op =
      (hs.map fun h ↦ h.gate₂ (d := d)).prod * (hs.map fun h ↦ h.gate₁ (d := d)).prod * u.op := by
  have i₁ := (Layer.nonempty_unique_index_of_forall_isUnitary
    (forall_isUnitary_layerOne (d := d) hs hv)).some.default
  have i₂ := (Layer.nonempty_unique_index_of_forall_isUnitary
    (forall_isUnitary_layerTwo (d := d) hs hv)).some.default
  rw [roundUnitary, UnitaryCircuit.op_comp, UnitaryCircuit.op_comp,
    UnitaryCircuit.op_ofLayer _ _ i₁, UnitaryCircuit.op_ofLayer _ _ i₂, kraus_layerOne,
    kraus_layerTwo, Matrix.mul_assoc]

/-- The teleportation round after the circuit `u` exceeds the depth of `u` by at most `2`,
whatever the number and the lengths of the chains. -/
theorem depth_round_le (u : UnitaryCircuit Γ (Qudits S d)) (hs : List (TeleportHop Γ))
    (hv : Valid hs) : (round u hs hv).depth ≤ u.depth + 2 := by
  refine (Circuit.depth_comp _ _).trans ?_
  rw [Circuit.depth_measureCorrect, add_zero]
  change (roundUnitary u hs hv).depth ≤ _
  rw [roundUnitary, UnitaryCircuit.depth_comp, UnitaryCircuit.depth_comp,
    UnitaryCircuit.depth_ofLayer, UnitaryCircuit.depth_ofLayer, add_assoc]
  exact Nat.add_le_add_left (Nat.add_le_add (Layer.depth_le_one _) (Layer.depth_le_one _)) _

/-- After the empty circuit, the teleportation round has depth at most `2`. -/
theorem depth_round_id_le (hs : List (TeleportHop Γ)) (hv : Valid hs) :
    (round (UnitaryCircuit.id Γ (Qudits S d)) hs hv).depth ≤ 2 := by
  simpa using depth_round_le (UnitaryCircuit.id Γ (Qudits S d)) hs hv

/-- The teleportation round is a measurement circuit. -/
theorem forall_round (u : UnitaryCircuit Γ (Qudits S d)) (hs : List (TeleportHop Γ))
    (hv : Valid hs) :
    (round u hs hv).Forall KrausGate.ev KrausFamily.IsUnitaryOrMeasurement :=
  ((roundUnitary u hs hv).forall_isUnitary.mono fun _ hK ↦ Or.inl hK).comp _
    (Circuit.forall_measureCorrect _ fun _ _ ↦
      Unitary.star_mem (chainFrame_mem_unitaryGroup _ _ _))

/-- **Teleportation in one round.** For a valid list of `H` hops, the teleportation round after
the unitary circuit `u` implements `P U` on the vectors `v` such that `U v` has `|0⟩` at the
sites `e` and `f` of every hop, `U` the operator of `u` and `P` the permutation of sites of the
hops; on every branch the scalar is `d^{-H}`. With `u` empty, a register is moved along every
chain of hops, of any length, in depth at most `2`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("Isometries ... act on
a constant number of sites which, although spatially separated, can be teleported at
neighboring registers with a constant overhead"). -/
theorem isImplementationOn_round (u : UnitaryCircuit Γ (Qudits S d))
    {hs : List (TeleportHop Γ)} (hv : Valid hs) :
    (round u hs hv).IsImplementationOn KrausGate.ev {v | IsZeroOn (pairSites hs) (u.op *ᵥ v)}
      (sitePermOp (sitePerm hs) * u.op) := by
  refine Circuit.isImplementationOn_comp_measureCorrect KrausGate.ev
    (fun p ↦ ⟨_, UnitaryCircuit.kraus_eq_smul_op _ p⟩) fun m ↦
      ⟨((d : ℂ) ^ hs.length)⁻¹, fun v hv' ↦ ?_⟩
  set z := extendOutcome hs m
  have hm : m = fun i : {i // i ∈ measuredSites hs} ↦ z i :=
    funext fun i ↦ by simp [z, extendOutcome, i.2]
  have hstar :
      piKronecker (fun i ↦ star (chainFrame hs z i)) * piKronecker (chainFrame hs z) = 1 := by
    rw [piKronecker_mul]
    simp only [Unitary.star_mul_self_of_mem (chainFrame_mem_unitaryGroup hs z _), piKronecker_one]
  have hP : place (measuredSites hs) (single m m (1 : ℂ)) =
      place (measuredSites hs) (single (fun i ↦ z i) (fun i ↦ z i) 1) := by
    rw [← hm]
  rw [hP, op_roundUnitary]
  have hK : piKronecker (fun i ↦ star (chainFrame hs z i)) *
      place (measuredSites hs) (single (fun i ↦ z i) (fun i ↦ z i) 1) *
      ((hs.map fun h ↦ h.gate₂ (d := d)).prod * (hs.map fun h ↦ h.gate₁ (d := d)).prod * u.op) =
      piKronecker (fun i ↦ star (chainFrame hs z i)) * chainPre hs z * u.op := by
    simp only [chainPre, Matrix.mul_assoc]
  rw [hK, ← mulVec_mulVec, ← mulVec_mulVec, chainPre_mulVec hv z hv', mulVec_smul,
    mulVec_mulVec, hstar, one_mulVec, mulVec_mulVec]

end TeleportHop

end QuantumCircuit
