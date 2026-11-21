/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Compile.Dilation
import QICLean.Circuit.Compile.PermGate
import QICLean.Circuit.Geometry.Port
import QICLean.Circuit.Geometry.Ring
import QICLean.ManyBody.Sites.Relabel

/-!
# Compiling ring protocols to physical ports

A protocol on the ring of `N` sites whose bases have at most `d ^ k` elements is simulated on the
ring with physical ports (`Geometry.portRing`), with `2k + 1` qudits of dimension `d` at every
site: the port, `k` data qudits holding the register of the site, and `k` scratch qudits. A gate
on the registers of the sites `j` and `j + 1` is executed by moving the register of `j`, one
digit per port layer, into the scratch qudits of `j + 1`, acting inside the site `j + 1`, and
moving the register back. Every layer of the ring protocol costs `2k` port layers.

## Main definitions

* `QuantumCircuit.portDataEmbedding` — the register of a site in its data wires.

## Main results

* `QuantumCircuit.Layer.exists_portRing_sites` — a layer of operations on whole sites is dilated
  by a unitary circuit of depth `0` on the ring with ports.
* `QuantumCircuit.Layer.exists_portRing` — a layer of the ring of registers is dilated by a
  unitary circuit on the ring with ports, of depth at most `2k` times its depth, with
  environments at the wires of any set meeting every site.

## Implementation notes

The ports move registers by permutations of the wires: every routing layer has the one Kraus
operator `sitePermOp π` of a permutation `π`, so the forward routing is the permutation `τ` of
the wires taking the data wire `t` of the left end `j` of a cell to the scratch wire `t` of
`j + 1` (`routeTotal_dataWire`). After the routing every gate of the layer acts inside one site:
the layer is coarsened along the map `host` sending `j` to `j + 1` (`Layer.exists_coarsen`),
encoded along the registers moved by `τ` (`Layer.exists_encoded`), and its families on the single
sites are read as gates on all the wires of a site (`refine`). The code moved by `τ` is the data
code conjugated by `sitePermOp τ` (`routed_code`), so the backward routing returns it. The
routing layers are unitary and the refined layer has gates on whole sites only, so each part is
dilated with environments at the wires of a set meeting every site (`Circuit.isUnitaryDilation`).
The permutation gates are those of `Compile/PermGate`.
-/

open Matrix ManyBody

namespace QuantumCircuit

/-! ### The routing circuit -/

section Routing

variable {N k : ℕ}

/-- The data wire `t` of a site: wire `1 + t`. -/
private def dataWire (t : Fin k) : Fin (2 * k + 1) := ⟨1 + t, by omega⟩

/-- The scratch wire `t` of a site: wire `1 + k + t`. -/
private def scratchWire (t : Fin k) : Fin (2 * k + 1) := ⟨1 + k + t, by omega⟩

private theorem dataWire_ne_zero (t : Fin k) : dataWire t ≠ 0 := by simp [dataWire, Fin.ext_iff]

private theorem scratchWire_ne_zero (t : Fin k) : scratchWire t ≠ 0 := by
  simp [scratchWire, Fin.ext_iff]

private theorem dataWire_ne_scratchWire (t s : Fin k) : dataWire t ≠ scratchWire s := by
  simp [dataWire, scratchWire, Fin.ext_iff]
  omega

private theorem dataWire_inj {t s : Fin k} : dataWire t = dataWire s ↔ t = s := by
  simp [dataWire, Fin.ext_iff]

private theorem scratchWire_inj {t s : Fin k} : scratchWire t = scratchWire s ↔ t = s := by
  simp [scratchWire, Fin.ext_iff]

/-- The data wire carried by a wire of a site, if any. -/
private def dataIndex (u : Fin (2 * k + 1)) : Option (Fin k) :=
  if h : 1 ≤ u.1 ∧ u.1 < 1 + k then some ⟨u.1 - 1, by omega⟩ else none

private theorem dataIndex_dataWire (t : Fin k) : dataIndex (dataWire t) = some t := by
  simp [dataIndex, dataWire]

private theorem eq_dataWire_of_dataIndex {u : Fin (2 * k + 1)} {t : Fin k}
    (h : dataIndex u = some t) : u = dataWire t := by
  unfold dataIndex at h
  split_ifs at h with hu
  obtain rfl := Option.some.inj h
  ext
  simp only [dataWire]
  omega

/-- The permutation `σ` of the wires of every site of `D`. -/
private def sitewisePerm (D : Finset (Fin N)) (σ : Equiv.Perm (Fin (2 * k + 1))) :
    Equiv.Perm (Fin N × Fin (2 * k + 1)) :=
  Equiv.prodShear (Equiv.refl _) fun i ↦ if i ∈ D then σ else Equiv.refl _

private theorem sitewisePerm_apply (D : Finset (Fin N)) (σ : Equiv.Perm (Fin (2 * k + 1)))
    (w : Fin N × Fin (2 * k + 1)) :
    sitewisePerm D σ w = (w.1, if w.1 ∈ D then σ w.2 else w.2) := by
  change (w.1, (if w.1 ∈ D then σ else Equiv.refl _) w.2) = _
  split_ifs <;> rfl

/-- The exchange of the ports of the sites `j` and `j + 1` for every `j ∈ C`. -/
private def portShift (C : Finset (Fin N)) (w : Fin N × Fin (2 * k + 1)) :
    Fin N × Fin (2 * k + 1) :=
  if w.2 = 0 ∧ w.1 ∈ C then (finRotate N w.1, 0)
  else if w.2 = 0 ∧ (finRotate N).symm w.1 ∈ C then ((finRotate N).symm w.1, 0) else w

private theorem portShift_of_mem {C : Finset (Fin N)} {j : Fin N} (hj : j ∈ C) :
    portShift (k := k) C (j, 0) = (finRotate N j, 0) := by
  simp [portShift, hj, -finRotate_apply]

private theorem portShift_of_symm_mem {C : Finset (Fin N)} {j : Fin N} (hj : j ∉ C)
    (hj' : (finRotate N).symm j ∈ C) :
    portShift (k := k) C (j, 0) = ((finRotate N).symm j, 0) := by
  rw [portShift, ite_eq_right (fun h ↦ absurd h.2 hj), ite_eq_left ⟨rfl, hj'⟩]

private theorem portShift_of_notMem {C : Finset (Fin N)} {j : Fin N} (hj : j ∉ C)
    (hj' : (finRotate N).symm j ∉ C) : portShift (k := k) C (j, 0) = (j, 0) := by
  rw [portShift, ite_eq_right (fun h ↦ absurd h.2 hj), ite_eq_right (fun h ↦ absurd h.2 hj')]

private theorem portShift_of_ne {C : Finset (Fin N)} {w : Fin N × Fin (2 * k + 1)}
    (hw : w.2 ≠ 0) : portShift C w = w := by
  simp [portShift, hw]

private theorem portShift_involutive (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C) :
    Function.Involutive (portShift (k := k) C) := by
  rintro ⟨i, u⟩
  by_cases hu : u = 0
  · subst hu
    by_cases hi : i ∈ C
    · rw [portShift_of_mem hi, portShift_of_symm_mem (hC i hi)
        (by rw [Equiv.symm_apply_apply]; exact hi), Equiv.symm_apply_apply]
    · by_cases hi' : (finRotate N).symm i ∈ C
      · rw [portShift_of_symm_mem hi hi', portShift_of_mem hi', Equiv.apply_symm_apply]
      · rw [portShift_of_notMem hi hi', portShift_of_notMem hi hi']
  · rw [portShift_of_ne (w := (i, u)) hu, portShift_of_ne (w := (i, u)) hu]

/-- The exchange of the ports along the cells `C`, as a permutation. -/
private def portPerm (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C) :
    Equiv.Perm (Fin N × Fin (2 * k + 1)) :=
  (portShift_involutive C hC).toPerm _

private theorem portPerm_apply (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C)
    (w : Fin N × Fin (2 * k + 1)) : portPerm C hC w = portShift C w := rfl

/-- Neighbouring cells of a layer on a ring of at least two sites are not both used: the
two cells share a site and are distinct. -/
private theorem finRotate_notMem (hN : 2 ≤ N) {C : Finset (Fin N)}
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell) :
    ∀ j ∈ C, finRotate N j ∉ C := by
  intro j hj hj'
  have hne : j ≠ finRotate N j := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    rw [finRotate_apply]
    intro h
    simpa using congrArg (· - j) h
  exact Finset.disjoint_left.mp (hring hj hj' hne)
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (Finset.mem_insert_self _ _)

variable (d : ℕ)

/-- The cell of all the wires of a site. -/
private def inlCell : Fin N ↪ (Geometry.portRing N (2 * k + 1)).Cell :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- The cell of the ports of a site and the next. -/
private def inrCell : Fin N ↪ (Geometry.portRing N (2 * k + 1)).Cell :=
  ⟨Sum.inr, Sum.inr_injective⟩

private theorem cell_inlCell (i : Fin N) :
    (Geometry.portRing N (2 * k + 1)).cell (inlCell i) = {i} ×ˢ Finset.univ := rfl

private theorem cell_inrCell (i : Fin N) :
    (Geometry.portRing N (2 * k + 1)).cell (inrCell i) = {(i, 0), (finRotate N i, 0)} := rfl

private theorem cost_inlCell (i : Fin N) : (Geometry.portRing N (2 * k + 1)).cost (inlCell i) = 0 :=
  rfl

private theorem cost_inrCell (i : Fin N) :
    (Geometry.portRing N (2 * k + 1)).cost (inrCell i) = 1 :=
  rfl

private theorem mem_cell_inlCell {i : Fin N} {w : Fin N × Fin (2 * k + 1)} :
    w ∈ (Geometry.portRing N (2 * k + 1)).cell (inlCell i) ↔ w.1 = i := by
  rw [cell_inlCell, Finset.mem_product]
  simp

private theorem pairwiseDisjoint_inl (D : Finset (Fin N)) :
    Set.PairwiseDisjoint (D.map (inlCell (k := k)) : Set (Geometry.portRing N (2 * k + 1)).Cell)
      (Geometry.portRing N (2 * k + 1)).cell := by
  intro b hb b' hb' hne
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hb hb'
  obtain ⟨i, -, rfl⟩ := hb
  obtain ⟨i', -, rfl⟩ := hb'
  refine Finset.disjoint_left.mpr fun w hw hw' ↦ hne ?_
  rw [mem_cell_inlCell] at hw hw'
  rw [← hw, ← hw']

private theorem sitewisePerm_mem (D : Finset (Fin N)) (σ : Equiv.Perm (Fin (2 * k + 1))) :
    ∀ b ∈ D.map (inlCell (k := k)),
      ∀ v ∈ (Geometry.portRing N (2 * k + 1)).cell b,
        sitewisePerm D σ v ∈ (Geometry.portRing N (2 * k + 1)).cell b := by
  intro b hb v hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hb
  rw [mem_cell_inlCell] at hv ⊢
  rw [sitewisePerm_apply]
  exact hv

private theorem sitewisePerm_fix (D : Finset (Fin N)) (σ : Equiv.Perm (Fin (2 * k + 1))) :
    ∀ v, v ∉ (D.map (inlCell (k := k))).biUnion
      (Geometry.portRing N (2 * k + 1)).cell → sitewisePerm D σ v = v := by
  intro v hv
  have h : v.1 ∉ D := fun h ↦ hv (Finset.mem_biUnion.mpr
    ⟨inlCell v.1, Finset.mem_map_of_mem _ h, mem_cell_inlCell.mpr rfl⟩)
  rw [sitewisePerm_apply, ite_eq_right_iff.mpr fun h' ↦ absurd h' h]

/-- The layer permuting the wires of every site of `D` by `σ`, of depth `0`. -/
private def siteLayer (D : Finset (Fin N)) (σ : Equiv.Perm (Fin (2 * k + 1))) :
    Layer (Geometry.portRing N (2 * k + 1)) KrausGate (Qudits (Fin N × Fin (2 * k + 1)) d)
      (Qudits (Fin N × Fin (2 * k + 1)) d) :=
  Layer.ofCells _ (pairwiseDisjoint_inl D) fun b ↦
    permGate (sitewisePerm D σ) _ (sitewisePerm_mem D σ b b.2)

private theorem kraus_siteLayer (D : Finset (Fin N)) (σ : Equiv.Perm (Fin (2 * k + 1)))
    (i : (siteLayer d D σ).Index) :
    (siteLayer d D σ).kraus KrausGate.ev i = sitePermOp (sitewisePerm D σ) :=
  kraus_ofCells_permGate _ (pairwiseDisjoint_inl D) _ (sitewisePerm_mem D σ)
    (sitewisePerm_fix D σ) i

private theorem depth_siteLayer (D : Finset (Fin N)) (σ : Equiv.Perm (Fin (2 * k + 1))) :
    (siteLayer d D σ).depth = 0 := by
  simp [Layer.depth, siteLayer, Layer.ofCells, Finset.filter_map, cost_inlCell]

private theorem mem_cell_inrCell {j : Fin N} {w : Fin N × Fin (2 * k + 1)} :
    w ∈ (Geometry.portRing N (2 * k + 1)).cell (inrCell j) ↔
      w = (j, 0) ∨ w = (finRotate N j, 0) := by
  rw [cell_inrCell, Finset.mem_insert, Finset.mem_singleton]

private theorem pairwiseDisjoint_inr {C : Finset (Fin N)}
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell) :
    Set.PairwiseDisjoint (C.map (inrCell (k := k)) : Set (Geometry.portRing N (2 * k + 1)).Cell)
      (Geometry.portRing N (2 * k + 1)).cell := by
  intro b hb b' hb' hne
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hb hb'
  obtain ⟨j, hj, rfl⟩ := hb
  obtain ⟨j', hj', rfl⟩ := hb'
  have hjj : j ≠ j' := fun h ↦ hne (h ▸ rfl)
  have key : ∀ {w : Fin N × Fin (2 * k + 1)} {j : Fin N},
      w ∈ (Geometry.portRing N (2 * k + 1)).cell (inrCell j) → w.1 ∈ (Geometry.ring N).cell j := by
    intro w j hw
    rcases mem_cell_inrCell.mp hw with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact Finset.disjoint_left.mpr fun w hw hw' ↦
    Finset.disjoint_left.mp (hring hj hj' hjj) (key hw) (key hw')

private theorem portPerm_mem (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C) :
    ∀ b ∈ C.map (inrCell (k := k)), ∀ v ∈ (Geometry.portRing N (2 * k + 1)).cell b,
      portPerm C hC v ∈ (Geometry.portRing N (2 * k + 1)).cell b := by
  intro b hb v hv
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
  rw [mem_cell_inrCell] at hv ⊢
  rcases hv with rfl | rfl
  · exact Or.inr (portShift_of_mem hj)
  · refine Or.inl ?_
    rw [portPerm_apply, portShift_of_symm_mem (hC j hj) (by rw [Equiv.symm_apply_apply]; exact hj),
      Equiv.symm_apply_apply]

private theorem portPerm_fix (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C) :
    ∀ v, v ∉ (C.map (inrCell (k := k))).biUnion (Geometry.portRing N (2 * k + 1)).cell →
      portPerm C hC v = v := by
  rintro ⟨i, u⟩ hv
  have hmem : ∀ j ∈ C, (i, u) ∉ (Geometry.portRing N (2 * k + 1)).cell (inrCell j) :=
    fun j hj h ↦ hv (Finset.mem_biUnion.mpr ⟨inrCell j, Finset.mem_map_of_mem _ hj, h⟩)
  rw [portPerm_apply]
  by_cases hu : u = 0
  · subst hu
    have hi : i ∉ C := fun hi ↦ hmem i hi (mem_cell_inrCell.mpr (Or.inl rfl))
    have hi' : (finRotate N).symm i ∉ C := fun hi' ↦ hmem _ hi'
      (mem_cell_inrCell.mpr (Or.inr (by rw [Equiv.apply_symm_apply])))
    exact portShift_of_notMem hi hi'
  · exact portShift_of_ne (w := (i, u)) hu

/-- The layer exchanging the ports along the cells `C`, of cost `1`. -/
private def portLayer (C : Finset (Fin N))
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell)
    (hC : ∀ j ∈ C, finRotate N j ∉ C) :
    Layer (Geometry.portRing N (2 * k + 1)) KrausGate (Qudits (Fin N × Fin (2 * k + 1)) d)
      (Qudits (Fin N × Fin (2 * k + 1)) d) :=
  Layer.ofCells _ (pairwiseDisjoint_inr hring) fun b ↦
    permGate (portPerm (k := k) C hC) _ (portPerm_mem (k := k) C hC b b.2)

private theorem kraus_portLayer (C : Finset (Fin N))
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell)
    (hC : ∀ j ∈ C, finRotate N j ∉ C) (i : (portLayer (k := k) d C hring hC).Index) :
    (portLayer (k := k) d C hring hC).kraus KrausGate.ev i = sitePermOp (portPerm (k := k) C hC) :=
  kraus_ofCells_permGate _ (pairwiseDisjoint_inr hring) _ (portPerm_mem (k := k) C hC)
    (portPerm_fix (k := k) C hC) i

private theorem depth_portLayer (C : Finset (Fin N))
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell)
    (hC : ∀ j ∈ C, finRotate N j ∉ C) :
    (portLayer (k := k) d C hring hC).depth = if C.Nonempty then 1 else 0 := by
  rw [Layer.depth, Finset.filter_true_of_mem fun b hb ↦ ?_]
  · exact if_congr Finset.map_nonempty rfl rfl
  · obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hb
    rw [cost_inrCell]
    exact Nat.one_pos

/-- The depth of a layer on the ring is `1` if it uses a cell and `0` otherwise. -/
private theorem depth_ring {G : Finset (Fin N) → (Fin N → Type) → (Fin N → Type) → Type 1}
    [GateFamily G] {X Y : Fin N → Type} (L : Layer (Geometry.ring N) G X Y) :
    L.depth = if L.cells.Nonempty then 1 else 0 := by
  rw [Layer.depth, Finset.filter_true_of_mem fun b _ ↦ Geometry.ring_cost_pos b]

/-- One round of the routing for the cells `C`: the exchanges of the port with the data wire
`t` at the sites of `C`, of the ports along `C`, and of the port with the scratch wire `t` at
the sites after `C`. -/
private def roundPerm (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C) (t : Fin k) :
    Equiv.Perm (Fin N × Fin (2 * k + 1)) :=
  sitewisePerm (C.map (finRotate N).toEmbedding) (Equiv.swap 0 (scratchWire t)) *
    (portPerm C hC * sitewisePerm C (Equiv.swap 0 (dataWire t)))

private theorem sitewisePerm_apply_of_eq (D : Finset (Fin N))
    {σ : Equiv.Perm (Fin (2 * k + 1))} {w : Fin N × Fin (2 * k + 1)} (h : σ w.2 = w.2) :
    sitewisePerm D σ w = w := by
  rw [sitewisePerm_apply]
  split_ifs <;> simp [h]

private theorem roundPerm_dataWire_of_ne (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C)
    {s t : Fin k} (hst : s ≠ t) (i : Fin N) :
    roundPerm C hC s (i, dataWire t) = (i, dataWire t) := by
  have h₁ : sitewisePerm C (Equiv.swap 0 (dataWire s)) (i, dataWire t) = (i, dataWire t) :=
    sitewisePerm_apply_of_eq _ (Equiv.swap_apply_of_ne_of_ne (dataWire_ne_zero t)
      (mt dataWire_inj.mp hst.symm))
  have h₂ : portPerm C hC (i, dataWire t) = (i, dataWire t) :=
    portShift_of_ne (w := (i, dataWire t)) (dataWire_ne_zero t)
  have h₃ : sitewisePerm (C.map (finRotate N).toEmbedding) (Equiv.swap 0 (scratchWire s))
      (i, dataWire t) = (i, dataWire t) :=
    sitewisePerm_apply_of_eq _ (Equiv.swap_apply_of_ne_of_ne (dataWire_ne_zero t)
      (dataWire_ne_scratchWire t s))
  rw [roundPerm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h₁, h₂, h₃]

private theorem roundPerm_scratchWire_of_ne (C : Finset (Fin N))
    (hC : ∀ j ∈ C, finRotate N j ∉ C) {s t : Fin k} (hst : s ≠ t) (i : Fin N) :
    roundPerm C hC s (i, scratchWire t) = (i, scratchWire t) := by
  have h₁ : sitewisePerm C (Equiv.swap 0 (dataWire s)) (i, scratchWire t) =
      (i, scratchWire t) :=
    sitewisePerm_apply_of_eq _ (Equiv.swap_apply_of_ne_of_ne (scratchWire_ne_zero t)
      (dataWire_ne_scratchWire s t).symm)
  have h₂ : portPerm C hC (i, scratchWire t) = (i, scratchWire t) :=
    portShift_of_ne (w := (i, scratchWire t)) (scratchWire_ne_zero t)
  have h₃ : sitewisePerm (C.map (finRotate N).toEmbedding) (Equiv.swap 0 (scratchWire s))
      (i, scratchWire t) = (i, scratchWire t) :=
    sitewisePerm_apply_of_eq _ (Equiv.swap_apply_of_ne_of_ne (scratchWire_ne_zero t)
      (mt scratchWire_inj.mp hst.symm))
  rw [roundPerm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h₁, h₂, h₃]

/-- The site receiving the register of the site `r`: the next site if `r` is the left end of a
cell of `C`, else `r`. -/
private def host (C : Finset (Fin N)) (r : Fin N) : Fin N :=
  if r ∈ C then finRotate N r else r

/-- The wire receiving the data wire `t` of the site `r`. -/
private def target (C : Finset (Fin N)) (r : Fin N) (t : Fin k) : Fin N × Fin (2 * k + 1) :=
  if r ∈ C then (finRotate N r, scratchWire t) else (r, dataWire t)

private theorem roundPerm_dataWire (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C)
    (r : Fin N) (t : Fin k) : roundPerm C hC t (r, dataWire t) = target C r t := by
  rw [roundPerm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, target]
  by_cases hr : r ∈ C
  · have h₁ : sitewisePerm C (Equiv.swap 0 (dataWire t)) (r, dataWire t) = (r, 0) := by
      rw [sitewisePerm_apply, ite_eq_left hr, Equiv.swap_apply_right]
    have h₃ : sitewisePerm (C.map (finRotate N).toEmbedding) (Equiv.swap 0 (scratchWire t))
        (finRotate N r, 0) = (finRotate N r, scratchWire t) := by
      rw [sitewisePerm_apply,
        ite_eq_left (Finset.mem_map_equiv.mpr (by rw [Equiv.symm_apply_apply]; exact hr)),
        Equiv.swap_apply_left]
    rw [ite_eq_left hr, h₁, portPerm_apply, portShift_of_mem hr, h₃]
  · have h₁ : sitewisePerm C (Equiv.swap 0 (dataWire t)) (r, dataWire t) = (r, dataWire t) := by
      rw [sitewisePerm_apply, ite_eq_right hr]
    have h₃ : sitewisePerm (C.map (finRotate N).toEmbedding) (Equiv.swap 0 (scratchWire t))
        (r, dataWire t) = (r, dataWire t) :=
      sitewisePerm_apply_of_eq _ (Equiv.swap_apply_of_ne_of_ne (dataWire_ne_zero t)
        (dataWire_ne_scratchWire t t))
    rw [ite_eq_right hr, h₁, portPerm_apply,
      portShift_of_ne (w := (r, dataWire t)) (dataWire_ne_zero t), h₃]

/-- The steps of the routing along a list of rounds: three layers per round. -/
private def routeIndex (m : List (Fin k)) : List (Fin k × Fin 3) :=
  m.flatMap fun t ↦ [(t, 0), (t, 1), (t, 2)]

/-- The permutation of a step of the routing. -/
private def routePerm (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C)
    (a : Fin k × Fin 3) : Equiv.Perm (Fin N × Fin (2 * k + 1)) :=
  ![sitewisePerm C (Equiv.swap 0 (dataWire a.1)), portPerm C hC,
    sitewisePerm (C.map (finRotate N).toEmbedding) (Equiv.swap 0 (scratchWire a.1))] a.2

/-- The permutation of the routing along a list of rounds. -/
private def routeTotal (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C)
    (m : List (Fin k)) : Equiv.Perm (Fin N × Fin (2 * k + 1)) :=
  ((routeIndex m).map (routePerm C hC)).reverse.prod

private theorem routeTotal_cons (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C)
    (a : Fin k) (m : List (Fin k)) :
    routeTotal C hC (a :: m) = routeTotal C hC m * roundPerm C hC a := by
  simp [routeTotal, routeIndex, roundPerm, routePerm]

private theorem routeTotal_fix (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C)
    (i : Fin N) {t : Fin k} : ∀ m : List (Fin k), t ∉ m →
      routeTotal C hC m (i, dataWire t) = (i, dataWire t) ∧
        routeTotal C hC m (i, scratchWire t) = (i, scratchWire t)
  | [], _ => ⟨rfl, rfl⟩
  | a :: m, ht => by
    have hat : a ≠ t := fun h ↦ ht (h ▸ List.mem_cons_self)
    have ih := routeTotal_fix C hC i m fun h ↦ ht (List.mem_cons_of_mem a h)
    rw [routeTotal_cons, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      roundPerm_dataWire_of_ne C hC hat, roundPerm_scratchWire_of_ne C hC hat]
    exact ih

private theorem routeTotal_dataWire (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C)
    (r : Fin N) {t : Fin k} : ∀ m : List (Fin k), m.Nodup → t ∈ m →
      routeTotal C hC m (r, dataWire t) = target C r t
  | a :: m, hm, ht => by
    rw [routeTotal_cons, Equiv.Perm.mul_apply]
    by_cases hat : a = t
    · subst hat
      have hfix := routeTotal_fix C hC (k := k) (t := a) (finRotate N r) m (List.nodup_cons.mp hm).1
      have hfix' := routeTotal_fix C hC (k := k) (t := a) r m (List.nodup_cons.mp hm).1
      rw [roundPerm_dataWire, target]
      split_ifs
      · exact hfix.2
      · exact hfix'.1
    · rw [roundPerm_dataWire_of_ne C hC hat]
      exact routeTotal_dataWire C hC r m (List.nodup_cons.mp hm).2
        ((List.mem_cons.mp ht).resolve_left (Ne.symm hat))

/-- The data wire `t` of the site `r` reaches the site `host C r`. -/
private theorem routeTotal_dataWire_fst (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C)
    (r : Fin N) (t : Fin k) :
    (routeTotal C hC (List.finRange k) (r, dataWire t)).1 = host C r := by
  rw [routeTotal_dataWire C hC r _ (List.nodup_finRange k) (List.mem_finRange t), target, host]
  split_ifs <;> rfl

/-- The layer of a step of the routing. -/
private def routeLayer (C : Finset (Fin N))
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell)
    (hC : ∀ j ∈ C, finRotate N j ∉ C) (a : Fin k × Fin 3) :
    Layer (Geometry.portRing N (2 * k + 1)) KrausGate (Qudits (Fin N × Fin (2 * k + 1)) d)
      (Qudits (Fin N × Fin (2 * k + 1)) d) :=
  ![siteLayer d C (Equiv.swap 0 (dataWire a.1)), portLayer d C hring hC,
    siteLayer d (C.map (finRotate N).toEmbedding) (Equiv.swap 0 (scratchWire a.1))] a.2

private theorem kraus_routeLayer (C : Finset (Fin N))
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell)
    (hC : ∀ j ∈ C, finRotate N j ∉ C) :
    ∀ (a : Fin k × Fin 3) (i : (routeLayer d C hring hC a).Index),
      (routeLayer d C hring hC a).kraus KrausGate.ev i = sitePermOp (routePerm C hC a) := by
  rintro ⟨t, j⟩ i
  fin_cases j
  · exact kraus_siteLayer d _ _ i
  · exact kraus_portLayer d C hring hC i
  · exact kraus_siteLayer d _ _ i

private theorem forall_isUnitary_routeLayer (C : Finset (Fin N))
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell)
    (hC : ∀ j ∈ C, finRotate N j ∉ C) (a : Fin k × Fin 3) :
    (routeLayer d C hring hC a).Forall KrausGate.ev KrausFamily.IsUnitary := by
  obtain ⟨t, j⟩ := a
  have hone : ∀ {α : Type} [Fintype α] [DecidableEq α],
      (KrausFamily.single (1 : Matrix α α ℂ)).IsUnitary :=
    KrausFamily.isUnitary_single (one_mem _)
  fin_cases j
  · exact Layer.forall_ofCells _ hone _ _ _ fun b ↦
      isUnitary_permGate (sitewisePerm C (Equiv.swap 0 (dataWire t))) _
        (sitewisePerm_mem C _ b b.2)
  · exact Layer.forall_ofCells _ hone _ _ _ fun b ↦
      isUnitary_permGate _ _ (portPerm_mem (k := k) C hC b b.2)
  · exact Layer.forall_ofCells _ hone _ _ _ fun b ↦
      isUnitary_permGate (sitewisePerm (C.map (finRotate N).toEmbedding)
        (Equiv.swap 0 (scratchWire t))) _ (sitewisePerm_mem _ _ b b.2)

private theorem depth_routeLayer (C : Finset (Fin N))
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell)
    (hC : ∀ j ∈ C, finRotate N j ∉ C) (m : List (Fin k)) :
    (((routeIndex m).map (routeLayer d C hring hC)).map Layer.depth).sum =
      m.length * if C.Nonempty then 1 else 0 := by
  induction m with
  | nil => simp [routeIndex]
  | cons a m ih =>
    simp only [routeIndex, List.flatMap_cons, List.map_append, List.sum_append] at ih ⊢
    rw [ih]
    simp only [routeLayer, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons]
    simp [depth_siteLayer, depth_portLayer]
    split_ifs <;> omega

private theorem routeKraus (C : Finset (Fin N)) (hC : ∀ j ∈ C, finRotate N j ∉ C)
    (l : List (Fin k × Fin 3)) :
    (l.map fun a ↦ sitePermOp (α := Fin d) (routePerm C hC a)).reverse.prod =
      sitePermOp (l.map (routePerm C hC)).reverse.prod := by
  rw [← list_prod_map_sitePermOp, ← List.map_reverse, ← List.map_reverse, List.map_map]
  rfl

private theorem forall₂_routeLayer (C : Finset (Fin N))
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell)
    (hC : ∀ j ∈ C, finRotate N j ∉ C) (l : List (Fin k × Fin 3)) :
    List.Forall₂ (fun L U ↦ ∀ i, L.kraus KrausGate.ev i = U) (l.map (routeLayer d C hring hC))
      (l.map fun a ↦ sitePermOp (routePerm C hC a)) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun a _ ↦ kraus_routeLayer d C hring hC a

/-- A circuit with a unique branch whose Kraus operator is `U` is conjugation by `U`. -/
private theorem map_eq_of_kraus {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
    {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    {c : Circuit Γ KrausGate X X} (hc : c.Forall KrausGate.ev KrausFamily.IsUnitary)
    {U : Matrix (Config X) (Config X) ℂ} (hU : ∀ p, c.kraus KrausGate.ev p = U)
    (ρ : Matrix (Config X) (Config X) ℂ) : c.map KrausGate.ev ρ = U * ρ * Uᴴ := by
  obtain ⟨u⟩ := Circuit.nonempty_unique_index KrausGate.ev (hc.mono fun _ h ↦ h.1)
  have : Unique (c.krausFamily KrausGate.ev).Index := u
  rw [Circuit.map, KrausFamily.map_apply, Fintype.sum_unique]
  exact congrArg (fun A ↦ A * ρ * Aᴴ) (hU _)

/-- A layer of unitary local families has a Kraus index. -/
private theorem nonempty_index_of_forall_isUnitary {S : Type} [DecidableEq S]
    {Γ : Geometry S} {X Y : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] {L : Layer Γ KrausGate X Y}
    (h : L.Forall KrausGate.ev KrausFamily.IsUnitary) : Nonempty L.Index :=
  ⟨(fun b ↦ (h.1 b).1.some.default, fun s ↦ (h.2 s).1.some.default)⟩

/-- The forward routing circuit. -/
private def forwardCircuit (C : Finset (Fin N))
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell)
    (hC : ∀ j ∈ C, finRotate N j ∉ C) :
    Circuit (Geometry.portRing N (2 * k + 1)) KrausGate (Qudits (Fin N × Fin (2 * k + 1)) d)
      (Qudits (Fin N × Fin (2 * k + 1)) d) :=
  Circuit.seq ((routeIndex (List.finRange k)).map (routeLayer d C hring hC))

/-- Every wire holds a qudit of dimension `d`. -/
private theorem card_qudits [NeZero d] (s : Fin N × Fin (2 * k + 1)) :
    0 < Nat.card (Qudits (Fin N × Fin (2 * k + 1)) d s) ∧
      Nat.card (Qudits (Fin N × Fin (2 * k + 1)) d s) ≤ d := by
  simp only [Qudits, Nat.card_eq_fintype_card, Fintype.card_fin, le_rfl, and_true]
  exact NeZero.pos d

private theorem isUnitaryDilation_forwardCircuit [NeZero d] (C : Finset (Fin N))
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell)
    (hC : ∀ j ∈ C, finRotate N j ∉ C) (D : Finset (Fin N × Fin (2 * k + 1))) :
    IsUnitaryDilation (Geometry.portRing N (2 * k + 1)) D d (k * if C.Nonempty then 1 else 0)
      ((forwardCircuit (k := k) d C hring hC).map KrausGate.ev) ∧
    ∀ ρ, (forwardCircuit (k := k) d C hring hC).map KrausGate.ev ρ =
      sitePermOp (routeTotal C hC (List.finRange k)) * ρ *
        (sitePermOp (routeTotal C hC (List.finRange k)))ᴴ := by
  have hU : (forwardCircuit (k := k) d C hring hC).Forall KrausGate.ev KrausFamily.IsUnitary :=
    Circuit.forall_seq _ _ fun L hL ↦ by
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hL
      exact forall_isUnitary_routeLayer d C hring hC a
  have hne : ∀ L ∈ (routeIndex (List.finRange k)).map (routeLayer d C hring hC),
      Nonempty L.Index := fun L hL ↦ by
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hL
    exact nonempty_index_of_forall_isUnitary (forall_isUnitary_routeLayer d C hring hC a)
  refine ⟨(Circuit.isUnitaryDilation D _ (hU.mono fun _ h ↦ h.isTP) (Circuit.isUnbranched_seq _)
    (Circuit.isUnitaryOff_of_forall_isUnitary D hU)
    (Circuit.isDimBounded_seq (fun s _ ↦ card_qudits d s) _)).mono le_rfl ?_,
    map_eq_of_kraus hU fun p ↦ ?_⟩
  · unfold forwardCircuit
    rw [Circuit.depth, Circuit.total_seq _ _ hne, depth_routeLayer,
      List.length_finRange]
  · exact (Circuit.kraus_seq_map _ _ _ _ (fun a _ ↦ kraus_routeLayer d C hring hC a) p).trans
      (routeKraus d C hC _)

private theorem forall_isUnitary_adjoint {S : Type} [DecidableEq S]
    {Γ : Geometry S} {X Y : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] {L : Layer Γ KrausGate X Y}
    (h : L.Forall KrausGate.ev KrausFamily.IsUnitary) :
    L.adjoint.Forall KrausGate.ev KrausFamily.IsUnitary :=
  ⟨fun b ↦ (h.1 b).adjoint, fun s ↦ (h.2 s).adjoint⟩

/-- The backward routing circuit: the adjoint layers of the forward one, in reverse order. -/
private def backwardCircuit (C : Finset (Fin N))
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell)
    (hC : ∀ j ∈ C, finRotate N j ∉ C) :
    Circuit (Geometry.portRing N (2 * k + 1)) KrausGate (Qudits (Fin N × Fin (2 * k + 1)) d)
      (Qudits (Fin N × Fin (2 * k + 1)) d) :=
  Circuit.seqAdjoint ((routeIndex (List.finRange k)).map (routeLayer d C hring hC))

private theorem isUnitaryDilation_backwardCircuit [NeZero d] (C : Finset (Fin N))
    (hring : (C : Set (Fin N)).PairwiseDisjoint (Geometry.ring N).cell)
    (hC : ∀ j ∈ C, finRotate N j ∉ C) (D : Finset (Fin N × Fin (2 * k + 1))) :
    IsUnitaryDilation (Geometry.portRing N (2 * k + 1)) D d (k * if C.Nonempty then 1 else 0)
      ((backwardCircuit (k := k) d C hring hC).map KrausGate.ev) ∧
    ∀ ρ, (backwardCircuit (k := k) d C hring hC).map KrausGate.ev ρ =
      (sitePermOp (routeTotal C hC (List.finRange k)))ᴴ * ρ *
        sitePermOp (routeTotal C hC (List.finRange k)) := by
  have hU : (backwardCircuit (k := k) d C hring hC).Forall KrausGate.ev
      KrausFamily.IsUnitary :=
    Circuit.forall_seq _ _ fun L hL ↦ by
      obtain ⟨L', hL', rfl⟩ := List.mem_map.mp hL
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hL')
      exact forall_isUnitary_adjoint (forall_isUnitary_routeLayer d C hring hC a)
  have hne : ∀ L ∈ ((routeIndex (List.finRange k)).map (routeLayer d C hring hC)).reverse.map
      Layer.adjoint, Nonempty L.Index := fun L hL ↦ by
    obtain ⟨L', hL', rfl⟩ := List.mem_map.mp hL
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hL')
    exact nonempty_index_of_forall_isUnitary
      (forall_isUnitary_adjoint (forall_isUnitary_routeLayer d C hring hC a))
  refine ⟨(Circuit.isUnitaryDilation D _ (hU.mono fun _ h ↦ h.isTP)
    (Circuit.isUnbranched_seq _) (Circuit.isUnitaryOff_of_forall_isUnitary D hU)
    (Circuit.isDimBounded_seq (fun s _ ↦ card_qudits d s) _)).mono le_rfl ?_, fun ρ ↦ ?_⟩
  · unfold backwardCircuit Circuit.seqAdjoint
    rw [Circuit.depth, Circuit.total_seq _ _ hne, List.map_map, List.map_reverse,
      List.sum_reverse]
    exact ((depth_routeLayer d C hring hC _).trans (by rw [List.length_finRange])).le
  · rw [map_eq_of_kraus hU (U := (sitePermOp (routeTotal C hC (List.finRange k)))ᴴ)
      fun p ↦ (Circuit.kraus_seqAdjoint (forall₂_routeLayer d C hring hC _) p).trans
        (by rw [routeKraus]; rfl), conjTranspose_conjTranspose]

end Routing

/-! ### Gates on whole sites -/

section Refine

variable {N k : ℕ}

section Blocks

variable {Y Z : Fin N → Type} (L : Layer (Geometry.sites (Fin N)) KrausGate Y Z)

/-- The site of a block of a layer on single sites. -/
private def blockSite : L.Block → Fin N
  | .inl b => b.1
  | .inr s => s.1

private theorem region_eq_singleton (β : L.Block) : L.region β = {blockSite L β} := by
  cases β <;> rfl

private theorem mem_region_blockOf_iff {i v : Fin N} : v ∈ L.region (L.blockOf i) ↔ v = i := by
  have h := L.mem_region_blockOf i
  rw [region_eq_singleton, Finset.mem_singleton] at h ⊢
  rw [← h]

/-- The blocks of a layer on single sites are its sites. -/
private noncomputable def blockEquiv : Fin N ≃ L.Block where
  toFun := L.blockOf
  invFun := blockSite L
  left_inv i := by
    have h := L.mem_region_blockOf i
    rw [region_eq_singleton, Finset.mem_singleton] at h
    exact h.symm
  right_inv β := L.blockOf_eq_of_mem
    (by rw [region_eq_singleton]; exact Finset.mem_singleton_self _)

end Blocks

variable {X : Fin N × Fin (2 * k + 1) → Type} [∀ w, Fintype (X w)] [∀ w, DecidableEq (X w)]
  (L : Layer (Geometry.sites (Fin N)) KrausGate (blockSystem Prod.fst X) (blockSystem Prod.fst X))

/-- The configurations of the wires of the site `i` are those of the block of `i`. -/
private def wireEquiv (i : Fin N) :
    RegionConfig X ((Geometry.portRing N (2 * k + 1)).cell (inlCell i)) ≃
      RegionConfig (blockSystem Prod.fst X) (L.region (L.blockOf i)) where
  toFun y v w := y ⟨w.1, mem_cell_inlCell.mpr <| by
    have hv := (mem_region_blockOf_iff L).mp v.2
    have hw := w.2
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and] at hw
    rw [hw, hv]⟩
  invFun z w := z ⟨i, (mem_region_blockOf_iff L).mpr rfl⟩ ⟨w.1, by
    simpa using mem_cell_inlCell.mp w.2⟩
  left_inv _ := rfl
  right_inv z := by
    funext ⟨v, hv⟩ w
    obtain rfl := (mem_region_blockOf_iff L).mp hv
    rfl

/-- The gate of the refined layer on a cell of the ring with ports. -/
private noncomputable def refineGate : (c : (Geometry.portRing N (2 * k + 1)).Cell) →
    KrausGate ((Geometry.portRing N (2 * k + 1)).cell c) X X
  | .inl i => (⟨L.BlockIndex (L.blockOf i), L.blockKraus KrausGate.ev (L.blockOf i)⟩ :
      KrausFamily _ _).reindex (wireEquiv L i) (wireEquiv L i)
  | .inr _ => KrausFamily.single 1

/-- The layer of whole-site gates carrying the families of `L` on the blocks of the wires. -/
private noncomputable def refine : Layer (Geometry.portRing N (2 * k + 1)) KrausGate X X :=
  Layer.ofCells _ (pairwiseDisjoint_inl Finset.univ) fun b ↦ refineGate L b.1

/-- The cells of the refined layer are the sites. -/
private noncomputable def refineCellEquiv : Fin N ≃ (refine L).cells where
  toFun i := ⟨inlCell i, Finset.mem_map_of_mem _ (Finset.mem_univ i)⟩
  invFun b := Sum.elim id id b.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨b, hb⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hb
    rfl

private theorem refine_free_isEmpty (s : (refine L).Free) : False :=
  s.2 (Finset.mem_biUnion.mpr ⟨inlCell s.1.1, Finset.mem_map_of_mem _ (Finset.mem_univ _),
    mem_cell_inlCell.mpr rfl⟩)

/-- The Kraus indices of the refined layer are those of `L`. -/
private noncomputable def refineIndexEquiv : (refine L).Index ≃ L.Index :=
  letI : Unique ((s : (refine L).Free) → ((refine L).onsite s).Index) :=
    ⟨⟨fun s ↦ (refine_free_isEmpty L s).elim⟩,
      fun _ ↦ funext fun s ↦ (refine_free_isEmpty L s).elim⟩
  ((Equiv.prodUnique _ _).trans ((Equiv.piCongrLeft _ (refineCellEquiv L)).symm.trans
    ((Equiv.piCongrLeft L.BlockIndex (blockEquiv L)).trans L.indexEquiv.symm)))

private theorem kraus_refine (p : (refine L).Index) (y x : Config X) :
    (refine L).kraus KrausGate.ev p y x =
      L.kraus KrausGate.ev (refineIndexEquiv L p) ((blockConfigEquiv Prod.fst X).symm y)
        ((blockConfigEquiv Prod.fst X).symm x) := by
  rw [Layer.kraus_apply, Fintype.prod_eq_one _ fun s ↦ (refine_free_isEmpty L s).elim, mul_one,
    Layer.kraus_apply_eq_prod, ← (refineCellEquiv L).prod_comp, ← (blockEquiv L).prod_comp]
  refine Fintype.prod_congr _ _ fun i ↦ ?_
  have hidx : L.indexEquiv (refineIndexEquiv L p) (blockEquiv L i) =
      p.1 (refineCellEquiv L i) := by
    unfold refineIndexEquiv
    erw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_symm_apply]
    rfl
  rw [hidx]
  rfl

private theorem depth_refine : (refine L).depth = 0 := by
  rw [Layer.depth, Finset.filter_false_of_mem fun b hb ↦ ?_]
  · rfl
  · obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hb
    rw [cost_inlCell]
    exact lt_irrefl 0

private theorem forall_isTP_refine (hL : L.Forall KrausGate.ev KrausFamily.IsTP) :
    (refine L).Forall KrausGate.ev KrausFamily.IsTP := by
  refine Layer.forall_ofCells _ (KrausFamily.isUnitary_single (one_mem _)).isTP _ _ _ ?_
  rintro ⟨b, hb⟩
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hb
  exact KrausFamily.IsTP.reindex
    (K := ⟨L.BlockIndex (L.blockOf i), L.blockKraus KrausGate.ev (L.blockOf i)⟩)
    (L.blockEffect_eq_one KrausGate.ev hL (L.blockOf i)) _ _

/-- The refined layer is unitary off every set of wires meeting every site. -/
private theorem isUnitaryOff_refine {D : Finset (Fin N × Fin (2 * k + 1))}
    (hD : ∀ i, ∃ w, (i, w) ∈ D) : (refine L).IsUnitaryOff D := by
  refine ⟨fun ⟨b, hb⟩ _ hdis ↦ ?_, fun s _ ↦ (refine_free_isEmpty L s).elim⟩
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hb
  obtain ⟨w, hw⟩ := hD i
  exact (Finset.disjoint_left.mp hdis (mem_cell_inlCell.mpr rfl : (i, w) ∈ _) hw).elim

private theorem map_refine :
    (Circuit.ofLayer (refine L)).map KrausGate.ev ∘ₗ
        (reindexAlgEquiv ℂ ℂ (blockConfigEquiv Prod.fst X)).toLinearMap =
      (reindexAlgEquiv ℂ ℂ (blockConfigEquiv Prod.fst X)).toLinearMap ∘ₗ
        (Circuit.ofLayer L).map KrausGate.ev := by
  refine LinearMap.ext fun ρ ↦ ?_
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, coe_reindexAlgEquiv,
    reindex_apply, Circuit.map_ofLayer]
  exact Layer.map_submatrix_of_op (refineIndexEquiv L) _ _
    (fun p ↦ Matrix.ext fun y x ↦ kraus_refine L p y x) ρ

end Refine

/-! ### Routing a layer of the ring -/

variable {N k d : ℕ} [NeZero d]

/-- **Operations on whole sites are free on the ring with ports.** A layer of trace-preserving
gates and onsite families on the single sites, each acting on all the wires of its site, is
realised on the ring with ports by a map with a unitary dilation of depth `0` whose environments
lie at the wires of a set `D` containing a wire of every site, every wire outside `D` having
dimension `d` throughout the dilating circuit.

Source: arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC", and Supplement,
proof of Proposition 2, p. 8 (operations on one site and its local memory are free). -/
theorem Layer.exists_portRing_sites
    (L : Layer (Geometry.sites (Fin N)) KrausGate
      (blockSystem Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))
      (blockSystem Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)))
    (hL : L.Forall KrausGate.ev KrausFamily.IsTP) (D : Finset (Fin N × Fin (2 * k + 1)))
    (hD : ∀ i, ∃ w, (i, w) ∈ D) :
    ∃ Φ, IsUnitaryDilation (Geometry.portRing N (2 * k + 1)) D d 0 Φ ∧
      Φ ∘ₗ (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap =
        (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (Circuit.ofLayer L).map KrausGate.ev :=
  ⟨_, (Layer.isUnitaryDilation (refine L) D (forall_isTP_refine L hL) (isUnitaryOff_refine L hD)
    (Circuit.isDimBounded_ofLayer _ (fun s _ ↦ card_qudits d s) fun s _ ↦ card_qudits d s)).mono
      le_rfl (depth_refine L).le, map_refine L⟩

variable (N k d) in
/-- The register of a site in its wires: the digit `t` of the register on the data wire `1 + t`,
and `0` on the port and on the scratch wires. -/
def portDataEmbedding (i : Fin N) :
    (Fin k → Fin d) ↪ blockSystem Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d) i where
  toFun x w := (dataIndex w.1.2).elim 0 x
  inj' x x' h := funext fun t ↦ by
    have := congrFun h ⟨(i, dataWire t), by simp⟩
    simpa [dataIndex_dataWire] using this

/-- The registers of the sites `host C⁻¹ {i}` in the wires of the site `i`, through the routing
permutation `τ`. -/
private def routedEmbedding (C : Finset (Fin N)) (τ : Equiv.Perm (Fin N × Fin (2 * k + 1)))
    (hτ : ∀ r t, (τ (r, dataWire t)).1 = host C r) (i : Fin N) :
    blockSystem (host C) (fun _ : Fin N ↦ Fin k → Fin d) i ↪
      blockSystem Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d) i where
  toFun z w := (dataIndex (τ.symm w.1).2).elim 0 fun t ↦
    if h : host C (τ.symm w.1).1 = i then z ⟨(τ.symm w.1).1, by simp [h]⟩ t else 0
  inj' z z' h := by
    funext ⟨r, hr⟩ t
    have hri : host C r = i := by simpa using hr
    have hw : (τ (r, dataWire t)).1 = i := (hτ r t).trans hri
    have := congrFun h ⟨τ (r, dataWire t), by simp [hw]⟩
    simpa [dataIndex_dataWire, hri] using this

private theorem portDataEmbedding_apply (i : Fin N) (x : Fin k → Fin d)
    (w : {w // w ∈ blockPreimage Prod.fst {i}}) :
    portDataEmbedding N k d i x w = (dataIndex w.1.2).elim 0 x :=
  rfl

private theorem routedEmbedding_apply (C : Finset (Fin N))
    (τ : Equiv.Perm (Fin N × Fin (2 * k + 1))) (hτ : ∀ r t, (τ (r, dataWire t)).1 = host C r)
    (i : Fin N) (z : blockSystem (host C) (fun _ : Fin N ↦ Fin k → Fin d) i)
    (w : {w // w ∈ blockPreimage Prod.fst {i}}) :
    routedEmbedding (d := d) C τ hτ i z w = (dataIndex (τ.symm w.1).2).elim 0 fun t ↦
      if h : host C (τ.symm w.1).1 = i then z ⟨(τ.symm w.1).1, by simp [h]⟩ t else 0 :=
  rfl

/-- The routed code is the code of the data wires moved along `τ`. -/
private theorem routed_code (C : Finset (Fin N)) (τ : Equiv.Perm (Fin N × Fin (2 * k + 1)))
    (hτ : ∀ r t, (τ (r, dataWire t)).1 = host C r) :
    basisInclusion
      (((blockConfigEquiv (host C) fun _ : Fin N ↦ Fin k → Fin d).symm.toEmbedding.trans
        (Function.Embedding.piCongrRight (routedEmbedding (d := d) C τ hτ))).trans
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding) =
      sitePermOp τ * basisInclusion ((Function.Embedding.piCongrRight
        (portDataEmbedding N k d)).trans
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding) := by
  ext σ x
  rw [mul_basisInclusion_apply, sitePermOp_apply]
  have key : ∀ w, (((blockConfigEquiv (host C) fun _ : Fin N ↦ Fin k → Fin d).symm.toEmbedding.trans
      (Function.Embedding.piCongrRight (routedEmbedding (d := d) C τ hτ))).trans
        (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding) x w =
      ((Function.Embedding.piCongrRight (portDataEmbedding N k d)).trans
        (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding) x
          (τ.symm w) := by
    intro w
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, blockConfigEquiv_apply,
      Function.Embedding.piCongrRight_apply, routedEmbedding_apply, portDataEmbedding_apply,
      blockConfigEquiv_symm_apply]
    rcases ht : dataIndex (τ.symm w).2 with _ | t
    · rfl
    · have hw : w = τ ((τ.symm w).1, dataWire t) := by
        rw [← eq_dataWire_of_dataIndex ht, Prod.mk.eta, Equiv.apply_symm_apply]
      have h : host C (τ.symm w).1 = w.1 := by rw [← hτ, ← hw]
      simp [h]
  simp only [basisInclusion, submatrix_apply, id, one_apply]
  refine if_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩ rfl rfl
  · funext v
    rw [h, Function.comp_apply, key, Equiv.symm_apply_apply]
  · funext w
    rw [key, h, Function.comp_apply, Equiv.apply_symm_apply]

/-- The data code on the wires is conjugation by the isometry of the data embedding. -/
private theorem dataCode_apply
    (ρ : Matrix (Config fun _ : Fin N ↦ Fin k → Fin d) (Config fun _ : Fin N ↦ Fin k → Fin d) ℂ) :
    (reindexAlgEquiv ℂ ℂ (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)))
        ((encodeCircuit (Geometry.ring N) (portDataEmbedding N k d)).map KrausGate.ev ρ) =
      basisInclusion ((Function.Embedding.piCongrRight (portDataEmbedding N k d)).trans
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding) * ρ *
        (basisInclusion ((Function.Embedding.piCongrRight (portDataEmbedding N k d)).trans
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding))ᴴ := by
  rw [map_encodeCircuit, reindexAlgEquiv_eq_basisInclusion_mul,
    ← basisInclusion_mul_basisInclusion]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

/-- **Routing a layer of the ring to the ports.** Let `L` be a layer of trace-preserving gates on
the ring of `N ≥ 2` sites, each site holding a register of `k` digits. On the ring with ports and
`2k + 1` wires per site, with the register of every site in its data wires, `L` is realised by a
map with a unitary dilation of depth at most `2k` times the depth of `L` whose environments lie
at the wires of a set `D` containing a wire of every site, every wire outside `D` having dimension
at most `d` throughout the dilating circuit: for every cell `{j, j + 1}` of `L` the
register of `j` is moved digit by digit through the two ports into the scratch wires of `j + 1`,
the gate acts inside the site `j + 1`, and the register is moved back. The moves are unitary and
the gates act on whole sites, which meet `D`. The two ports of a cell are distinct sites, which
is where `2 ≤ N` is used.

This lemma is formalization-side: it is the routing step of arXiv:2103.13367, Supplement, proof
of Proposition 2, p. 8, with the depth `2k` per layer. -/
theorem Layer.exists_portRing (hN : 2 ≤ N)
    (L : Layer (Geometry.ring N) KrausGate (fun _ ↦ Fin k → Fin d) (fun _ ↦ Fin k → Fin d))
    (hL : L.Forall KrausGate.ev KrausFamily.IsTP) (D : Finset (Fin N × Fin (2 * k + 1)))
    (hD : ∀ i, ∃ w, (i, w) ∈ D) :
    ∃ Φ, IsUnitaryDilation (Geometry.portRing N (2 * k + 1)) D d (2 * k * L.depth) Φ ∧
      Φ ∘ₗ (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (encodeCircuit (Geometry.ring N) (portDataEmbedding N k d)).map KrausGate.ev =
        (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (encodeCircuit (Geometry.ring N) (portDataEmbedding N k d)).map KrausGate.ev ∘ₗ
            (Circuit.ofLayer L).map KrausGate.ev := by
  have hC := finRotate_notMem hN L.pairwiseDisjoint
  have hτ := routeTotal_dataWire_fst (k := k) L.cells hC
  have hcover : ∀ b ∈ L.cells, ((Geometry.ring N).cell b).image (host L.cells) ⊆
      (Geometry.sites (Fin N)).cell (finRotate N b) := by
    intro b hb v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_singleton.mpr ?_
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact ite_eq_left hb
    · rw [Finset.mem_singleton.mp hu]
      exact ite_eq_right (hC b hb)
  obtain ⟨L₁, -, hL₁, hm₁⟩ := L.exists_coarsen (Γ' := Geometry.sites (Fin N)) (host L.cells)
    (finRotate N) hcover fun _ _ _ _ h ↦ Finset.disjoint_singleton.mpr h
  obtain ⟨L₂, -, hL₂, hm₂⟩ := L₁.exists_encoded (hL₁ hL) (routedEmbedding (d := d) _ _ hτ)
    (routedEmbedding (d := d) _ _ hτ)
  have hm₃ := map_refine L₂
  obtain ⟨hF, hFm⟩ := isUnitaryDilation_forwardCircuit (k := k) d L.cells L.pairwiseDisjoint hC D
  obtain ⟨hB, hBm⟩ := isUnitaryDilation_backwardCircuit (k := k) d L.cells L.pairwiseDisjoint hC D
  have hM : IsUnitaryDilation (Geometry.portRing N (2 * k + 1)) D d 0
      ((Circuit.ofLayer (refine L₂)).map KrausGate.ev) :=
    (Layer.isUnitaryDilation (refine L₂) D (forall_isTP_refine L₂ hL₂)
      (isUnitaryOff_refine L₂ hD) (Circuit.isDimBounded_ofLayer _ (fun s _ ↦ card_qudits d s)
        fun s _ ↦ card_qudits d s)).mono le_rfl (depth_refine L₂).le
  set P := sitePermOp (α := Fin d) (routeTotal L.cells hC (List.finRange k))
  set J := basisInclusion ((Function.Embedding.piCongrRight (portDataEmbedding N k d)).trans
    (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding)
  have hZ : ∀ ρ, (reindexAlgEquiv ℂ ℂ
      (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)))
        ((encodeCircuit (Geometry.sites (Fin N)) (routedEmbedding (d := d) _ _ hτ)).map KrausGate.ev
          (reindexAlgEquiv ℂ ℂ (blockConfigEquiv (host L.cells) _).symm ρ)) =
        (P * J) * ρ * (P * J)ᴴ := by
    intro ρ
    rw [← routed_code L.cells _ hτ, reindexAlgEquiv_eq_basisInclusion_mul,
      map_encodeCircuit, reindexAlgEquiv_eq_basisInclusion_mul,
      ← basisInclusion_mul_basisInclusion,
      ← basisInclusion_mul_basisInclusion]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have hmid : ∀ ρ, (Circuit.ofLayer (refine L₂)).map KrausGate.ev ((P * J) * ρ * (P * J)ᴴ) =
      (P * J) * (Circuit.ofLayer L).map KrausGate.ev ρ * (P * J)ᴴ := by
    intro ρ
    rw [← hZ, ← hZ]
    have h₃ := LinearMap.congr_fun hm₃; have h₂ := LinearMap.congr_fun hm₂
    have h₁ := LinearMap.congr_fun hm₁
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply] at h₁ h₂ h₃
    rw [h₃, h₂, h₁]
  have hPP : Pᴴ * P = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem (sitePermOp_mem_unitary _)
  refine ⟨_, ((hF.comp hM).comp hB).mono le_rfl (le_of_eq ?_), LinearMap.ext fun ρ ↦ ?_⟩
  · rw [depth_ring L]
    ring
  · simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
    rw [dataCode_apply, dataCode_apply, hFm,
      show P * (J * ρ * Jᴴ) * Pᴴ = (P * J) * ρ * (P * J)ᴴ by
        simp only [conjTranspose_mul, Matrix.mul_assoc], hmid, hBm]
    simp only [conjTranspose_mul, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hPP, Matrix.mul_one]
    rfl

end QuantumCircuit
