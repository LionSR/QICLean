/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Compile.Encoding
import QICLean.Circuit.Core.Coarsen
import QICLean.Circuit.Core.Substitute
import QICLean.Circuit.Geometry.Block

/-!
# Blocking protocols

A blocking of a geometry `Γ` into a geometry `Γ'` along a map of sites `f`, with `r` colours,
turns a protocol of depth `T` on `Γ` into a protocol of depth `r * T` on `Γ'`, read on the blocked
systems (`IsProtocol.block`). Layer by layer: a layer on `Γ` is encoded into the sums
`X s ⊕ Y s` of its input and output bases, so that all its parts act on one system; its gates
are split into the `r` colour classes of their covering cells, each a layer whose cells have
pairwise disjoint covering cells, and its onsite families into a layer of their own; every part
is coarsened to a layer on `Γ'` (`Layer.exists_coarsen`), the encoding, the onsite families and
the decoding at depth zero; and the circuits of the layers are assembled by unbranched
substitution (`Circuit.exists_substitute`). A conversion followed by a conversion on the blocks
is a conversion on the blocks (`IsConversion.block_trans`).

On the ring, with the blocking `Geometry.ringBlocking`, a protocol of depth `T` on `M * k`
sites is a protocol of depth `2T` (`M` even) or `3T` (`M` odd) on the `M` blocks of `k`
consecutive sites.

## Main results

* `QuantumCircuit.IsProtocol.block` — a protocol on a geometry is a protocol on its blocks.
* `QuantumCircuit.IsConversion.block_trans` — a conversion followed by a conversion on the
  blocks.

The declarations replace the regrouping of `TNLean/Circuit/Channel/RegroupedProtocol.lean` at
commit `0c76bc5a1a9df19136f61b908497542e5db406da` (Apache-2.0), stated there on the ring with one
dimension at every site and proved by regrouping the bond layers of three colours; here for any
blocking of geometries, any finite bases, and the colouring of the blocking.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}

namespace Layer

section Split

variable {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The onsite family of the layer `L` at a site met by no cell, and the identity at the sites
of the cells. Its index is a choice of an index of the onsite family at every free site equal to
`s`, so that it is uniform in `s`. -/
private def freeFamily (L : Layer Γ KrausGate X X) (s : S) : KrausFamily (X s) (X s) :=
  ⟨(t : {t : L.Free // t.1 = s}) → (L.onsite t.1).Index, fun k ↦
    if h : s ∈ L.cells.biUnion Γ.cell then 1 else (L.onsite ⟨s, h⟩).op (k ⟨⟨s, h⟩, rfl⟩)⟩

omit [∀ s, Fintype (X s)] in
private theorem freeFamily_op_of_mem (L : Layer Γ KrausGate X X) {s : S}
    (h : s ∈ L.cells.biUnion Γ.cell) (k : (freeFamily L s).Index) :
    (freeFamily L s).op k = 1 := by
  simp [freeFamily, h]

omit [∀ s, Fintype (X s)] in
private theorem freeFamily_op_of_notMem (L : Layer Γ KrausGate X X) (t : L.Free)
    (k : (freeFamily L t.1).Index) :
    (freeFamily L t.1).op k = (L.onsite t).op (k ⟨t, rfl⟩) := by
  simp [freeFamily, t.2]

private theorem isTP_freeFamily (L : Layer Γ KrausGate X X)
    (hL : ∀ t, (L.onsite t).IsTP) (s : S) : (freeFamily L s).IsTP := by
  rw [KrausFamily.IsTP, KrausFamily.effect]
  by_cases h : s ∈ L.cells.biUnion Γ.cell
  · have : IsEmpty {t : L.Free // t.1 = s} := ⟨fun t ↦ t.1.2 (by rw [t.2]; exact h)⟩
    let : Unique (freeFamily L s).Index := Pi.uniqueOfIsEmpty _
    rw [Fintype.sum_unique, freeFamily_op_of_mem L h, conjTranspose_one, Matrix.one_mul]
  · let t : L.Free := ⟨s, h⟩
    let : Unique {t : L.Free // t.1 = s} :=
      ⟨⟨⟨t, rfl⟩⟩, fun u ↦ Subtype.ext (Subtype.ext u.2)⟩
    refine (Fintype.sum_equiv
      (Equiv.piUnique fun u : {t : L.Free // t.1 = s} ↦ (L.onsite u.1).Index) _ _
      fun j ↦ ?_).trans (hL t)
    simp only [freeFamily, h, ↓reduceDIte]
    rfl

/-- The onsite families of the layer `L`, as an onsite layer with the identity at the sites of
the cells. -/
private abbrev freeLayer (L : Layer Γ KrausGate X X) : Layer Γ KrausGate X X :=
  ofOnsite (freeFamily L)

/-- The gates of the layer `L`, as a layer with the identity at the sites met by no cell. -/
private abbrev cellLayer (L : Layer Γ KrausGate X X) : Layer Γ KrausGate X X :=
  ofCells L.cells L.pairwiseDisjoint L.gate

/-- An index of the onsite layer and of the layer of gates is an index of the layer. -/
private def splitIndexEquiv (L : Layer Γ KrausGate X X) :
    (freeLayer L).Index × (cellLayer L).Index ≃ L.Index where
  toFun p := (p.2.1, fun t ↦ p.1.2 ⟨t.1, by simp [ofOnsite]⟩ ⟨t, rfl⟩)
  invFun l := ((fun b ↦ absurd b.2 (Finset.notMem_empty _), fun _ t ↦ l.2 t.1),
    (l.1, fun _ ↦ ()))
  left_inv p := by
    obtain ⟨⟨k₁, k₂⟩, i₁, i₂⟩ := p
    refine Prod.ext (Prod.ext (funext fun b ↦ absurd b.2 (Finset.notMem_empty _))
      (funext fun s ↦ funext fun ⟨t, ht⟩ ↦ ?_)) rfl
    have key : ∀ (s' : (freeLayer L).Free) (_ : s' = s) (u : {t : L.Free // t.1 = s'.1}),
        k₂ s' u = k₂ s ⟨u.1, u.2.trans (congrArg Subtype.val ‹s' = s›)⟩ := by
      rintro _ rfl _; rfl
    exact key ⟨t.1, by simp [ofOnsite]⟩ (Subtype.ext ht) ⟨t, rfl⟩
  right_inv _ := rfl

/-- A Kraus operator of the layer is the product of those of the onsite layer and of the layer of
gates. -/
private theorem kraus_split (L : Layer Γ KrausGate X X)
    (p : (freeLayer L).Index × (cellLayer L).Index) :
    (freeLayer L).kraus KrausGate.ev p.1 * (cellLayer L).kraus KrausGate.ev p.2 =
      L.kraus KrausGate.ev (splitIndexEquiv L p) := by
  classical
  obtain ⟨k, i⟩ := p
  set C := L.cells.biUnion Γ.cell
  ext y x
  dsimp only [splitIndexEquiv, Equiv.coe_fn_mk]
  rw [mul_apply, kraus_ofOnsite]
  let w₀ : Config X := fun s ↦ if s ∈ C then y s else x s
  have hcell (b : L.cells) :
      (fun v : {v // v ∈ Γ.cell b} ↦ w₀ v) = fun v : {v // v ∈ Γ.cell b} ↦ y v :=
    funext fun v ↦ ite_eq_left (Finset.mem_biUnion.mpr ⟨b.1, b.2, v.2⟩)
  have hfree (t : L.Free) : w₀ t = x t := ite_eq_right t.2
  rw [Finset.sum_eq_single w₀ (fun w _ hw ↦ ?_) fun h ↦ absurd (Finset.mem_univ _) h]
  · have hprod : ∏ s, (freeFamily L s).op (k.2 ⟨s, by simp [ofOnsite]⟩) (y s) (w₀ s) =
        ∏ t : L.Free, (L.onsite t).op (k.2 ⟨t.1, by simp [ofOnsite]⟩ ⟨t, rfl⟩) (y t) (x t) := by
      rw [← Finset.prod_subset (Finset.subset_univ Cᶜ) fun s _ hs ↦ ?_,
        Finset.prod_subtype Cᶜ (p := (· ∉ C)) fun _ ↦ Finset.mem_compl]
      · refine Fintype.prod_congr _ _ fun t ↦ ?_
        have h := freeFamily_op_of_notMem L t (k.2 ⟨t, by simp [ofOnsite]⟩)
        rw [h, hfree t]
      · have hs : s ∈ C := by simpa using hs
        have h := freeFamily_op_of_mem L hs (k.2 ⟨s, by simp [ofOnsite]⟩)
        rw [h, show w₀ s = y s from ite_eq_left hs, one_apply_eq]
    have h₂ : ∏ t : (cellLayer L).Free, ((cellLayer L).onsite t).op (i.2 t) (w₀ t) (x t) = 1 :=
      Fintype.prod_eq_one _ fun t ↦ by
        change (1 : Matrix (X t) (X t) ℂ) (w₀ t) (x t) = 1
        rw [hfree t, one_apply_eq]
    rw [prodOp_apply, kraus_apply, kraus_apply, hprod, h₂, mul_one, mul_comm]
    congr 1
    exact Fintype.prod_congr _ _ fun b ↦ by
      change (L.gate b).op _ (fun v ↦ w₀ v) _ = _
      rw [hcell b]
      rfl
  · obtain ⟨s, hs⟩ := Function.ne_iff.mp hw
    by_cases h : s ∈ C
    · refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ s) ?_) _
      have h' := freeFamily_op_of_mem L h (k.2 ⟨s, by simp [ofOnsite]⟩)
      dsimp only
      rw [h', one_apply_ne]
      intro e
      exact hs (e.symm.trans (ite_eq_left h).symm)
    · refine mul_eq_zero_of_right _ ?_
      rw [kraus_apply]
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨s, h⟩) ?_)
      change (1 : Matrix (X s) (X s) ℂ) (w s) (x s) = 0
      exact one_apply_ne fun e ↦ hs (e.trans (ite_eq_right h).symm)

/-- The map of the layer `L` is the map of its gates followed by the map of its onsite
families. -/
private theorem map_split (L : Layer Γ KrausGate X X) :
    (Circuit.ofLayer L).map KrausGate.ev =
      (Circuit.ofLayer (freeLayer L)).map KrausGate.ev ∘ₗ
        (Circuit.ofLayer (cellLayer L)).map KrausGate.ev := by
  refine LinearMap.ext fun ρ ↦ ?_
  simp only [Circuit.map_ofLayer, LinearMap.comp_apply, KrausFamily.map_apply]
  change ∑ l : L.Index, L.kraus KrausGate.ev l * ρ * (L.kraus KrausGate.ev l)ᴴ =
    ∑ k : (freeLayer L).Index, (freeLayer L).kraus KrausGate.ev k *
      (∑ i : (cellLayer L).Index, (cellLayer L).kraus KrausGate.ev i * ρ *
        ((cellLayer L).kraus KrausGate.ev i)ᴴ) * ((freeLayer L).kraus KrausGate.ev k)ᴴ
  rw [← (splitIndexEquiv L).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← kraus_split L (k, i), conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The gates of a colour class of a layer of gates with the identity elsewhere. -/
private abbrev colourLayer (cells : Finset Γ.Cell)
    (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell) (g : (b : cells) → KrausGate (Γ.cell b) X X)
    {r : ℕ} (κ : Γ.Cell → Fin r) (c : Fin r) : Layer Γ KrausGate X X :=
  ofCells (cells.filter (κ · = c))
    (h.subset (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
    fun b ↦ g ⟨b.1, (Finset.mem_filter.mp b.2).1⟩

/-- A layer of gates on disjoint cells, with the identity elsewhere, is the composite of the
layers of its colour classes for any colouring of its cells. -/
private theorem map_ofCells_eq_prod (cells : Finset Γ.Cell)
    (h : (cells : Set Γ.Cell).PairwiseDisjoint Γ.cell) (g : (b : cells) → KrausGate (Γ.cell b) X X)
    {r : ℕ} (κ : Γ.Cell → Fin r) :
    (Circuit.ofLayer (ofCells cells h g)).map KrausGate.ev =
      (List.ofFn fun c ↦ (Circuit.ofLayer (colourLayer cells h g κ c)).map KrausGate.ev).prod := by
  let incl (c : Fin r) (b : {b // b ∈ cells.filter (κ · = c)}) : cells :=
    ⟨b.1, (Finset.mem_filter.mp b.2).1⟩
  have hincl (c : Fin r) : Function.Injective (incl c) :=
    fun a b e ↦ Subtype.ext (congrArg Subtype.val e :)
  let l : List cells := (List.ofFn fun c ↦ (Finset.univ.toList).map (incl c)).flatten
  have hl : l.Nodup := by
    refine List.nodup_flatten.mpr ⟨fun l' hl' ↦ ?_, List.pairwise_ofFn.mpr fun i j hij ↦ ?_⟩
    · obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hl'
      exact (Finset.nodup_toList _).map (hincl c)
    · refine List.disjoint_left.mpr fun b hbi hbj ↦ ?_
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hbi
      obtain ⟨a', -, e⟩ := List.mem_map.mp hbj
      have hi := (Finset.mem_filter.mp a.2).2
      have hj := (Finset.mem_filter.mp a'.2).2
      rw [show a'.1 = a.1 from congrArg Subtype.val e] at hj
      exact hij.ne (hi.symm.trans hj)
  have hall (b : cells) : b ∈ l := by
    refine List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨κ b.1, rfl⟩, List.mem_map.mpr
      ⟨⟨b.1, Finset.mem_filter.mpr ⟨b.2, rfl⟩⟩, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩⟩
  simp only [Circuit.map_ofLayer]
  rw [map_ofCells KrausGate.ev cells h g l hl hall, List.map_flatten, List.prod_flatten,
    List.map_ofFn, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.mpr (funext fun c ↦ ?_)
  rw [Function.comp_apply, Function.comp_apply, map_ofCells KrausGate.ev _ _ _ Finset.univ.toList
    (Finset.nodup_toList _) fun b ↦ Finset.mem_toList.mpr (Finset.mem_univ _), List.map_map]
  rfl

end Split

section Block

variable {S' : Type} [Fintype S'] [DecidableEq S'] {Γ' : Geometry S'} {f : S → S'} {r : ℕ}

/-- The linear map `A` is realised on the blocks of `f` by a protocol of depth at most `n` on
`Γ'`: there is such a protocol intertwining the blockings of the matrices. -/
private def IsBlocked (Γ' : Geometry S') (f : S → S') (n : ℕ) {X Y : S → Type}
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (A : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Y) (Config Y) ℂ) : Prop :=
  ∃ Φ', IsProtocol Γ' n Φ' ∧
    Φ' ∘ₗ (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f X).symm).toLinearMap =
      (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f Y).symm).toLinearMap ∘ₗ A

variable {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]

private theorem IsBlocked.comp {n m : ℕ}
    {A : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Y) (Config Y) ℂ}
    {B : Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (hA : IsBlocked Γ' f n A) (hB : IsBlocked Γ' f m B) : IsBlocked Γ' f (n + m) (B ∘ₗ A) := by
  obtain ⟨Φ, hΦ, hΦA⟩ := hA
  obtain ⟨Ψ, hΨ, hΨB⟩ := hB
  refine ⟨Ψ ∘ₗ Φ, hΦ.comp hΨ, ?_⟩
  rw [LinearMap.comp_assoc, hΦA, ← LinearMap.comp_assoc, hΨB, LinearMap.comp_assoc]

private theorem IsBlocked.mono {n m : ℕ}
    {A : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Y) (Config Y) ℂ}
    (hA : IsBlocked Γ' f n A) (hnm : n ≤ m) : IsBlocked Γ' f m A :=
  let ⟨Φ, hΦ, hΦA⟩ := hA
  ⟨Φ, hΦ.mono hnm, hΦA⟩

/-- A product of maps each realised on the blocks in depth one is realised in depth the number
of factors. -/
private theorem isBlocked_prod
    (l : List (Module.End ℂ (Matrix (Config X) (Config X) ℂ)))
    (hl : ∀ A ∈ l, IsBlocked Γ' f 1 A) : IsBlocked Γ' f l.length l.prod := by
  induction l with
  | nil =>
    refine ⟨LinearMap.id, IsProtocol.id, ?_⟩
    rw [List.prod_nil, Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_id]
  | cons A l ih =>
    rw [List.prod_cons, Module.End.mul_eq_comp, List.length_cons]
    exact (ih fun B hB ↦ hl B (List.mem_cons_of_mem _ hB)).comp (hl A List.mem_cons_self)

/-- A trace-preserving layer whose cells have pairwise disjoint covering cells is realised on the
blocks in depth one, and in depth zero when it has no cells. -/
private theorem isBlocked_layer (hB : Γ.Blocking Γ' f r) (L : Layer Γ KrausGate X Y)
    (hL : ∀ b₁ ∈ L.cells, ∀ b₂ ∈ L.cells, hB.cover b₁ ≠ hB.cover b₂ →
      Disjoint (Γ'.cell (hB.cover b₁)) (Γ'.cell (hB.cover b₂)))
    (hTP : L.Forall KrausGate.ev KrausFamily.IsTP) :
    IsBlocked Γ' f (if L.cells = ∅ then 0 else 1) ((Circuit.ofLayer L).map KrausGate.ev) := by
  obtain ⟨L', hcells, hTP', hmap⟩ :=
    L.exists_coarsen f hB.cover (fun b _ ↦ hB.image_subset b) hL
  refine ⟨_, ⟨Circuit.ofLayer L', ⟨hTP' hTP, fun _ ↦ trivial⟩, ?_, rfl,
    Circuit.isUnbranched_ofLayer L'⟩, hmap⟩
  rw [Circuit.depth_ofLayer, Layer.depth]
  split_ifs with h₁ h₂ <;> try omega
  rw [hcells, h₂, Finset.image_empty, Finset.filter_empty] at h₁
  exact absurd h₁ Finset.not_nonempty_empty

omit [Fintype S] [Fintype S'] [DecidableEq S'] in
/-- An onsite layer has no cells. -/
private theorem cells_ofOnsite {X Y : S → Type} (o : (s : S) → KrausFamily (X s) (Y s)) :
    (ofOnsite (Γ := Γ) (G := KrausGate) o).cells = ∅ :=
  rfl

/-- A trace-preserving layer on nonempty bases is realised on the blocks in `r` times its depth.
The layer is encoded into the sums of its input and output bases, split into its onsite families
and the `r` colour classes of its gates, and each part is coarsened. -/
private theorem exists_block_layer (hB : Γ.Blocking Γ' f r) [∀ s, Nonempty (X s)]
    (L : Layer Γ KrausGate X Y) (hTP : L.Forall KrausGate.ev KrausFamily.IsTP) :
    ∃ c' : Circuit Γ' KrausGate (blockSystem f X) (blockSystem f Y), c'.IsUnbranched ∧
      c'.Forall KrausGate.ev KrausFamily.IsTP ∧ c'.depth ≤ r * L.depth ∧
      c'.map KrausGate.ev ∘ₗ (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f X).symm).toLinearMap =
        (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f Y).symm).toLinearMap ∘ₗ
          (Circuit.ofLayer L).map KrausGate.ev := by
  suffices h : IsBlocked Γ' f (r * L.depth) ((Circuit.ofLayer L).map KrausGate.ev) by
    obtain ⟨_, ⟨c', hTP', hd, rfl, hu⟩, hm⟩ := h
    exact ⟨c', hu, hTP', hd, hm⟩
  by_cases hcells : L.cells = ∅
  · refine (isBlocked_layer hB L (by simp [hcells]) hTP).mono ?_
    rw [ite_eq_left hcells]
    exact Nat.zero_le _
  have hdepth : L.depth = 1 := by
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hcells
    exact ite_eq_left ⟨b, Finset.mem_filter.mpr ⟨hb, hB.cost_pos b⟩⟩
  rw [hdepth, mul_one]
  have := L.nonempty_output_of_forall_isTP KrausGate.ev hTP
  let W : S → Type := fun s ↦ X s ⊕ Y s
  let e : ∀ s, X s ↪ W s := fun _ ↦ Function.Embedding.inl
  let e' : ∀ s, Y s ↪ W s := fun _ ↦ Function.Embedding.inr
  let y₀ : ∀ s, Y s := fun _ ↦ Classical.arbitrary _
  obtain ⟨L', hcells', hTP', hL'⟩ := L.exists_encoded hTP e e'
  have hmap : (Circuit.ofLayer L).map KrausGate.ev =
      (decodeCircuit Γ e' y₀).map KrausGate.ev ∘ₗ
        ((Circuit.ofLayer (freeLayer L')).map KrausGate.ev ∘ₗ
          ((List.ofFn fun c ↦ (Circuit.ofLayer (colourLayer L'.cells L'.pairwiseDisjoint L'.gate
            (hB.colour ∘ hB.cover) c)).map KrausGate.ev).prod ∘ₗ
              (encodeCircuit Γ e).map KrausGate.ev)) := by
    calc (Circuit.ofLayer L).map KrausGate.ev
        = (decodeCircuit Γ e' y₀).map KrausGate.ev ∘ₗ ((encodeCircuit Γ e').map KrausGate.ev ∘ₗ
            (Circuit.ofLayer L).map KrausGate.ev) := by
          rw [← LinearMap.comp_assoc, map_decodeCircuit_comp_map_encodeCircuit, LinearMap.id_comp]
      _ = (decodeCircuit Γ e' y₀).map KrausGate.ev ∘ₗ ((Circuit.ofLayer L').map KrausGate.ev ∘ₗ
            (encodeCircuit Γ e).map KrausGate.ev) := by rw [hL']
      _ = _ := by
          rw [map_split L', map_ofCells_eq_prod _ _ _ (hB.colour ∘ hB.cover)]
          simp only [LinearMap.comp_assoc]
  rw [hmap]
  refine IsBlocked.mono (n := 0 + r + 0 + 0)
    (IsBlocked.comp (IsBlocked.comp (IsBlocked.comp ?_ ?_) ?_) ?_) (by omega)
  · refine (isBlocked_layer hB _ (by simp [cells_ofOnsite])
      ⟨fun b ↦ absurd b.2 (by simp [ofOnsite]),
      fun _ ↦ KrausFamily.isTP_embed _⟩).mono ?_
    simp [cells_ofOnsite]
  · refine (isBlocked_prod _ fun A hA ↦ ?_).mono (List.length_ofFn).le
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hA
    refine (isBlocked_layer hB _ (fun b₁ hb₁ b₂ hb₂ hne ↦ hB.disjoint _ _ ?_ hne) ?_).mono ?_
    · exact ((Finset.mem_filter.mp hb₁).2.trans (Finset.mem_filter.mp hb₂).2.symm :)
    · refine forall_ofCells KrausGate.ev
        (fun {α} _ _ ↦ (KrausFamily.isUnitary_single (one_mem _)).isTP) _ _ _ fun b ↦ ?_
      exact hTP'.1 ⟨b.1, (Finset.mem_filter.mp b.2).1⟩
    · split_ifs <;> omega
  · refine (isBlocked_layer hB _ (by simp [cells_ofOnsite])
      ⟨fun b ↦ absurd b.2 (by simp [ofOnsite]),
      fun s ↦ isTP_freeFamily L' hTP'.2 s.1⟩).mono ?_
    simp [cells_ofOnsite]
  · refine (isBlocked_layer hB _ (by simp [cells_ofOnsite])
      ⟨fun b ↦ absurd b.2 (by simp [ofOnsite]),
      fun _ ↦ KrausFamily.isTP_decode _ _⟩).mono ?_
    simp [cells_ofOnsite]

end Block

end Layer

section Block

variable {S' : Type} [Fintype S'] [DecidableEq S'] {Γ' : Geometry S'} {f : S → S'} {r : ℕ}
  {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]

/-- **Blocking a protocol.** Let `Γ` be blocked into `Γ'` along `f` with `r` colours. A protocol of
depth `T` on `Γ` from `X` to `Z` is, read on the blocks, a protocol of depth `r * T` on `Γ'` from
the blocked system of `X` to that of `Z`: its map is `Φ` conjugated by the identifications of the
configurations of the systems with those of the blocked systems.

The input bases are nonempty: the layers are realised one at a time along the unbranched circuit
of the protocol, and on an empty basis the empty Kraus family is trace-preserving, so a layer
would have no branch to continue along (`Circuit.exists_substitute`). On the ring, with
`Geometry.ringBlocking`, the depth is `2T` for an even number of blocks and `3T` for an odd one.

This theorem is formalization-side: it is the blocking of arXiv:2103.13367v3, `main.tex`,
lines 287–289, for any blocking of geometries. -/
theorem IsProtocol.block [∀ s, Nonempty (X s)] (hB : Γ.Blocking Γ' f r) {T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol Γ T Φ) :
    IsProtocol Γ' (r * T)
      ((reindexAlgEquiv ℂ ℂ (blockConfigEquiv f Z).symm).toLinearMap ∘ₗ Φ ∘ₗ
        (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f X)).toLinearMap) := by
  obtain ⟨c, hTP, hd, rfl, hu⟩ := h
  let Ψ : SystemMap S S' := ⟨blockSystem f, fun _ _ ↦ inferInstance, fun _ _ ↦ inferInstance⟩
  obtain ⟨c', hu', hTP', hd', hm⟩ := Circuit.exists_substitute (Γ' := Γ') Ψ
    (fun X _ _ ↦ (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f X).symm).toLinearMap) r
    (fun _ _ _ _ _ _ _ L hL ↦ Layer.exists_block_layer hB L hL) c hu hTP
  refine ⟨c', hTP', hd'.trans (Nat.mul_le_mul_left r hd), ?_, hu'⟩
  have hid : (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f X).symm).toLinearMap ∘ₗ
      (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f X)).toLinearMap = LinearMap.id := by
    refine LinearMap.ext fun ρ ↦ ?_
    simp
  rw [← LinearMap.comp_id (c'.map KrausGate.ev), ← hid, ← LinearMap.comp_assoc, hm,
    LinearMap.comp_assoc]

/-- **A conversion followed by a conversion on the blocks.** If `ρ` is converted into `σ` in depth
`T` on `Γ`, and the blocked `σ` is converted into `τ` in depth `U` on `Γ'`, then the blocked `ρ`
is converted into `τ` in depth `r * T + U` on `Γ'`. The input bases are nonempty, as in
`IsProtocol.block`.

Source: arXiv:2103.13367v3, `main.tex`, lines 287–289 (a state is converted, its sites are
grouped into blocks, and the blocked state is converted further). -/
theorem IsConversion.block_trans [∀ s, Nonempty (X s)] (hB : Γ.Blocking Γ' f r) {T U : ℕ}
    {Z' : S' → Type} [∀ s, Fintype (Z' s)] {ρ : Matrix (Config X) (Config X) ℂ}
    {σ : Matrix (Config Y) (Config Y) ℂ} {τ : Matrix (Config Z') (Config Z') ℂ}
    (h₁ : IsConversion Γ T ρ σ)
    (h₂ : IsConversion Γ' U
      (reindex (blockConfigEquiv f Y).symm (blockConfigEquiv f Y).symm σ) τ) :
    IsConversion Γ' (r * T + U)
      (reindex (blockConfigEquiv f X).symm (blockConfigEquiv f X).symm ρ) τ := by
  obtain ⟨Φ, hΦ, rfl⟩ := h₁
  obtain ⟨Ψ, hΨ, rfl⟩ := h₂
  refine ⟨_, (hΦ.block hB).comp hΨ, ?_⟩
  simp

end Block

end QuantumCircuit
