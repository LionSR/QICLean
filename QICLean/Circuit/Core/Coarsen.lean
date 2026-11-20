/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.LayerDual
import QICLean.Circuit.Core.Parallel
import QICLean.ManyBody.Sites.Block
import QICLean.ManyBody.Sites.ProductFamily

/-!
# Coarsening a layer along blocks of sites

Let a map of sites `f : S → S'` group the sites of a geometry `Γ` into blocks, the sites of a
geometry `Γ'`, and let every cell `b` used by a layer `L` on `Γ` lie, after `f`, in a cell
`cover b` of `Γ'`, distinct covering cells being disjoint. Then `L`, read on the blocked
systems, is a layer on `Γ'` with the covering cells (`Layer.exists_coarsen`). Its gate on a
covering cell `c` is the product of the gates of `L` on the cells covered by `c` and of the
onsite families of `L` at the remaining sites of the blocks of `c`; its onsite family at a block
met by no covering cell is the product of the onsite families of `L` at the sites of the block.
The blocks of `L`, its cells and its remaining sites, are thereby distributed among the blocks
of the coarse layer, and the Kraus operators of the two layers are the same products of local
entries.

## Main results

* `QuantumCircuit.Layer.exists_coarsen` — a layer whose cells have disjoint covering cells is a
  layer on the blocks.
-/

open Matrix ManyBody

namespace QuantumCircuit

namespace Layer

variable {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']
  {Γ : Geometry S} {Γ' : Geometry S'} {X Y : S → Type}

/-- A product over the fibres of a map is the product over its domain. -/
private theorem prod_fibre {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [CommMonoid M] (κ : α → β) (H : (b : β) → {a // κ a = b} → M) :
    ∏ b, ∏ a, H b a = ∏ a, H (κ a) ⟨a, rfl⟩ := by
  rw [← Fintype.prod_sigma fun p : (Σ b, {a // κ a = b}) ↦ H p.1 p.2]
  exact Fintype.prod_equiv (Equiv.sigmaFiberEquiv κ) _ _ fun ⟨_, _, h⟩ ↦ by subst h; rfl

/-- Kraus families whose operators agree up to relabelling the bases and the indices have maps
that agree up to the relabelling. -/
theorem map_submatrix_of_op {α β α' β' : Type} [Fintype α] [Fintype α']
    {K : KrausFamily α β} {K' : KrausFamily α' β'} (φ : K'.Index ≃ K.Index) (e : α' ≃ α)
    (e' : β' ≃ β) (h : ∀ i, K'.op i = (K.op (φ i)).submatrix e' e) (ρ : Matrix α α ℂ) :
    K'.map (ρ.submatrix e e) = (K.map ρ).submatrix e' e' := by
  rw [KrausFamily.map_apply, KrausFamily.map_apply, ← φ.symm.sum_comp]
  ext a b
  simp only [Matrix.sum_apply, submatrix_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h, Equiv.apply_symm_apply, conjTranspose_submatrix, submatrix_mul_equiv,
    submatrix_mul_equiv, submatrix_apply]

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)]

section Coarsen

variable (f : S → S') (cover : Γ.Cell → Γ'.Cell) (L : Layer Γ KrausGate X Y)
  (hcover : ∀ b ∈ L.cells, (Γ.cell b).image f ⊆ Γ'.cell (cover b))
  (hL : ∀ b₁ ∈ L.cells, ∀ b₂ ∈ L.cells, cover b₁ ≠ cover b₂ →
    Disjoint (Γ'.cell (cover b₁)) (Γ'.cell (cover b₂)))

omit [Fintype S] [Fintype S'] [DecidableEq S'] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] in
include hL in
/-- The covering cells of the cells of the layer are pairwise disjoint. -/
private theorem pairwiseDisjoint_image_cover :
    ((L.cells.image cover : Finset Γ'.Cell) : Set Γ'.Cell).PairwiseDisjoint Γ'.cell := by
  intro c₁ hc₁ c₂ hc₂ hne
  obtain ⟨b₁, hb₁, rfl⟩ := Finset.mem_image.mp hc₁
  obtain ⟨b₂, hb₂, rfl⟩ := Finset.mem_image.mp hc₂
  exact hL b₁ hb₁ b₂ hb₂ hne

/-- The blocks of the coarse layer: its covering cells and the blocks met by none of them,
described by a layer with these cells and identity gates. -/
private abbrev skeleton : Layer Γ' KrausGate (fun _ ↦ PUnit) (fun _ ↦ PUnit) :=
  ofCells (L.cells.image cover) (pairwiseDisjoint_image_cover cover L hL)
    fun _ ↦ KrausFamily.single 1

/-- The block of the coarse layer receiving a block of the layer: the covering cell of a cell,
and the coarse block containing the block of a remaining site. -/
private noncomputable def coarseBlock : L.Block → (skeleton cover L hL).Block
  | .inl b => .inl ⟨cover b, Finset.mem_image_of_mem cover b.2⟩
  | .inr v => (skeleton cover L hL).blockOf (f v)

omit [Fintype S] [Fintype S'] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] in
include hcover in
private theorem mem_region_coarseBlock (β : L.Block) {v : S} (hv : v ∈ L.region β) :
    f v ∈ (skeleton cover L hL).region (coarseBlock f cover L hL β) := by
  match β with
  | .inl b => exact hcover b b.2 (Finset.mem_image_of_mem f hv)
  | .inr s =>
    rw [Finset.mem_singleton.mp hv]
    exact (skeleton cover L hL).mem_region_blockOf (f s.1)

omit [Fintype S] [Fintype S'] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] in
include hcover in
private theorem coarseBlock_blockOf {v : S} {β' : (skeleton cover L hL).Block}
    (hv : f v ∈ (skeleton cover L hL).region β') :
    coarseBlock f cover L hL (L.blockOf v) = β' :=
  ((skeleton cover L hL).blockOf_eq_of_mem
    (mem_region_coarseBlock f cover L hcover hL _ (L.mem_region_blockOf v))).symm.trans
    ((skeleton cover L hL).blockOf_eq_of_mem hv)

/-- The blocks of the layer received by a coarse block. -/
private abbrev Fibre (β' : (skeleton cover L hL).Block) : Type :=
  {β : L.Block // coarseBlock f cover L hL β = β'}

/-- A configuration of the blocked system on a coarse block is a configuration on every block
of the layer it receives. -/
private noncomputable def fibreEquiv (Z : S → Type) (β' : (skeleton cover L hL).Block) :
    RegionConfig (blockSystem f Z) ((skeleton cover L hL).region β') ≃
      ((β : Fibre f cover L hL β') → RegionConfig Z (L.region β.1)) where
  toFun z β v := z ⟨f v, by
    obtain ⟨β, rfl⟩ := β
    exact mem_region_coarseBlock f cover L hcover hL β v.2⟩ ⟨v, by simp⟩
  invFun F s' w := F ⟨L.blockOf w, coarseBlock_blockOf f cover L hcover hL
    (by rw [Finset.mem_singleton.mp (Finset.mem_filter.mp w.2).2]; exact s'.2)⟩
    ⟨w, L.mem_region_blockOf w⟩
  left_inv z := by
    funext ⟨s', hs'⟩ ⟨w, hw⟩
    have key : ∀ t (_ : t = s') (ht : t ∈ (skeleton cover L hL).region β')
        (hw' : w ∈ blockPreimage f {t}), z ⟨t, ht⟩ ⟨w, hw'⟩ = z ⟨s', hs'⟩ ⟨w, hw⟩ := by
      rintro _ rfl _ _; rfl
    exact key _ (Finset.mem_singleton.mp (Finset.mem_filter.mp hw).2) _ _
  right_inv F := by
    funext ⟨β, hβ⟩ ⟨v, hv⟩
    have key : ∀ γ (_ : γ = β) (hγ : coarseBlock f cover L hL γ = β')
        (hv' : v ∈ L.region γ), F ⟨γ, hγ⟩ ⟨v, hv'⟩ = F ⟨β, hβ⟩ ⟨v, hv⟩ := by
      rintro _ rfl _ _; rfl
    exact key _ (L.blockOf_eq_of_mem hv) _ _

/-- The family of the coarse layer on a coarse block: the product of the families of the
layer on the blocks it receives. -/
private noncomputable def coarseFamily (β' : (skeleton cover L hL).Block) :
    KrausFamily (RegionConfig (blockSystem f X) ((skeleton cover L hL).region β'))
      (RegionConfig (blockSystem f Y) ((skeleton cover L hL).region β')) :=
  (prodFamily fun β : Fibre f cover L hL β' ↦
      (⟨L.BlockIndex β.1, L.blockKraus KrausGate.ev β.1⟩ :
        KrausFamily (RegionConfig X (L.region β.1)) (RegionConfig Y (L.region β.1)))).reindex
    (fibreEquiv f cover L hcover hL X β') (fibreEquiv f cover L hcover hL Y β')

/-- The configurations of a system on a single site. -/
private def singletonEquiv (Z : S' → Type) (s : S') : Z s ≃ RegionConfig Z {s} :=
  letI : Unique {v // v ∈ ({s} : Finset S')} :=
    ⟨⟨⟨s, Finset.mem_singleton_self s⟩⟩, fun v ↦ Subtype.ext (Finset.mem_singleton.mp v.2)⟩
  (Equiv.piUnique fun v : {v // v ∈ ({s} : Finset S')} ↦ Z v).symm

omit [Fintype S'] [DecidableEq S'] in
private theorem singletonEquiv_apply (Z : S' → Type) (z : (s : S') → Z s) (s : S') :
    singletonEquiv Z s (z s) = fun v : {v // v ∈ ({s} : Finset S')} ↦ z v.1 := by
  funext ⟨t, ht⟩
  obtain rfl : t = s := Finset.mem_singleton.mp ht
  rfl

/-- The coarse layer. -/
private noncomputable def coarsen : Layer Γ' KrausGate (blockSystem f X) (blockSystem f Y) where
  cells := L.cells.image cover
  pairwiseDisjoint := pairwiseDisjoint_image_cover cover L hL
  gate c := coarseFamily f cover L hcover hL (.inl c)
  onsite s := (coarseFamily f cover L hcover hL (.inr s)).reindex
    (singletonEquiv (blockSystem f X) s.1) (singletonEquiv (blockSystem f Y) s.1)

/-- A Kraus index of the coarse layer, as an index of the layer on every block received by
every coarse block. -/
private def toFibre (i' : (coarsen f cover L hcover hL).Index) :
    (β' : (skeleton cover L hL).Block) → (β : Fibre f cover L hL β') → L.BlockIndex β.1
  | .inl c => i'.1 c
  | .inr s => i'.2 s

omit [Fintype S'] in
private theorem toFibre_congr (i' : (coarsen f cover L hcover hL).Index) {β : L.Block}
    {β' : (skeleton cover L hL).Block} (h : coarseBlock f cover L hL β = β') :
    toFibre f cover L hcover hL i' β' ⟨β, h⟩ =
      toFibre f cover L hcover hL i' (coarseBlock f cover L hL β) ⟨β, rfl⟩ := by
  subst h; rfl

/-- The Kraus indices of the coarse layer are those of the layer. -/
private noncomputable def coarsenIndexEquiv :
    (coarsen f cover L hcover hL).Index ≃ L.Index where
  toFun i' := L.indexEquiv.symm fun β ↦
    toFibre f cover L hcover hL i' (coarseBlock f cover L hL β) ⟨β, rfl⟩
  invFun i := (fun _ β ↦ L.indexEquiv i β.1, fun _ β ↦ L.indexEquiv i β.1)
  left_inv i' := by
    refine Prod.ext (funext fun c ↦ funext fun β ↦ ?_) (funext fun s ↦ funext fun β ↦ ?_)
    · simp only [Equiv.apply_symm_apply]
      exact (toFibre_congr f cover L hcover hL i' β.2).symm
    · simp only [Equiv.apply_symm_apply]
      exact (toFibre_congr f cover L hcover hL i' β.2).symm
  right_inv i := by
    refine L.indexEquiv.injective (funext fun β ↦ ?_)
    rw [Equiv.apply_symm_apply]
    have key : ∀ β' (h : coarseBlock f cover L hL β = β'),
        toFibre f cover L hcover hL (fun _ β ↦ L.indexEquiv i β.1, fun _ β ↦ L.indexEquiv i β.1)
          β' ⟨β, h⟩ = L.indexEquiv i β := by
      rintro (_ | _) _ <;> rfl
    exact key _ rfl

/-- The Kraus operators of the coarse layer are those of the layer, read on the blocks. -/
private theorem kraus_coarsen (i' : (coarsen f cover L hcover hL).Index) :
    (coarsen f cover L hcover hL).kraus KrausGate.ev i' =
      (L.kraus KrausGate.ev (coarsenIndexEquiv f cover L hcover hL i')).submatrix
        (blockConfigEquiv f Y) (blockConfigEquiv f X) := by
  ext z w
  rw [submatrix_apply, kraus_apply, kraus_apply_eq_prod]
  have hfree (s : (coarsen f cover L hcover hL).Free) :
      ((coarsen f cover L hcover hL).onsite s).op (i'.2 s) (z s) (w s) =
        (coarseFamily f cover L hcover hL (.inr s)).op (i'.2 s) (fun v ↦ z v) fun v ↦ w v := by
    exact congr_arg₂ ((coarseFamily f cover L hcover hL (.inr s)).op (i'.2 s))
      (singletonEquiv_apply _ z s.1) (singletonEquiv_apply _ w s.1)
  simp only [hfree]
  trans ∏ β' : (skeleton cover L hL).Block, ∏ β : Fibre f cover L hL β',
    L.blockKraus KrausGate.ev β.1 (toFibre f cover L hcover hL i' β' β)
      (fibreEquiv f cover L hcover hL Y β' (fun v ↦ z v) β)
      (fibreEquiv f cover L hcover hL X β' (fun v ↦ w v) β)
  · rw [Fintype.prod_sum_type]
    rfl
  rw [prod_fibre (coarseBlock f cover L hL)]
  refine Fintype.prod_congr _ _ fun β ↦ ?_
  have hi : L.indexEquiv (coarsenIndexEquiv f cover L hcover hL i') β =
      toFibre f cover L hcover hL i' (coarseBlock f cover L hL β) ⟨β, rfl⟩ :=
    congrFun (L.indexEquiv.apply_symm_apply _) β
  rw [hi]
  rfl

end Coarsen

/-- **Coarsening a layer.** Let `f` group the sites of `Γ` into the sites of `Γ'`, let every
cell `b` of the layer `L` lie, after `f`, in the cell `cover b` of `Γ'`, and let distinct
covering cells be disjoint. Then there is a layer `L'` on `Γ'` from the blocked system of `X` to
that of `Y` with the covering cells as its cells, trace-preserving when `L` is, whose map is the
map of `L` read on the blocks.

This lemma is formalization-side: it is the step of blocking a protocol layer by layer. -/
theorem exists_coarsen (f : S → S') (cover : Γ.Cell → Γ'.Cell) (L : Layer Γ KrausGate X Y)
    (hcover : ∀ b ∈ L.cells, (Γ.cell b).image f ⊆ Γ'.cell (cover b))
    (hL : ∀ b₁ ∈ L.cells, ∀ b₂ ∈ L.cells, cover b₁ ≠ cover b₂ →
      Disjoint (Γ'.cell (cover b₁)) (Γ'.cell (cover b₂))) :
    ∃ L' : Layer Γ' KrausGate (blockSystem f X) (blockSystem f Y),
      L'.cells = L.cells.image cover ∧
      (L.Forall KrausGate.ev KrausFamily.IsTP → L'.Forall KrausGate.ev KrausFamily.IsTP) ∧
      (Circuit.ofLayer L').map KrausGate.ev ∘ₗ
          (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f X).symm).toLinearMap =
        (reindexAlgEquiv ℂ ℂ (blockConfigEquiv f Y).symm).toLinearMap ∘ₗ
          (Circuit.ofLayer L).map KrausGate.ev := by
  refine ⟨coarsen f cover L hcover hL, rfl, fun hTP ↦ ?_, ?_⟩
  · have hβ (β' : (skeleton cover L hL).Block) :
        (coarseFamily f cover L hcover hL β').IsTP := by
      refine KrausFamily.IsTP.reindex (KrausFamily.IsTP.prodFamily fun β ↦ ?_) _ _
      exact L.blockEffect_eq_one KrausGate.ev hTP β.1
    exact ⟨fun c ↦ hβ (.inl c), fun s ↦ (hβ (.inr s)).reindex _ _⟩
  · refine LinearMap.ext fun ρ ↦ ?_
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, coe_reindexAlgEquiv,
      reindex_apply, Equiv.symm_symm, Circuit.map_ofLayer]
    exact map_submatrix_of_op (coarsenIndexEquiv f cover L hcover hL) _ _
      (kraus_coarsen f cover L hcover hL) ρ

end Layer

end QuantumCircuit
