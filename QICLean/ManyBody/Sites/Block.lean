/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Partition
import QICLean.ManyBody.Sites.Placement

/-!
# Blocking sites

A map of sites `f : V → V'` groups the sites of `V` into blocks: the block `b : V'` is the
preimage `blockPreimage f {b}`. A system `X` on `V` is then a system `blockSystem f X` on `V'`,
whose basis at `b` is the configurations of the block. The configurations of the two systems are
the same (`blockConfigEquiv`, the partition of the sites into the blocks, `complPartitionEquiv`),
and so are the configurations of a region `D'` of blocks and of its preimage
(`blockRegionConfigEquiv`); a block that consists of one site `v` has the configurations of `v`
(`blockFiberEquiv`). Placement commutes with blocking
(`reindex_blockConfigEquiv_place`), and a product operator of the sites is the product over the
blocks of the product operators of the blocks (`reindex_blockConfigEquiv_symm_piKronecker`).

## Main definitions

* `ManyBody.blockPreimage` — the sites of a region of blocks.
* `ManyBody.blockSystem` — the blocked system.
* `ManyBody.blockConfigEquiv`, `ManyBody.blockRegionConfigEquiv` — its configurations.
* `ManyBody.blockFiberEquiv` — the configurations of a block that consists of one site.

## Main results

* `ManyBody.reindex_blockConfigEquiv_place` — an operator placed on a region of blocks is the
  operator placed on its preimage.
* `ManyBody.reindex_blockConfigEquiv_symm_piKronecker` — a product operator on the sites is, on the
  blocks, the product over the blocks of the product operators of the blocks.
* `ManyBody.reindex_blockConfigEquiv_one_kronecker` — blocking commutes with a spectator factor
  (`ManyBody.blockConfigProdEquiv`).
-/

open Matrix
open scoped Kronecker

namespace ManyBody

variable {V V' : Type} [Fintype V] [DecidableEq V'] (f : V → V')

/-- The preimage of a region of blocks: the sites whose block lies in the region. -/
abbrev blockPreimage (D' : Finset V') : Finset V :=
  Finset.univ.filter (f · ∈ D')

/-- A site lies in the block `b` exactly when its block is `b`. -/
theorem mem_blockPreimage_singleton {v : V} {b : V'} :
    v ∈ blockPreimage f {b} ↔ f v = b := by
  simp

/-- The blocks partition the sites. -/
private theorem isComplPartition_blockPreimage :
    IsComplPartition (∅ : Finset V) (fun b ↦ blockPreimage f {b}) (fun v ↦ f v.1) where
  disjoint _ := Finset.disjoint_empty_right _
  mem _ := (mem_blockPreimage_singleton f).mpr rfl
  eq_of_mem _ _ h := (mem_blockPreimage_singleton f).mp h

/-- The system on `V'` whose basis at `b` is the configurations of the block `b`. -/
abbrev blockSystem (X : V → Type) : V' → Type :=
  fun b ↦ RegionConfig X (blockPreimage f {b})

/-- The configurations of the blocked system are those of the system: the partition of the
sites into the blocks of `f` (`complPartitionEquiv`). -/
def blockConfigEquiv (X : V → Type) : Config (blockSystem f X) ≃ Config X :=
  (complPartitionEquiv (isComplPartition_blockPreimage f)).symm.trans (complEmptyEquiv X)

@[simp] theorem blockConfigEquiv_apply {X : V → Type} (z : Config (blockSystem f X)) (v : V) :
    blockConfigEquiv f X z v = z (f v) ⟨v, by simp⟩ :=
  rfl

@[simp] theorem blockConfigEquiv_symm_apply {X : V → Type} (σ : Config X) (b : V')
    (v : {v // v ∈ blockPreimage f {b}}) : (blockConfigEquiv f X).symm σ b v = σ v :=
  rfl

/-- The configurations of a region `D'` of the blocked system are those of its preimage. -/
def blockRegionConfigEquiv (X : V → Type) (D' : Finset V') :
    RegionConfig (blockSystem f X) D' ≃ RegionConfig X (blockPreimage f D') where
  toFun z v := z ⟨f v, (Finset.mem_filter.mp v.2).2⟩ ⟨v, by simp⟩
  invFun a b v := a ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ((mem_blockPreimage_singleton f).mp v.2).symm ▸ b.2⟩⟩
  left_inv z := by
    funext ⟨b, hb⟩ ⟨v, hv⟩
    have key : ∀ b' (_ : b' = b) (hb' : b' ∈ D') (hv' : v ∈ blockPreimage f {b'}),
        z ⟨b', hb'⟩ ⟨v, hv'⟩ = z ⟨b, hb⟩ ⟨v, hv⟩ := by
      rintro _ rfl _ _; rfl
    exact key _ ((mem_blockPreimage_singleton f).mp hv) _ _
  right_inv _ := rfl

/-! ### A block of one site -/

section Fiber

variable {b : V'} {v : V} (hf : ∀ u, f u = b ↔ u = v)
include hf

/-- The site `v` lies in the block `b` that consists of `v` alone. -/
theorem mem_blockPreimage_of_fiber : v ∈ blockPreimage f {b} :=
  (mem_blockPreimage_singleton f).mpr ((hf v).mpr rfl)

/-- The only site of the block `b` that consists of `v` alone is `v`. -/
theorem eq_of_mem_blockPreimage_of_fiber {u : V} (hu : u ∈ blockPreimage f {b}) : u = v :=
  (hf u).mp ((mem_blockPreimage_singleton f).mp hu)

/-- The configurations of a block that consists of the single site `v` are the configurations
of `v`: a configuration of the block is read by its value at `v`. -/
def blockFiberEquiv (X : V → Type) : blockSystem f X b ≃ X v where
  toFun z := z ⟨v, mem_blockPreimage_of_fiber f hf⟩
  invFun x u := cast (congrArg X (eq_of_mem_blockPreimage_of_fiber f hf u.2).symm) x
  left_inv z := funext fun ⟨u, hu⟩ ↦ by
    obtain rfl := eq_of_mem_blockPreimage_of_fiber f hf hu
    rfl
  right_inv _ := rfl

/-- The identification of the configurations of a block of one site is the value at the
site. -/
@[simp] theorem blockFiberEquiv_apply (X : V → Type) (z : blockSystem f X b) :
    blockFiberEquiv f hf X z = z ⟨v, mem_blockPreimage_of_fiber f hf⟩ :=
  rfl

end Fiber

variable [DecidableEq V] [Fintype V']

/-- Blocking commutes with placement: an operator placed on the region `D'` of the blocked
system is, read on the system, the same operator placed on the preimage of `D'`. -/
theorem reindex_blockConfigEquiv_place {X : V → Type} [∀ v, DecidableEq (X v)]
    (D' : Finset V')
    (K : Matrix (RegionConfig (blockSystem f X) D') (RegionConfig (blockSystem f X) D') ℂ) :
    reindex (blockConfigEquiv f X) (blockConfigEquiv f X) (place D' K) =
      place (blockPreimage f D')
        (reindex (blockRegionConfigEquiv f X D') (blockRegionConfigEquiv f X D') K) := by
  ext σ τ
  rw [reindex_apply, submatrix_apply, place_apply, place_apply]
  refine if_congr ⟨fun h v hv ↦ ?_, fun h b hb ↦ funext fun v ↦ h v.1 ?_⟩ rfl rfl
  · exact congrFun (h (f v) (by simpa using hv)) ⟨v, by simp⟩
  · simpa [(mem_blockPreimage_singleton f).mp v.2] using hb

omit [DecidableEq V] in
/-- Blocking a product operator gives the product over the blocks of the product operators of
the blocks: `⊗_v m_v` read on the blocked system is `⊗_b ⊗_{f v = b} m_v`. -/
theorem reindex_blockConfigEquiv_symm_piKronecker {X Y : V → Type}
    (m : (v : V) → Matrix (X v) (Y v) ℂ) :
    reindex (blockConfigEquiv f X).symm (blockConfigEquiv f Y).symm (piKronecker m) =
      piKronecker fun b ↦ piKronecker fun v : {v // v ∈ blockPreimage f {b}} ↦ m v := by
  ext z w
  rw [reindex_apply, submatrix_apply, piKronecker_apply, piKronecker_apply, Equiv.symm_symm,
    Equiv.symm_symm]
  simp only [piKronecker_apply]
  rw [← Fintype.prod_sigma (fun p : (Σ b : V', {v // v ∈ blockPreimage f {b}}) ↦
    m p.2 (z p.1 p.2) (w p.1 p.2))]
  refine Fintype.prod_equiv
    ⟨fun v ↦ (⟨f v, v, by simp⟩ : Σ b : V', {v // v ∈ blockPreimage f {b}}), fun p ↦ p.2.1,
      fun _ ↦ rfl, fun ⟨b, v, hv⟩ ↦ ?_⟩ _ _ fun _ ↦ rfl
  obtain rfl : f v = b := by simpa using hv
  rfl

/-- The configurations of a product system `W × X` on the blocks are the pairs of configurations
of the two blocked systems. -/
def blockConfigProdEquiv (W X : V → Type) :
    Config (blockSystem f fun v ↦ W v × X v) ≃
      Config (blockSystem f W) × Config (blockSystem f X) :=
  (blockConfigEquiv f _).trans ((Equiv.arrowProdEquivProdArrow V W X).trans
    ((blockConfigEquiv f W).symm.prodCongr (blockConfigEquiv f X).symm))

omit [DecidableEq V] in
/-- Blocking commutes with a spectator factor: `1 ⊗ M` on the product systems, read on the
blocks, is `1 ⊗` the matrix `M` read on the blocks. -/
theorem reindex_blockConfigEquiv_one_kronecker {W X Y : V → Type} [∀ v, DecidableEq (W v)]
    (M : Matrix (Config Y) (Config X) ℂ) :
    reindex (blockConfigEquiv f fun v ↦ W v × Y v).symm
        (blockConfigEquiv f fun v ↦ W v × X v).symm
        (reindex (Equiv.arrowProdEquivProdArrow V W Y).symm
          (Equiv.arrowProdEquivProdArrow V W X).symm
          ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ M)) =
      reindex (blockConfigProdEquiv f W Y).symm (blockConfigProdEquiv f W X).symm
        ((1 : Matrix (Config (blockSystem f W)) (Config (blockSystem f W)) ℂ) ⊗ₖ
          reindex (blockConfigEquiv f Y).symm (blockConfigEquiv f X).symm M) := by
  ext y x
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, blockConfigProdEquiv,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, kroneckerMap_apply,
    one_apply, Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq]

end ManyBody
