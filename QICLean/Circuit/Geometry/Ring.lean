/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Geometry.Block
import QICLean.ManyBody.Sites.Lattice.Ring

/-!
# The ring geometry

The ring of `N` sites has one cell `{k, k + 1}` of cost `1` for each site `k`, indices modulo
`N`. Its neighbourhood of a region is the ring ball of radius `1`, so its `r`-fold neighbourhood
is the ring ball of radius `r`. Grouping the ring of `M * k` sites into `M` blocks of `k`
consecutive sites is a blocking of geometries into the ring of `M` blocks, coloured by the parity
of the cells with a third colour for the closing cell of an odd ring.

Adapted from TNLean at commit `e41c3b6371c44bcecb7004d78ff5ec11ae2282f3` (Apache-2.0):
`ringBond`, `ringBond_subset_neighbourhood` and `bondNeighbourhood_ringBond` of
`TNLean/Circuit/Geometry.lean`. Changes: the bonds are the cells of a `Geometry`, written with
`finRotate` so that the ring is defined for every `N`; `bondNeighbourhood_ringBond` is
`neighbourhood_ring`.

## Main definitions

* `QuantumCircuit.Geometry.ring` — the cells `{k, k + 1}` of the ring, of cost `1`.
* `QuantumCircuit.Geometry.ringBlocking` — the blocking of the ring of `M * k` sites into the
  ring of `M` blocks of `k` consecutive sites, with two colours for `M` even and three for `M`
  odd.

## Main results

* `QuantumCircuit.Geometry.iterate_neighbourhood_ring` — the `r`-fold neighbourhood of the ring
  is the ring ball of radius `r`.
-/

namespace QuantumCircuit

open ManyBody Fin.CommRing

namespace Geometry

/-- The ring of `N` sites: one cell `{k, k + 1}` of cost `1` for each site `k`, indices modulo
`N`. For `N = 1` the cell is `{0}`, and for `N = 2` both cells are `{0, 1}`. -/
abbrev ring (N : ℕ) : Geometry (Fin N) where
  Cell := Fin N
  cell k := {k, finRotate N k}
  cost _ := 1

/-- Every cell of the ring has positive cost. -/
theorem ring_cost_pos {N : ℕ} (b : (ring N).Cell) : 0 < (ring N).cost b :=
  Nat.one_pos

variable {N : ℕ} [NeZero N]

theorem ring_cell (k : Fin N) : (ring N).cell k = {k, k + 1} := by
  change ({k, finRotate N k} : Finset (Fin N)) = _
  rw [finRotate_apply]

/-- The neighbourhood of a region on the ring is its ring ball of radius `1`. -/
theorem neighbourhood_ring (X : Finset (Fin N)) : (ring N).neighbourhood X = ringBall X 1 := by
  have hcell (k j : Fin N) : j ∈ (ring N).cell k ↔ j = k ∨ j = k + 1 := by
    rw [ring_cell, Finset.mem_insert, Finset.mem_singleton]
  refine subset_antisymm (Finset.union_subset (subset_ringBall X 1) ?_) fun j hj ↦ ?_
  · simp only [Finset.biUnion_subset_iff_forall_subset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rintro k ⟨i, hi⟩
    rw [Finset.mem_inter, hcell] at hi
    intro j hj
    rw [hcell] at hj
    obtain ⟨hik, hiX⟩ := hi
    rcases hik with hik | hik <;> rcases hj with hj | hj <;> rw [hj] <;> rw [hik] at hiX
    · exact subset_ringBall X 1 hiX
    · exact mem_ringBall.mpr ⟨k, hiX, 1, by simp, by push_cast; ring⟩
    · exact mem_ringBall.mpr ⟨k + 1, hiX, -1, by simp, by push_cast; ring⟩
    · exact subset_ringBall X 1 hiX
  · obtain ⟨i, hi, m, hm, rfl⟩ := mem_ringBall.mp hj
    have hm' := abs_le.mp hm
    push_cast at hm'
    have hmem (k : Fin N) (hk : i ∈ (ring N).cell k) {j : Fin N} (hj : j ∈ (ring N).cell k) :
        j ∈ (ring N).neighbourhood X :=
      Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, i, Finset.mem_inter.mpr ⟨hk, hi⟩⟩, hj⟩)
    obtain rfl | rfl | rfl : m = -1 ∨ m = 0 ∨ m = 1 := by omega
    · exact hmem (i + ((-1 : ℤ) : Fin N)) ((hcell _ _).mpr (Or.inr (by push_cast; ring)))
        ((hcell _ _).mpr (Or.inl rfl))
    · simpa using (ring N).subset_neighbourhood X hi
    · exact hmem i ((hcell _ _).mpr (Or.inl rfl)) ((hcell _ _).mpr (Or.inr (by push_cast; ring)))

/-- The `r`-fold neighbourhood of a region on the ring is its ring ball of radius `r`. -/
theorem iterate_neighbourhood_ring (X : Finset (Fin N)) (r : ℕ) :
    (ring N).neighbourhood^[r] X = ringBall X r := by
  induction r with
  | zero => exact (ringBall_zero X).symm
  | succ r ih => rw [Function.iterate_succ_apply', ih, neighbourhood_ring, ← ringBall_succ]

/-! ### Blocking the ring -/

/-- The block of the successor of a site is its block or the next block. -/
private theorem div_succ_mod {M k p : ℕ} (hp : p < M * k) :
    (p + 1) % (M * k) / k = p / k ∨ (p + 1) % (M * k) / k = (p / k + 1) % M := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hp
  by_cases h : p + 1 = M * k
  · right
    have hM : 0 < M := Nat.pos_of_ne_zero fun h' ↦ by simp [h'] at hp
    have hdiv : p / k = M - 1 := Nat.div_eq_of_lt_le
      (by rw [Nat.sub_mul, one_mul]; omega) (by rw [Nat.sub_add_cancel hM]; omega)
    rw [h, Nat.mod_self, Nat.zero_div, hdiv, Nat.sub_add_cancel hM, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (by omega), Nat.succ_div]
    split_ifs with hd
    · right
      refine (Nat.mod_eq_of_lt ?_).symm
      have := (Nat.div_lt_iff_lt_mul hk).mpr (show p + 1 < M * k by omega)
      simpa only [Nat.succ_div, hd, ↓reduceIte] using this
    · left
      rfl

/-- **Blocking the ring.** The ring of `M * k` sites is blocked into the ring of `M` blocks of
`k` consecutive sites, the site `p` lying in the block `⌊p / k⌋`: the cell `{p, p + 1}` is
covered by the cell `{⌊p / k⌋, ⌊p / k⌋ + 1}`. The cells `{j, j + 1}` of the blocked ring are
coloured alternately by the parity of `j`, the closing cell `{M - 1, 0}` of an odd ring having a
third colour, so that two colours suffice for `M` even and three for `M` odd. A protocol of depth
`T` on the ring of sites is therefore a protocol of depth `2T` or `3T` on the ring of blocks.

This blocking is formalization-side; the source groups blocks of `q` neighbouring sites
(arXiv:2103.13367v3, `main.tex`, line 287). -/
def ringBlocking (M k : ℕ) [NeZero M] :
    (ring (M * k)).Blocking (ring M) Fin.divNat (if M % 2 = 0 then 2 else 3) where
  cover := Fin.divNat
  image_subset p := by
    have : NeZero (M * k) := ⟨fun h ↦ (Fin.pos p).ne' h⟩
    rw [ring_cell, ring_cell, Finset.image_insert, Finset.image_singleton]
    refine Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_self _ _,
      Finset.singleton_subset_iff.mpr ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff]
    simpa [Fin.val_add, Fin.coe_divNat] using div_succ_mod p.isLt
  colour j := ⟨if j.val + 1 = M ∧ M % 2 = 1 then 2 else j.val % 2, by split_ifs <;> omega⟩
  disjoint c₁ c₂ hc hne := by
    have hmod (a : ℕ) (ha : a < M) : (a + 1 % M) % M = if a + 1 = M then 0 else a + 1 := by
      rcases Nat.lt_or_ge 1 M with hM | hM
      · rw [Nat.mod_eq_of_lt hM]
        split_ifs with h
        · rw [h, Nat.mod_self]
        · exact Nat.mod_eq_of_lt (by omega)
      · obtain rfl : M = 1 := by omega
        obtain rfl : a = 0 := by omega
        rfl
    change Fin M at c₁ c₂
    rw [ring_cell, ring_cell]
    obtain ⟨a, h₁⟩ := c₁
    obtain ⟨b, h₂⟩ := c₂
    have hne' : a ≠ b := fun h ↦ hne (Fin.ext h)
    rw [Fin.ext_iff] at hc
    simp only [Finset.disjoint_insert_left, Finset.mem_insert, Finset.mem_singleton,
      Finset.disjoint_singleton_left, Fin.ext_iff, Fin.val_add, Fin.val_one'] at hc ⊢
    rw [hmod _ h₁, hmod _ h₂]
    clear hne hmod
    split_ifs at hc ⊢ <;> simp only [not_or, not_and_or, not_false_eq_true, and_true] at * <;>
      omega
  cost_pos := ring_cost_pos

end Geometry

end QuantumCircuit
