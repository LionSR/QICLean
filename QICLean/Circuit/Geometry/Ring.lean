/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Geometry.Basic
import QICLean.ManyBody.Sites.Lattice.Ring

/-!
# The ring geometry

The ring of `N` sites has one cell `{k, k + 1}` of cost `1` for each site `k`, indices modulo
`N`. Its neighbourhood of a region is the ring ball of radius `1`, so its `r`-fold neighbourhood
is the ring ball of radius `r`.

Adapted from TNLean at commit `e41c3b6371c44bcecb7004d78ff5ec11ae2282f3` (Apache-2.0):
`ringBond`, `ringBond_subset_neighbourhood` and `bondNeighbourhood_ringBond` of
`TNLean/Circuit/Geometry.lean`. Changes: the bonds are the cells of a `Geometry`, written with
`finRotate` so that the ring is defined for every `N`; `bondNeighbourhood_ringBond` is
`neighbourhood_ring`.

## Main definitions

* `QuantumCircuit.Geometry.ring` — the cells `{k, k + 1}` of the ring, of cost `1`.

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

end Geometry

end QuantumCircuit
