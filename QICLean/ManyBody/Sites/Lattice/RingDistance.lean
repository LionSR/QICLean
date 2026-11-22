/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Ring

/-!
# The distance between two sets of sites of the ring

For nonempty sets `X` and `Y` of sites of the ring of `N` sites, `ringSupportDistance X Y` is
the least `r` such that some site of `Y` is `x + m` for a site `x` of `X` and an integer
displacement `|m| ≤ r`, indices modulo `N`. It is the least distance in the cycle graph from a
site of `X` to a site of `Y`: it is at most the cycle-graph distance of any two such sites, and
the two sets are separated by `r` in the cycle graph exactly when `r` is smaller than it.

Moved from TNLean, `TNLean/MPS/Preparation/FiniteRingLiebRobinson.lean` at commit `49b78ed821`
(Apache-2.0). Changes: namespace `ManyBody` in place of `MPSPreparation`; the walk estimate is
read from `ManyBody.mem_graphNeighborhood_cycleGraph`.

## Main definitions

* `ManyBody.ringSupportDistance` — the distance between two nonempty sets of sites of the ring.

## Main results

* `ManyBody.ringSupportDistance_le_edist` — it is at most the cycle-graph distance of any two
  sites of the sets.
* `ManyBody.isGraphSeparated_iff_lt_ringSupportDistance` — two sets are separated by `r` in the
  cycle graph exactly when `r` is smaller than their distance.
-/

namespace ManyBody

open Fin.CommRing

variable {N : ℕ} [NeZero N]

/-- Some site of `Y` is reached from a site of `X` by a displacement of absolute value at
most `r`. -/
private def Reaches (X Y : Set (Fin N)) (r : ℕ) : Prop :=
  ∃ x ∈ X, ∃ y ∈ Y, ∃ m : ℤ, |m| ≤ r ∧ y = x + (m : Fin N)

private theorem exists_reaches (X Y : Set (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty) :
    ∃ r, Reaches X Y r := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  refine ⟨(y - x).val, x, hx, y, hy, (y - x).val, by simp, ?_⟩
  simp only [Int.cast_natCast, Fin.cast_val_eq_self]
  ring

open Classical in
/-- **The distance between two sets of sites of the ring.** For nonempty sets `X` and `Y` it is
the least `r` such that some site of `Y` is `x + m` for a site `x` of `X` and an integer
displacement `|m| ≤ r`, indices modulo `N`. -/
noncomputable def ringSupportDistance (X Y : Set (Fin N))
    (hX : X.Nonempty) (hY : Y.Nonempty) : ℕ :=
  Nat.find (exists_reaches X Y hX hY)

private theorem reaches_ringSupportDistance (X Y : Set (Fin N))
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    Reaches X Y (ringSupportDistance X Y hX hY) := by
  classical
  exact Nat.find_spec (exists_reaches X Y hX hY)

/-- The distance between two sets of sites of the ring is at most the cycle-graph distance
between any site of the first and any site of the second. -/
theorem ringSupportDistance_le_edist (X Y : Set (Fin N))
    (hX : X.Nonempty) (hY : Y.Nonempty) {x y : Fin N} (hx : x ∈ X) (hy : y ∈ Y) :
    (ringSupportDistance X Y hX hY : ℕ∞) ≤ (SimpleGraph.cycleGraph N).edist x y := by
  classical
  by_cases htop : (SimpleGraph.cycleGraph N).edist x y = ⊤
  · simp [htop]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have hmem : y ∈ graphNeighborhood (SimpleGraph.cycleGraph N) {x} n :=
    mem_graphNeighborhood.mpr ⟨x, Finset.mem_singleton_self x, hn.ge⟩
  obtain ⟨x', hx', m, hm, heq⟩ := mem_graphNeighborhood_cycleGraph.mp hmem
  rw [Finset.mem_singleton.mp hx'] at heq
  rw [← hn]
  exact_mod_cast Nat.find_min' (exists_reaches X Y hX hY) ⟨x, hx, y, hy, m, hm, heq⟩

/-- **Separation and distance on the ring.** Two nonempty sets of sites are separated by `r` in
the cycle graph exactly when `r` is smaller than their distance. -/
theorem isGraphSeparated_iff_lt_ringSupportDistance
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty) (r : ℕ) :
    IsGraphSeparated (SimpleGraph.cycleGraph N) X Y r ↔
      r < ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY := by
  classical
  constructor
  · intro h
    by_contra hlt
    have hle := Nat.le_of_not_gt hlt
    obtain ⟨x, hx, y, hy, m, hm, heq⟩ :=
      reaches_ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY
    have hmem : y ∈ graphNeighborhood (SimpleGraph.cycleGraph N) {x}
        (ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) :=
      mem_graphNeighborhood_cycleGraph.mpr ⟨x, Finset.mem_singleton_self x, m, hm, heq⟩
    obtain ⟨x', hx', hxy⟩ := mem_graphNeighborhood.mp hmem
    rw [Finset.mem_singleton.mp hx'] at hxy
    exact (h x hx y hy).not_ge (hxy.trans (by exact_mod_cast hle))
  · intro hr x hx y hy
    exact lt_of_lt_of_le (by exact_mod_cast hr)
      (ringSupportDistance_le_edist (X : Set (Fin N)) (Y : Set (Fin N)) hX hY hx hy)

end ManyBody
