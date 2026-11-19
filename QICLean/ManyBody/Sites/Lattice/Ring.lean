/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.Interval
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Balls and separation on the ring

The ring of `N` sites is `Fin N` with indices modulo `N`. The ball of radius `r` about a set of
sites `X` is the set of sites `x + m` with `x ∈ X` and `|m| ≤ r`; two sets are separated by `s`
when no site of the second is of the form `x + m` with `x` in the first and `|m| ≤ s`. Sets
separated by `2T` have disjoint balls of radius `T`, and sets separated by `s` are at distance
larger than `s` in the cycle graph.

Adapted from TNLean at commit `e41c3b6371c44bcecb7004d78ff5ec11ae2282f3` (Apache-2.0):
`neighbourhood`, `IsSeparatedBy` and their lemmas from `TNLean/Circuit/Geometry.lean`, and
`TNLean/Circuit/RingSeparation.lean`. Changes: namespace `ManyBody` in place of
`QuantumCircuit`; `ringBall` in place of `neighbourhood` and `IsRingSeparated` in place of
`IsSeparatedBy`; `ringBall_succ` stated through the radius-`1` ball, `ringBall_zero` and
`IsRingSeparated.lt_edist` added.

## Main definitions

* `ManyBody.ringBall` — the sites within ring distance `r` of a set.
* `ManyBody.IsRingSeparated` — two sets at ring distance larger than `s`.

## Main results

* `ManyBody.ringBall_succ` — the ball of radius `r + 1` is the radius-`1` ball of the ball of
  radius `r`.
* `ManyBody.IsRingSeparated.disjoint_ringBall` — sets separated by `2T` have disjoint balls of
  radius `T`.
* `ManyBody.exists_isRingSeparated_singletons_notMem_ringBall` — on more than `4T + 4` sites,
  two sites separated by `2T` and a third outside both balls of radius `T`.
* `ManyBody.IsRingSeparated.lt_edist` — separated sets are far apart in the cycle graph.
-/

namespace ManyBody

open Fin.CommRing

variable {N : ℕ} [NeZero N]

/-- The sites within ring distance `r` of `X`: those of the form `x + m` with `x ∈ X` and
`|m| ≤ r`, indices modulo `N`. -/
def ringBall (X : Finset (Fin N)) (r : ℕ) : Finset (Fin N) :=
  X.biUnion fun x ↦ (Finset.Icc (-(r : ℤ)) r).image fun m : ℤ ↦ x + (m : Fin N)

variable {X Y : Finset (Fin N)}

theorem mem_ringBall {r : ℕ} {j : Fin N} :
    j ∈ ringBall X r ↔ ∃ x ∈ X, ∃ m : ℤ, |m| ≤ r ∧ j = x + (m : Fin N) := by
  simp only [ringBall, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc, abs_le]
  constructor <;> rintro ⟨x, hx, m, hm, e⟩ <;> exact ⟨x, hx, m, hm, e.symm⟩

theorem subset_ringBall (X : Finset (Fin N)) (r : ℕ) : X ⊆ ringBall X r :=
  fun x hx ↦ mem_ringBall.mpr ⟨x, hx, 0, by simp, by simp⟩

/-- Rotating the ring rotates every ball by the same amount. -/
theorem ringBall_image_finRotate (X : Finset (Fin N)) (r : ℕ) :
    (ringBall X r).image (finRotate N) = ringBall (X.image (finRotate N)) r := by
  ext j
  simp only [Finset.mem_image, mem_ringBall]
  constructor
  · rintro ⟨y, ⟨x, hx, m, hm, rfl⟩, rfl⟩
    refine ⟨finRotate N x, ⟨x, hx, rfl⟩, m, hm, ?_⟩
    simp only [finRotate_apply]
    ring
  · rintro ⟨_, ⟨x, hx, rfl⟩, m, hm, rfl⟩
    refine ⟨x + (m : Fin N), ⟨x, hx, m, hm, rfl⟩, ?_⟩
    simp only [finRotate_apply]
    ring

private theorem ringBall_ringBall_subset (X : Finset (Fin N)) (r s : ℕ) :
    ringBall (ringBall X r) s ⊆ ringBall X (r + s) := by
  intro k hk
  obtain ⟨j, hj, m', hm', rfl⟩ := mem_ringBall.mp hk
  obtain ⟨x, hx, m, hm, rfl⟩ := mem_ringBall.mp hj
  refine mem_ringBall.mpr ⟨x, hx, m + m', ?_, ?_⟩
  · push_cast
    exact (abs_add_le m m').trans (add_le_add hm hm')
  · push_cast
    ring

/-- The ball of radius `r + 1` is the radius-`1` ball of the ball of radius `r`. -/
theorem ringBall_succ (X : Finset (Fin N)) (r : ℕ) :
    ringBall X (r + 1) = ringBall (ringBall X r) 1 := by
  refine subset_antisymm ?_ (ringBall_ringBall_subset X r 1)
  intro j hj
  obtain ⟨x, hx, m, hm, rfl⟩ := mem_ringBall.mp hj
  have hm' := abs_le.mp hm
  push_cast at hm'
  obtain ⟨s, hs, hms⟩ : ∃ s : ℤ, |s| ≤ 1 ∧ |m - s| ≤ r := by
    rcases lt_trichotomy m 0 with h | h | h
    · exact ⟨-1, by simp, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    · exact ⟨0, by simp, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    · exact ⟨1, by simp, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  refine mem_ringBall.mpr ⟨x + ((m - s : ℤ) : Fin N),
    mem_ringBall.mpr ⟨x, hx, m - s, hms, rfl⟩, s, by exact_mod_cast hs, ?_⟩
  push_cast
  ring

theorem ringBall_zero (X : Finset (Fin N)) : ringBall X 0 = X := by
  refine subset_antisymm (fun j hj ↦ ?_) (subset_ringBall X 0)
  obtain ⟨x, hx, m, hm, rfl⟩ := mem_ringBall.mp hj
  rw [Nat.cast_zero, abs_nonpos_iff] at hm
  simpa [hm] using hx

/-- Two sets of sites are at ring distance larger than `s`: no site of `Y` is of the form
`x + m` with `x ∈ X` and `|m| ≤ s`. -/
def IsRingSeparated (X Y : Finset (Fin N)) (s : ℕ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ m : ℤ, |m| ≤ s → y ≠ x + (m : Fin N)

/-- Sets separated by `2T` have disjoint balls of radius `T`. -/
theorem IsRingSeparated.disjoint_ringBall {T : ℕ} (h : IsRingSeparated X Y (2 * T)) :
    Disjoint (ringBall X T) (ringBall Y T) := by
  rw [Finset.disjoint_left]
  intro j hjX hjY
  obtain ⟨x, hx, m, hm, rfl⟩ := mem_ringBall.mp hjX
  obtain ⟨y, hy, m', hm', hj⟩ := mem_ringBall.mp hjY
  refine h x hx y hy (m - m') ?_ ?_
  · push_cast
    exact (abs_sub _ _).trans (by linarith)
  · push_cast
    linear_combination -hj

/-- Sets lying in two intervals are separated by `s` when both cyclic gaps are at least `s`. -/
theorem isRingSeparated_of_val_bounds {a w b w' s : ℕ}
    (hX : ∀ x ∈ X, a ≤ x.val ∧ x.val < a + w) (hY : ∀ y ∈ Y, b ≤ y.val ∧ y.val < b + w')
    (hab : a + w + s ≤ b) (hba : b + w' + s ≤ a + N) : IsRingSeparated X Y s := by
  intro x hx y hy m hm heq
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have h0 : 0 ≤ m % (N : ℤ) := Int.emod_nonneg _ hN.ne'
  have hv := congrArg Fin.val heq
  rw [Fin.val_add, Fin.val_intCast] at hv
  have hz : (y.val : ℤ) = ((x.val : ℤ) + m % N) % N := by
    rw [hv, Int.natCast_emod, Nat.cast_add, Int.toNat_of_nonneg h0]
  have e1 := Int.emod_add_mul_ediv ((x.val : ℤ) + m % N) N
  have e2 := Int.emod_add_mul_ediv m N
  have hdvd : (N : ℤ) ∣ (y.val : ℤ) - x.val - m :=
    ⟨-(((x.val : ℤ) + m % N) / N) - m / N, by rw [hz]; linear_combination e1 + e2⟩
  obtain ⟨hxa, hxw⟩ := hX x hx
  obtain ⟨hyb, hyw⟩ := hY y hy
  obtain ⟨hm1, hm2⟩ := abs_le.mp hm
  have hpos : 0 ≤ (y.val : ℤ) - x.val - m := by omega
  have hlt : (y.val : ℤ) - x.val - m < N := by omega
  have := Int.eq_zero_of_dvd_of_nonneg_of_lt hpos hlt hdvd
  omega

/-- Separation on the ring is symmetric. -/
theorem IsRingSeparated.symm {s : ℕ} (h : IsRingSeparated X Y s) : IsRingSeparated Y X s := by
  intro y hy x hx m hm heq
  apply h x hx y hy (-m) (by simpa using hm)
  push_cast
  linear_combination -heq

/-- A site of `Y` lies outside the ball of radius `s` about a set `X` separated from `Y` by
`s`. -/
theorem IsRingSeparated.notMem_ringBall {s : ℕ} (h : IsRingSeparated X Y s) {y : Fin N}
    (hy : y ∈ Y) : y ∉ ringBall X s := by
  intro hmem
  obtain ⟨x, hx, m, hm, heq⟩ := mem_ringBall.mp hmem
  exact h x hx y hy m hm heq

/-- On more than `4T + 4` sites there are two sites separated by `2T` and a third outside both
of their balls of radius `T`. -/
theorem exists_isRingSeparated_singletons_notMem_ringBall {T : ℕ} (hN : 4 * T + 4 < N) :
    ∃ i j k : Fin N, IsRingSeparated {i} {j} (2 * T) ∧ k ∉ ringBall {i} T ∪ ringBall {j} T := by
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨2 * T + 2, by omega⟩
  let k : Fin N := ⟨T + 1, by omega⟩
  have hsep (x y : Fin N) (s : ℕ) (hxy : x.val + 1 + s ≤ y.val)
      (hyx : y.val + 1 + s ≤ x.val + N) : IsRingSeparated {x} {y} s :=
    isRingSeparated_of_val_bounds
      (fun z hz ↦ by rcases Finset.mem_singleton.mp hz with rfl; exact ⟨le_rfl, by omega⟩)
      (fun z hz ↦ by rcases Finset.mem_singleton.mp hz with rfl; exact ⟨le_rfl, by omega⟩)
      hxy hyx
  refine ⟨i, j, k, hsep i j (2 * T) (by dsimp [i, j]; omega) (by dsimp [i, j]; omega), ?_⟩
  have hik := hsep i k T (by dsimp [i, k]; omega) (by dsimp [i, k]; omega)
  have hkj := hsep k j T (by dsimp [k, j]; omega) (by dsimp [k, j]; omega)
  exact fun h ↦ (Finset.mem_union.mp h).elim (hik.notMem_ringBall (by simp))
    (hkj.symm.notMem_ringBall (by simp))

/-- The end of a walk of length `ℓ` in the cycle graph is its start moved by at most `ℓ`. -/
private theorem exists_eq_add_of_walk {x y : Fin N} (p : (SimpleGraph.cycleGraph N).Walk x y) :
    ∃ m : ℤ, |m| ≤ p.length ∧ y = x + (m : Fin N) := by
  induction p with
  | nil => exact ⟨0, by simp, by simp⟩
  | @cons u v w h p ih =>
    obtain ⟨m, hm, rfl⟩ := ih
    obtain ⟨m₁, hm₁, rfl⟩ : ∃ m₁ : ℤ, |m₁| ≤ 1 ∧ v = u + (m₁ : Fin N) := by
      rcases SimpleGraph.cycleGraph_adj'.mp h with h | h
      · refine ⟨-((u - v).val : ℤ), by simp [h], ?_⟩
        rw [Int.cast_neg, Int.cast_natCast, Fin.cast_val_eq_self]
        ring
      · refine ⟨((v - u).val : ℤ), by simp [h], ?_⟩
        rw [Int.cast_natCast, Fin.cast_val_eq_self]
        ring
    refine ⟨m₁ + m, ?_, ?_⟩
    · rw [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one, add_comm (p.length : ℤ)]
      exact (abs_add_le _ _).trans (add_le_add hm₁ hm)
    · push_cast
      ring

/-- Sets separated by `s` are at distance larger than `s` in the cycle graph. -/
theorem IsRingSeparated.lt_edist {s : ℕ} (h : IsRingSeparated X Y s) {x y : Fin N}
    (hx : x ∈ X) (hy : y ∈ Y) : (s : ℕ∞) < (SimpleGraph.cycleGraph N).edist x y := by
  refine lt_of_not_ge fun hle ↦ ?_
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top (ne_top_of_le_ne_top
    (ENat.natCast_ne_top s) hle)
  obtain ⟨m, hm, rfl⟩ := exists_eq_add_of_walk p
  rw [← hp, Nat.cast_le] at hle
  exact h x hx _ hy m (hm.trans (by exact_mod_cast hle)) rfl

end ManyBody
