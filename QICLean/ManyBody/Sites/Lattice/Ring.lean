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
import QICLean.ManyBody.Sites.Block
import QICLean.ManyBody.Sites.Lattice.Chain
import QICLean.ManyBody.Sites.GraphBall

/-!
# Neighbourhoods and separation on the ring

The ring of `N` sites is `Fin N` with indices modulo `N`, and its graph is the cycle graph. The
neighbourhood of radius `r` of a set of sites `X` in the cycle graph,
`ManyBody.graphNeighborhood (cycleGraph N) X r`, is the set of sites `x + m` with `x ∈ X` and
`|m| ≤ r` (`ManyBody.mem_graphNeighborhood_cycleGraph`), and two sets are separated by `s`,
`ManyBody.IsGraphSeparated (cycleGraph N) X Y s`, when every site of the second lies outside
that set for `r = s`. The neighbourhoods and the separation are those of the cycle graph, so
their general properties (`ManyBody.graphNeighborhood_succ`,
`ManyBody.IsGraphSeparated.disjoint_graphNeighborhood`) are stated once for every graph; this
file proves the arithmetic description and the statements particular to the ring. Grouping the
ring of `M * k` sites into the `M` blocks of `k` consecutive sites rescales distances by `k`: the
sites of the blocks within distance `r` of a set of blocks lie within distance `k * r` of its
sites.

Adapted from TNLean at commit `e41c3b6371c44bcecb7004d78ff5ec11ae2282f3` (Apache-2.0):
`neighbourhood`, `IsSeparatedBy` and their lemmas from `TNLean/Circuit/Geometry.lean`, and
`TNLean/Circuit/RingSeparation.lean`. Changes: namespace `ManyBody` in place of
`QuantumCircuit`; the neighbourhood and the separation are those of the cycle graph, in place of
`neighbourhood` and `IsSeparatedBy` defined by cyclic arithmetic, which is now their
characterization. `preimage_graphNeighborhood_cycleGraph_subset` is
`preimage_siteBlock_neighbourhood_subset` of `TNLean/Circuit/Channel/SiteBlocking.lean` at commit
`0c76bc5a1a9df19136f61b908497542e5db406da`, with the block of a site written `Fin.divNat`.

## Main definitions

* `ManyBody.ringWindow` — the window of `k` consecutive sites starting at a site.

## Main results

* `ManyBody.mem_graphNeighborhood_cycleGraph` — the neighbourhoods of the cycle graph by cyclic
  arithmetic.
* `ManyBody.isGraphSeparated_cycleGraph_of_val_bounds` — sets in two intervals with cyclic gaps
  at least `s` are separated by `s`.
* `ManyBody.exists_isGraphSeparated_cycleGraph_singletons_notMem` — on more than `4T + 4`
  sites, two sites separated by `2T` and a third outside both neighbourhoods of radius `T`.
* `ManyBody.preimage_graphNeighborhood_cycleGraph_subset` — blocking rescales ring distances by
  the block size.
* `ManyBody.ringWindow_trans_finRotate` — the rotation of the ring moves each window of
  consecutive sites to the next one.
* `ManyBody.chainWindow_trans_ringWindow` — consecutive sites inside a window of the ring form a
  window of the ring.
-/

namespace ManyBody

open Fin.CommRing

variable {N : ℕ} [NeZero N]

variable {X Y : Finset (Fin N)}

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

/-- A site and its successor are at distance at most one in the cycle graph. -/
private theorem edist_add_one_le (x : Fin N) : (SimpleGraph.cycleGraph N).edist x (x + 1) ≤ 1 := by
  by_cases hN : N = 1
  · subst hN
    simp
  · refine (SimpleGraph.edist_eq_one_iff_adj.mpr (SimpleGraph.cycleGraph_adj'.mpr
      (Or.inr ?_))).le
    rw [add_sub_cancel_left, Fin.val_one']
    exact Nat.mod_eq_of_lt (by have := Nat.pos_of_neZero N; omega)

/-- A site moved by `n` is within distance `n` in the cycle graph. -/
private theorem edist_add_natCast_le (x : Fin N) (n : ℕ) :
    (SimpleGraph.cycleGraph N).edist x (x + (n : Fin N)) ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (SimpleGraph.cycleGraph N).edist x (x + ((n + 1 : ℕ) : Fin N))
        ≤ (SimpleGraph.cycleGraph N).edist x (x + (n : Fin N)) +
          (SimpleGraph.cycleGraph N).edist (x + (n : Fin N)) (x + (n : Fin N) + 1) := by
          rw [Nat.cast_succ, ← add_assoc]
          exact SimpleGraph.edist_triangle
      _ ≤ n + 1 := add_le_add ih (edist_add_one_le _)
      _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-- A site moved by `m` is within distance `|m|` in the cycle graph. -/
private theorem edist_add_intCast_le (x : Fin N) (m : ℤ) :
    (SimpleGraph.cycleGraph N).edist x (x + (m : Fin N)) ≤ m.natAbs := by
  rcases Int.natAbs_eq m with hm | hm
  · rw [hm, Int.cast_natCast, Int.natAbs_natCast]
    exact edist_add_natCast_le x _
  · rw [hm, Int.cast_neg, Int.cast_natCast, Int.natAbs_neg, Int.natAbs_natCast,
      SimpleGraph.edist_comm]
    simpa using edist_add_natCast_le (x + -(m.natAbs : Fin N)) m.natAbs

/-- **The neighbourhoods of the ring.** A site lies in the neighbourhood of radius `r` of `X`
in the cycle graph exactly when it is of the form `x + m` with `x ∈ X` and `|m| ≤ r`, indices
modulo `N`. -/
theorem mem_graphNeighborhood_cycleGraph {r : ℕ} {j : Fin N} :
    j ∈ graphNeighborhood (SimpleGraph.cycleGraph N) X r ↔
      ∃ x ∈ X, ∃ m : ℤ, |m| ≤ r ∧ j = x + (m : Fin N) := by
  constructor
  · intro hj
    obtain ⟨x, hx, p, hp⟩ := mem_graphNeighborhood_iff_exists_walk.mp hj
    obtain ⟨m, hm, rfl⟩ := exists_eq_add_of_walk p
    exact ⟨x, hx, m, hm.trans (by exact_mod_cast hp), rfl⟩
  · rintro ⟨x, hx, m, hm, rfl⟩
    refine mem_graphNeighborhood.mpr ⟨x, hx, (edist_add_intCast_le x m).trans ?_⟩
    have : m.natAbs ≤ r := by
      have := abs_le.mp hm
      omega
    exact_mod_cast this

/-- Rotating the ring rotates every neighbourhood by the same amount. -/
theorem graphNeighborhood_cycleGraph_image_finRotate (X : Finset (Fin N)) (r : ℕ) :
    (graphNeighborhood (SimpleGraph.cycleGraph N) X r).image (finRotate N) =
      graphNeighborhood (SimpleGraph.cycleGraph N) (X.image (finRotate N)) r := by
  ext j
  simp only [Finset.mem_image, mem_graphNeighborhood_cycleGraph]
  constructor
  · rintro ⟨y, ⟨x, hx, m, hm, rfl⟩, rfl⟩
    refine ⟨finRotate N x, ⟨x, hx, rfl⟩, m, hm, ?_⟩
    simp only [finRotate_apply]
    ring
  · rintro ⟨_, ⟨x, hx, rfl⟩, m, hm, rfl⟩
    refine ⟨x + (m : Fin N), ⟨x, hx, m, hm, rfl⟩, ?_⟩
    simp only [finRotate_apply]
    ring

/-- Sets lying in two intervals are separated by `s` in the cycle graph when both cyclic gaps
are at least `s`. -/
theorem isGraphSeparated_cycleGraph_of_val_bounds {a w b w' s : ℕ}
    (hX : ∀ x ∈ X, a ≤ x.val ∧ x.val < a + w) (hY : ∀ y ∈ Y, b ≤ y.val ∧ y.val < b + w')
    (hab : a + w + s ≤ b) (hba : b + w' + s ≤ a + N) :
    IsGraphSeparated (SimpleGraph.cycleGraph N) X Y s := by
  intro x hx y hy
  refine lt_of_not_ge fun hle ↦ ?_
  obtain ⟨x', hx', m, hm, heq⟩ := mem_graphNeighborhood_cycleGraph.mp
    (mem_graphNeighborhood.mpr ⟨x, Finset.mem_singleton_self x, hle⟩)
  rw [Finset.mem_singleton.mp hx'] at heq
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

/-- On more than `4T + 4` sites there are two sites separated by `2T` in the cycle graph and a
third outside both of their neighbourhoods of radius `T`. -/
theorem exists_isGraphSeparated_cycleGraph_singletons_notMem {T : ℕ} (hN : 4 * T + 4 < N) :
    ∃ i j k : Fin N, IsGraphSeparated (SimpleGraph.cycleGraph N) {i} {j} (2 * T) ∧
      k ∉ graphNeighborhood (SimpleGraph.cycleGraph N) {i} T ∪
        graphNeighborhood (SimpleGraph.cycleGraph N) {j} T := by
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨2 * T + 2, by omega⟩
  let k : Fin N := ⟨T + 1, by omega⟩
  have hsep (x y : Fin N) (s : ℕ) (hxy : x.val + 1 + s ≤ y.val)
      (hyx : y.val + 1 + s ≤ x.val + N) :
      IsGraphSeparated (SimpleGraph.cycleGraph N) {x} {y} s :=
    isGraphSeparated_cycleGraph_of_val_bounds
      (fun z hz ↦ by rcases Finset.mem_singleton.mp hz with rfl; exact ⟨le_rfl, by omega⟩)
      (fun z hz ↦ by rcases Finset.mem_singleton.mp hz with rfl; exact ⟨le_rfl, by omega⟩)
      hxy hyx
  refine ⟨i, j, k, hsep i j (2 * T) (by dsimp [i, j]; omega) (by dsimp [i, j]; omega), ?_⟩
  have hik := hsep i k T (by dsimp [i, k]; omega) (by dsimp [i, k]; omega)
  have hkj := hsep k j T (by dsimp [k, j]; omega) (by dsimp [k, j]; omega)
  exact fun h ↦ (Finset.mem_union.mp h).elim (hik.notMem_graphNeighborhood (by simp))
    (hkj.symm.notMem_graphNeighborhood (by simp))

/-! ### Blocks of consecutive sites -/

section Block

variable {M k : ℕ} [NeZero M] [NeZero k]

/-- Moving a block by `m` moves each of its sites by `k * m`. -/
private theorem finProdFinEquiv_add_intCast (j : Fin M) (t : Fin k) (m : ℤ) :
    finProdFinEquiv (j + (m : Fin M), t) =
      finProdFinEquiv (j, t) + (((k : ℤ) * m : ℤ) : Fin (M * k)) := by
  have hM : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hk : (0 : ℤ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  apply Fin.ext
  rw [Fin.val_add, finProdFinEquiv_apply_val, finProdFinEquiv_apply_val, Fin.val_add,
    Fin.val_intCast, Fin.val_intCast]
  dsimp only
  zify
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity)),
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  have e1 : (k : ℤ) * ((j + m % M) % M) = (k * j + k * m) % (M * k) := by
    rw [← Int.mul_emod_mul_of_pos _ _ hk, mul_add, ← Int.mul_emod_mul_of_pos _ _ hk,
      Int.add_emod_emod, mul_comm (M : ℤ)]
  have ht : (t : ℤ) < k := by exact_mod_cast t.isLt
  have hlt : (t : ℤ) + k * ((j + m % M) % M) < M * k := by
    have : ((j : ℤ) + m % M) % M < M := Int.emod_lt_of_pos _ hM
    nlinarith
  have h0 : (0 : ℤ) ≤ t + k * ((j + m % M) % M) :=
    add_nonneg (by positivity) (mul_nonneg hk.le (Int.emod_nonneg _ hM.ne'))
  rw [← Int.emod_eq_of_lt h0 hlt, e1, Int.add_emod_emod, Int.add_emod_emod, add_assoc]

/-- **Rescaling distances by the blocking factor.** Group the ring of `M * k` sites into the `M`
blocks of `k` consecutive sites, the site `p` lying in the block `⌊p / k⌋`. The sites of the
blocks within ring distance `r` of the blocks `R` lie within ring distance `k * r` of the sites
of `R`.

Source: arXiv:2103.13367v3, `main.tex`, line 289 (locality on the blocked chain, read on the
unblocked chain). -/
theorem preimage_graphNeighborhood_cycleGraph_subset (R : Finset (Fin M)) (r : ℕ) :
    blockPreimage (Fin.divNat (n := k)) (graphNeighborhood (SimpleGraph.cycleGraph M) R r) ⊆
      graphNeighborhood (SimpleGraph.cycleGraph (M * k))
        (blockPreimage (Fin.divNat (n := k)) R) (k * r) := by
  have hdiv (j : Fin M) (t : Fin k) : (finProdFinEquiv (j, t)).divNat = j := by
    simpa only [finProdFinEquiv_symm_apply] using
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (j, t))
  intro i hi
  obtain ⟨⟨j', t⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨j, hj, m, hm, hij⟩ := mem_graphNeighborhood_cycleGraph.mp (Finset.mem_filter.mp hi).2
  rw [hdiv] at hij
  subst hij
  refine mem_graphNeighborhood_cycleGraph.mpr ⟨finProdFinEquiv (j, t), ?_, (k : ℤ) * m, ?_,
    finProdFinEquiv_add_intCast j t m⟩
  · simpa [hdiv] using hj
  · rw [abs_mul, Nat.abs_cast]
    push_cast
    exact mul_le_mul_of_nonneg_left hm (by positivity)

end Block

/-! ### Windows of consecutive sites -/

section Window

variable {k : ℕ}

/-- The window of `k ≤ N` consecutive sites starting at the site `i`: the injection `j ↦ i + j`
of `Fin k` into the ring, indices modulo `N`. -/
def ringWindow (hk : k ≤ N) (i : Fin N) : Fin k ↪ Fin N :=
  ⟨fun j ↦ i + Fin.castLE hk j, fun _ _ h ↦ Fin.castLE_injective hk (add_left_cancel h)⟩

omit [NeZero N] in
@[simp]
theorem ringWindow_apply (hk : k ≤ N) (i : Fin N) (j : Fin k) :
    ringWindow hk i j = i + Fin.castLE hk j :=
  rfl

/-- The window of two sites starting at `i` is the bond `{i, i + 1}`. -/
theorem map_ringWindow_two (hk : 2 ≤ N) (i : Fin N) :
    Finset.univ.map (ringWindow hk i) = {i, i + 1} := by
  have h0 : (Fin.castLE hk 0 : Fin N) = 0 := Fin.ext (by simp)
  have h1 : (Fin.castLE hk 1 : Fin N) = 1 := Fin.ext (by simp [Nat.mod_eq_of_lt hk])
  ext j
  simp [Fin.exists_fin_two, h0, h1, eq_comm]

/-- **Rotating a window.** The rotation `j ↦ j + 1` of the ring carries the window starting at
`i` to the window starting at `i + 1`. -/
theorem ringWindow_trans_finRotate (hk : k ≤ N) (i : Fin N) :
    (ringWindow hk i).trans (finRotate N).toEmbedding = ringWindow hk (i + 1) := by
  ext j
  simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, ringWindow_apply,
    finRotate_apply]
  rw [add_right_comm]

/-- **A window of a window.** Inside the window of `m` consecutive sites of the ring starting at
`i`, the `k` consecutive sites starting at the position `b`, with `b + k ≤ m`, are the window of
the ring starting at `i + b`. -/
theorem chainWindow_trans_ringWindow {m : ℕ} (b : ℕ) (hb : b + k ≤ m) (hm : m ≤ N)
    (i : Fin N) :
    (chainWindow b hb).trans (ringWindow hm i) =
      ringWindow ((Nat.le_add_left k b).trans hb |>.trans hm) (i + (b : Fin N)) := by
  ext j
  simp only [Function.Embedding.trans_apply, ringWindow_apply, Fin.val_add, Fin.val_castLE,
    val_chainWindow, Fin.val_natCast, Nat.mod_add_mod, Nat.add_mod_mod]
  rw [add_assoc]

end Window

end ManyBody
