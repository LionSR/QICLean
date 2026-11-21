/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Connected vertex sets of a graph of bounded degree

At most `Δ ^ (2 (n - 1))` connected vertex sets of size `n` contain a given vertex of a graph of
degree at most `Δ`: every such set is the vertex set of a closed walk of length `2 (n - 1)`
from the vertex, built by adding one vertex at a time through a detour out and back along an
edge. This is the count of lattice animals (Klarner, Canad. J. Math. 19 (1967) 851) used by
the cluster expansion of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1227–1254,
eq. `perc2`, in the form `N x ^ n` with `x = max 1 (Δ ^ 2)`.

Moved from TNLean, `TNLean/Lattice/ConnectedSetCount.lean` at commit `e113e005`, by way of
`QICLean/ManyBody/Dynamics/GraphGrowth.lean`; the statements involve no sites and now sit in
the namespace `SimpleGraph`.

## Main results

* `SimpleGraph.card_connected_induce_mem_le` — the connected sets of size `n` through a vertex.
* `SimpleGraph.card_connected_induce_le_exponential` — all connected sets of size `n`.
-/

namespace SimpleGraph

open Finset

variable {V : Type*}

/-- Inserting a detour `w → u → w` at a vertex `w` of a closed walk lengthens it by
two and adds exactly the vertex `u` to its vertex set. -/
theorem exists_detour_walk (G : SimpleGraph V) {v w u : V} (p : G.Walk v v)
    (hw : w ∈ p.support) (hwu : G.Adj w u) :
    ∃ q : G.Walk v v, q.length = p.length + 2 ∧
      ∀ x, x ∈ q.support ↔ x ∈ p.support ∨ x = u := by
  classical
  refine ⟨(p.takeUntil w hw).append (.cons hwu (.cons hwu.symm (p.dropUntil w hw))), ?_, ?_⟩
  · have h := congrArg Walk.length (p.take_spec hw)
    rw [Walk.length_append] at h
    simp only [Walk.length_append, Walk.length_cons]
    omega
  · intro x
    conv_rhs => rw [← p.take_spec hw]
    simp only [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons]
    have := (p.dropUntil w hw).start_mem_support
    grind

/-- A finite vertex set `S` containing `v` that induces a connected subgraph is the
vertex set of a closed walk from `v` of length exactly `2 (|S| - 1)`. -/
theorem exists_closedWalk_support_toFinset_eq [DecidableEq V] (G : SimpleGraph V)
    {S : Finset V} {v : V} (hv : v ∈ S) (hS : (G.induce (S : Set V)).Connected) :
    ∃ p : G.Walk v v, p.length = 2 * (#S - 1) ∧ p.support.toFinset = S := by
  suffices h : ∀ k, 1 ≤ k → k ≤ #S → ∃ T ⊆ S, #T = k ∧
      ∃ p : G.Walk v v, p.length = 2 * (k - 1) ∧ p.support.toFinset = T by
    obtain ⟨T, hTS, hT, p, hp, hpT⟩ := h #S (card_pos.2 ⟨v, hv⟩) le_rfl
    exact ⟨p, hp, hpT.trans (eq_of_subset_of_card_le hTS hT.ge)⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun _ => ⟨{v}, by simpa using hv, by simp, .nil, by simp, by simp⟩
  | succ k hk ih =>
    intro hkS
    obtain ⟨T, hTS, hT, p, hp, hpT⟩ := ih (by omega)
    obtain ⟨b, hbS, hbT⟩ : ∃ b ∈ S, b ∉ T := not_subset.1 fun h =>
      by have := card_le_card h; omega
    obtain ⟨W⟩ := hS.preconnected (⟨v, by simpa using hv⟩ : (S : Set V))
      ⟨b, by simp [hbS]⟩
    obtain ⟨d, -, hdT, hdT'⟩ := W.exists_boundary_dart {x | x.1 ∈ T}
      (by simp [← hpT]) (by simpa using hbT)
    have hadj : G.Adj d.fst.1 d.snd.1 := d.adj
    obtain ⟨q, hq, hqsupp⟩ := exists_detour_walk G p (by simpa [← hpT] using hdT) hadj
    refine ⟨insert d.snd.1 T, insert_subset (by simp) hTS,
      by rw [card_insert_of_notMem hdT', hT], q, by rw [hq, hp]; omega, ?_⟩
    ext x
    simp [hqsupp, ← hpT, or_comm]

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a graph of maximum degree at most `Δ`, there are at most `Δ ^ L` walks of length
`L` between two given vertices. -/
theorem card_finsetWalkLength_le_pow {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (L : ℕ)
    (u x : V) : #(G.finsetWalkLength L u x) ≤ Δ ^ L := by
  induction L generalizing u with
  | zero =>
    rw [finsetWalkLength]
    split_ifs with h
    · subst h; simp
    · simp
  | succ L ih =>
    rw [finsetWalkLength]
    refine card_biUnion_le.trans ?_
    calc ∑ w : G.neighborSet u, #((G.finsetWalkLength L w x).map _)
        ≤ ∑ _w : G.neighborSet u, Δ ^ L :=
          Finset.sum_le_sum fun w _ => by rw [card_map]; exact ih w
      _ ≤ Δ ^ (L + 1) := by
        rw [sum_const, card_univ, card_neighborSet_eq_degree, smul_eq_mul, pow_succ,
          mul_comm]
        exact Nat.mul_le_mul_left _ (hΔ u)

/-- **Connected sets through a vertex** (Hastings, arXiv:cond-mat/0508554v3, lines
1227–1254, after Klarner 1967). In a finite graph of maximum degree at most `Δ`, at
most `Δ ^ (2 (n - 1))` vertex sets of size `n` that contain `v` induce a connected
subgraph. -/
theorem card_connected_induce_mem_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (v : V) (n : ℕ) :
    #{S : Finset V | v ∈ S ∧ #S = n ∧ (G.induce (S : Set V)).Connected} ≤
      Δ ^ (2 * (n - 1)) := by
  have key : ∀ S ∈ ({S : Finset V | v ∈ S ∧ #S = n ∧ (G.induce (S : Set V)).Connected} :
      Finset (Finset V)), ∃ p : G.Walk v v,
        p.length = 2 * (n - 1) ∧ p.support.toFinset = S := by
    intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    obtain ⟨hv, rfl, hc⟩ := hS
    exact exists_closedWalk_support_toFinset_eq G hv hc
  choose! f hf using key
  calc _ ≤ #(G.finsetWalkLength (2 * (n - 1)) v v) := by
        refine card_le_card_of_injOn f (fun S hS => ?_) (fun S hS T hT h => ?_)
        · simpa [mem_finsetWalkLength_iff] using (hf S hS).1
        · rw [← (hf S hS).2, h, (hf T hT).2]
    _ ≤ _ := card_finsetWalkLength_le_pow G hΔ _ v v

/-- **Connected sets of a given size** (Hastings, arXiv:cond-mat/0508554v3, lines
1227–1254, after Klarner 1967). In a graph on `N` vertices of maximum degree at most
`Δ`, at most `N Δ ^ (2 (n - 1))` vertex sets of size `n` induce a connected subgraph. -/
theorem card_connected_induce_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (n : ℕ) :
    #{S : Finset V | #S = n ∧ (G.induce (S : Set V)).Connected} ≤
      Fintype.card V * Δ ^ (2 * (n - 1)) := by
  calc _ ≤ #(univ.biUnion fun v : V =>
        ({S : Finset V | v ∈ S ∧ #S = n ∧ (G.induce (S : Set V)).Connected} :
          Finset (Finset V))) := by
        refine card_le_card fun S hS => ?_
        simp only [mem_filter, mem_univ, true_and] at hS
        obtain ⟨⟨v, hv⟩⟩ := hS.2.nonempty
        simp only [mem_biUnion, mem_univ, mem_filter, true_and]
        exact ⟨v, by simpa using hv, hS.1, hS.2⟩
    _ ≤ ∑ v : V, #({S : Finset V | v ∈ S ∧ #S = n ∧ (G.induce (S : Set V)).Connected} :
          Finset (Finset V)) := card_biUnion_le
    _ ≤ ∑ _v : V, Δ ^ (2 * (n - 1)) := Finset.sum_le_sum fun v _ =>
        card_connected_induce_mem_le G hΔ v n
    _ = _ := by simp

/-- The exponential cluster count used in Hastings, arXiv:cond-mat/0508554v3,
lines 1227–1254. The constant `max 1 (Δ ^ 2)` also covers edgeless graphs,
whose connected singleton sets must still be counted. -/
theorem card_connected_induce_le_exponential {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (n : ℕ) :
    #{S : Finset V | #S = n ∧ (G.induce (S : Set V)).Connected} ≤
      Fintype.card V * (max 1 (Δ ^ 2)) ^ n := by
  refine (card_connected_induce_le G hΔ n).trans (Nat.mul_le_mul_left _ ?_)
  rw [pow_mul]
  exact (pow_le_pow_left' (le_max_right 1 (Δ ^ 2)) (n - 1)).trans
    (pow_le_pow_right' (le_max_left 1 (Δ ^ 2)) (Nat.sub_le n 1))

end SimpleGraph
