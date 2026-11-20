/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import QICLean.Circuit.Geometry.Basic
import QICLean.ManyBody.Sites.Lattice.Chain
import QICLean.ManyBody.Sites.Lattice.PathGraph

/-!
# The geometry of the edges of a graph, and windows of a chain

A simple graph `G` on the sites `V` is the geometry with one cell `{u, v}` of cost `1` for each
edge `uv` (`Geometry.graph`): the gates of a circuit on it act on disjoint pairs of neighbouring
sites. Its `r`-fold neighbourhood of a region lies within graph distance `r` of the region, so
regions at graph distance larger than `2r` have disjoint `r`-fold neighbourhoods. The open chain
of `n` sites is the graph geometry of the path `SimpleGraph.pathGraph n`, whose cells are the
pairs `{p, p + 1}`; its neighbourhoods lie within the same distance along the chain.

The windows of `m` consecutive sites of the open chain of `n` sites (`Geometry.window`) are the
intervals `[a, a + m)`, cut off at the right end of the chain, one cell of cost `1` for each
`a < n`.

This is the model of arXiv:2103.13367: gates "acting on disjoint pairs of nearest-neighbor
spins" of a lattice, with "the minimal number of edges connecting the vertices `i` and `j` in the
graph associated with the lattice" as distance.

The declarations restate `edgeBond`, `openBond` and their light-cone lemmas of
`TNLean/Circuit/Geometry.lean`, and `windowSites` of `TNLean/Circuit/WindowProduct.lean`, at
commit `414a18fb88` (Apache-2.0). The changes: the bonds are the cells of a `Geometry`; the open
chain is the graph geometry of the path, so its lemmas are those of the graph; the light cone of
radius `r` is the `r`-fold neighbourhood of the geometry; a window is `ManyBody.interval`.

## Main definitions

* `QuantumCircuit.Geometry.graph` — the edges of a simple graph, of cost `1`.
* `QuantumCircuit.Geometry.window` — the windows of `m` consecutive sites of a chain.

## Main results

* `QuantumCircuit.Geometry.iterate_neighbourhood_graph_subset` — the `r`-fold neighbourhood lies
  within graph distance `r`.
* `QuantumCircuit.Geometry.disjoint_iterate_neighbourhood_graph` — regions at graph distance
  larger than `2r` have disjoint `r`-fold neighbourhoods.
* `QuantumCircuit.Geometry.iterate_neighbourhood_pathGraph_subset`,
  `QuantumCircuit.Geometry.disjoint_iterate_neighbourhood_pathGraph` — the same on the open
  chain, in terms of positions.
-/

namespace QuantumCircuit

namespace Geometry

section Graph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The geometry of the edges of the simple graph `G`: one cell `{u, v}` of cost `1` for each
edge `uv`.

Source: arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC" ("quantum gates
acting on disjoint pairs of nearest-neighbor spins" of a lattice). -/
abbrev graph (G : SimpleGraph V) : Geometry V where
  Cell := G.edgeSet
  cell e := Finset.univ.filter (· ∈ (e : Sym2 V))
  cost _ := 1

variable {G : SimpleGraph V}

theorem mem_graph_cell {e : (graph G).Cell} {v : V} :
    v ∈ (graph G).cell e ↔ v ∈ (e : Sym2 V) := by
  simp

/-- The cell of the edge `uv` is `{u, v}`. -/
theorem graph_cell_mk {u v : V} (h : G.Adj u v) :
    (graph G).cell ⟨s(u, v), h⟩ = {u, v} := by
  ext w
  simp

theorem graph_cost_pos (e : (graph G).Cell) : 0 < (graph G).cost e :=
  Nat.one_pos

/-- Two sites of one cell are at graph distance at most `1`. -/
private theorem edist_le_one_of_mem_cell {e : (graph G).Cell} {u v : V}
    (hu : u ∈ (graph G).cell e) (hv : v ∈ (graph G).cell e) : G.edist u v ≤ 1 := by
  rw [mem_graph_cell] at hu hv
  by_cases huv : u = v
  · simp [huv]
  · have he : (e : Sym2 V) = s(u, v) := (Sym2.mem_and_mem_iff huv).mp ⟨hu, hv⟩
    have hadj : G.Adj u v := (SimpleGraph.mem_edgeSet G).mp (he ▸ e.2)
    exact (SimpleGraph.edist_eq_one_iff_adj.mpr hadj).le

variable [DecidableRel G.Adj]

/-- **The graph light cone.** The `r`-fold neighbourhood of a region in the geometry of the edges
of `G` lies within graph distance `r` of the region.

Source: arXiv:2103.13367, main text, paragraph before Proposition `propQCA2` (the distance
`d(i, j)`, "the minimal number of edges connecting the vertices `i` and `j`"). -/
theorem iterate_neighbourhood_graph_subset (R : Finset V) (r : ℕ) :
    ((graph G).neighbourhood^[r] R : Set V) ⊆ {v | ∃ x ∈ R, G.edist x v ≤ r} := by
  induction r with
  | zero => exact fun x hx ↦ ⟨x, hx, by simp⟩
  | succ r ih =>
    intro v hv
    rw [Function.iterate_succ_apply', Finset.mem_coe, neighbourhood, Finset.mem_union] at hv
    rcases hv with hv | hv
    · obtain ⟨x, hx, h⟩ := ih hv
      exact ⟨x, hx, h.trans (by exact_mod_cast Nat.le_succ r)⟩
    · obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨u, hu⟩ := (Finset.mem_filter.mp he).2
      rw [Finset.mem_inter] at hu
      obtain ⟨x, hx, h⟩ := ih hu.2
      refine ⟨x, hx, (G.edist_triangle (v := u)).trans ?_⟩
      push_cast
      exact add_le_add h (edist_le_one_of_mem_cell hu.1 hve)

/-- Regions at graph distance larger than `2r` have disjoint `r`-fold neighbourhoods. -/
theorem disjoint_iterate_neighbourhood_graph {R R' : Finset V} {r : ℕ}
    (h : ∀ x ∈ R, ∀ y ∈ R', ((2 * r : ℕ) : ℕ∞) < G.edist x y) :
    Disjoint ((graph G).neighbourhood^[r] R) ((graph G).neighbourhood^[r] R') := by
  rw [Finset.disjoint_left]
  intro v hvR hvR'
  obtain ⟨x, hx, hxv⟩ := iterate_neighbourhood_graph_subset R r hvR
  obtain ⟨y, hy, hyv⟩ := iterate_neighbourhood_graph_subset R' r hvR'
  refine (h x hx y hy).not_ge ((G.edist_triangle (v := v)).trans ?_)
  rw [SimpleGraph.edist_comm (u := v)]
  calc G.edist x v + G.edist y v ≤ r + r := add_le_add hxv hyv
    _ = ((2 * r : ℕ) : ℕ∞) := by push_cast; exact (two_mul _).symm

/-- The graph light cone in terms of `SimpleGraph.dist`: every site of the `r`-fold
neighbourhood of `R` is reachable from a site of `R` at distance at most `r`. -/
theorem iterate_neighbourhood_graph_subset_dist (R : Finset V) (r : ℕ) :
    ((graph G).neighbourhood^[r] R : Set V) ⊆
      {v | ∃ x ∈ R, G.Reachable x v ∧ G.dist x v ≤ r} := by
  intro v hv
  obtain ⟨x, hx, h⟩ := iterate_neighbourhood_graph_subset R r hv
  have hreach : G.Reachable x v :=
    SimpleGraph.edist_ne_top_iff_reachable.mp (ne_top_of_le_ne_top (by simp) h)
  refine ⟨x, hx, hreach, ?_⟩
  rw [← hreach.coe_dist_eq_edist] at h
  exact_mod_cast h

/-- Regions such that every reachable pair is at graph distance larger than `2r` have disjoint
`r`-fold neighbourhoods. -/
theorem disjoint_iterate_neighbourhood_graph_of_dist {R R' : Finset V} {r : ℕ}
    (h : ∀ x ∈ R, ∀ y ∈ R', G.Reachable x y → 2 * r < G.dist x y) :
    Disjoint ((graph G).neighbourhood^[r] R) ((graph G).neighbourhood^[r] R') := by
  refine disjoint_iterate_neighbourhood_graph fun x hx y hy ↦ ?_
  by_cases hxy : G.Reachable x y
  · rw [← hxy.coe_dist_eq_edist]
    exact_mod_cast h x hx y hy hxy
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hxy]
    exact WithTop.coe_lt_top _

end Graph

/-! ### The open chain -/

section Chain

variable {n : ℕ}

/-- The cell of the open chain on the neighbouring sites `p` and `p'`, `p' = p + 1`. -/
def pathCell {p p' : Fin n} (h : p'.val = p.val + 1) : (graph (SimpleGraph.pathGraph n)).Cell :=
  ⟨s(p, p'), SimpleGraph.pathGraph_adj.mpr (Or.inl h.symm)⟩

theorem pathCell_cell {p p' : Fin n} (h : p'.val = p.val + 1) :
    (graph (SimpleGraph.pathGraph n)).cell (pathCell h) = {p, p'} :=
  graph_cell_mk _

/-- Every cell of the open chain is a pair of neighbouring sites. -/
theorem exists_pathCell (e : (graph (SimpleGraph.pathGraph n)).Cell) :
    ∃ (p p' : Fin n) (h : p'.val = p.val + 1), e = pathCell h := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ u v =>
    rcases SimpleGraph.pathGraph_adj.mp he with h | h
    · exact ⟨u, v, h.symm, rfl⟩
    · exact ⟨v, u, h.symm, Subtype.ext Sym2.eq_swap⟩

/-- **The open-chain light cone.** The `r`-fold neighbourhood of a region of the open chain lies
within distance `r` of the region along the chain. -/
theorem iterate_neighbourhood_pathGraph_subset (R : Finset (Fin n)) (r : ℕ) :
    ((graph (SimpleGraph.pathGraph n)).neighbourhood^[r] R : Set (Fin n)) ⊆
      {j | ∃ i ∈ R, (j : ℕ) ≤ i + r ∧ (i : ℕ) ≤ j + r} := by
  intro j hj
  obtain ⟨i, hi, h⟩ := iterate_neighbourhood_graph_subset R r hj
  rw [SimpleGraph.pathGraph_edist] at h
  have h' : Nat.dist i.val j.val ≤ r := by exact_mod_cast h
  refine ⟨i, hi, ?_, ?_⟩ <;> simp only [Nat.dist] at h' <;> omega

/-- Regions at distance larger than `2r` along the open chain have disjoint `r`-fold
neighbourhoods. -/
theorem disjoint_iterate_neighbourhood_pathGraph {R R' : Finset (Fin n)} {r : ℕ}
    (h : ∀ x ∈ R, ∀ y ∈ R', (x : ℕ) + 2 * r < y ∨ (y : ℕ) + 2 * r < x) :
    Disjoint ((graph (SimpleGraph.pathGraph n)).neighbourhood^[r] R)
      ((graph (SimpleGraph.pathGraph n)).neighbourhood^[r] R') := by
  rw [Finset.disjoint_left]
  intro j hjR hjR'
  obtain ⟨x, hx, hx₁, hx₂⟩ := iterate_neighbourhood_pathGraph_subset R r hjR
  obtain ⟨y, hy, hy₁, hy₂⟩ := iterate_neighbourhood_pathGraph_subset R' r hjR'
  have := h x hx y hy
  omega

end Chain

/-! ### Windows of a chain -/

/-- The windows of `m` consecutive sites of the open chain of `n` sites: one cell
`[a, a + m)`, cut off at the right end of the chain, of cost `1` for each `a < n`.

Source: arXiv:2307.01696, main text before Theorem 1 and paragraph "The sequential-RG circuit"
(unitaries "with constant support"). -/
abbrev window (n m : ℕ) : Geometry (Fin n) where
  Cell := Fin n
  cell a := ManyBody.interval n a (a + m)
  cost _ := 1

theorem mem_window_cell {n m : ℕ} {a : (window n m).Cell} {p : Fin n} :
    p ∈ (window n m).cell a ↔ a.val ≤ p.val ∧ p.val < a.val + m :=
  ManyBody.mem_interval

end Geometry

end QuantumCircuit
