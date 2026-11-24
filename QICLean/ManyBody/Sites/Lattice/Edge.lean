/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Oriented edges of a graph on an ordered vertex type

On a linearly ordered vertex type, an edge of a simple graph `G` has a canonical orientation:
the ordered pair `(u, v)` of its endpoints with `u < v`. `ManyBody.Edge G` is the type of these
pairs, so that it has one element for each edge, and each edge comes with a first and a second
endpoint. `ManyBody.Edge.ofAdj` orients an adjacent pair given in either order.

Moved from TNLean, `TNLean/PEPS/Defs.lean` (`Edge`, `instFintypeEdge`, `Edge.ofAdj` and its lemmas)
at commit `71c1185e9352a3b5237b37a6840640751da6ca2d`. Changes: namespace `ManyBody` in place of
`TNLean.PEPS`; no other change.

The region boundary and incidence predicates were moved from TNLean,
`TNLean/PEPS/Tensor/Region/RegionBlock.lean`,
 at commit `2417e0a2e4d8a1dc2db0a14e0c9cae4ca735829e`.
The predicates are in the same namespace as the edges.

## Main definitions

* `ManyBody.Edge` — the edges of `G`, as ordered endpoint pairs `(u, v)` with `u < v`.
* `ManyBody.Edge.ofAdj` — the edge of an adjacent pair.
-/

namespace ManyBody

variable {V : Type*} [Fintype V] [LinearOrder V]


/-- Undirected edges of `G`, represented by ordered endpoint pairs `(u, v)` with
`u < v` to avoid double-counting. -/
abbrev Edge (G : SimpleGraph V) : Type _ :=
  { uv : V × V // uv.1 < uv.2 ∧ G.Adj uv.1 uv.2 }

instance instFintypeEdge (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (Edge G) :=
  inferInstance

/-- The edge of `G` on an adjacent pair `(u, v)`, with the endpoints reordered into
the `Edge` convention `·.1 < ·.2`.  Adjacency forbids `u = v`, so exactly one of
`u < v` and `v < u` holds; the smaller endpoint is placed first.  This normalizes an
unordered adjacent pair into the ordered-endpoint `Edge` representation, the operation
needed to push an edge through a vertex bijection (such as a translation), where the
bijection may swap the lexicographic order of the two endpoints. -/
def Edge.ofAdj {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : Edge G :=
  if huv : u < v then
    ⟨(u, v), huv, h⟩
  else
    ⟨(v, u), lt_of_le_of_ne (not_lt.mp huv) (G.ne_of_adj h).symm, h.symm⟩

omit [Fintype V] in
/-- On a pair already in order (`u < v`), `Edge.ofAdj` keeps the endpoints as given. -/
theorem Edge.ofAdj_of_lt {G : SimpleGraph V} {u v : V} (h : G.Adj u v) (huv : u < v) :
    Edge.ofAdj h = ⟨(u, v), huv, h⟩ := by
  rw [Edge.ofAdj, dite_eq_left huv]

omit [Fintype V] in
/-- On a pair in reverse order (`v < u`), `Edge.ofAdj` swaps the endpoints. -/
theorem Edge.ofAdj_of_gt {G : SimpleGraph V} {u v : V} (h : G.Adj u v) (hvu : v < u) :
    Edge.ofAdj h =
      ⟨(v, u), hvu, h.symm⟩ := by
  rw [Edge.ofAdj, dite_eq_right (not_lt.mpr hvu.le)]

omit [Fintype V] in
/-- The unordered endpoint set of `Edge.ofAdj h` is `{u, v}`: its two endpoints are
`u` and `v` in some order. -/
theorem Edge.ofAdj_endpoints {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    ((Edge.ofAdj h).1.1 = u ∧ (Edge.ofAdj h).1.2 = v) ∨
      ((Edge.ofAdj h).1.1 = v ∧ (Edge.ofAdj h).1.2 = u) := by
  rcases lt_or_gt_of_ne (G.ne_of_adj h) with huv | hvu
  · exact Or.inl ⟨by rw [Edge.ofAdj_of_lt h huv], by rw [Edge.ofAdj_of_lt h huv]⟩
  · exact Or.inr ⟨by rw [Edge.ofAdj_of_gt h hvu], by rw [Edge.ofAdj_of_gt h hvu]⟩

omit [Fintype V] in
/-- An edge is determined by its unordered endpoint pair: if `(u, v)` is, in some
order, the ordered endpoint pair of `e`, then orienting `(u, v)` with `Edge.ofAdj`
recovers `e`. This is the bookkeeping that makes edge constructions independent
of the order in which an unordered adjacent pair is presented. -/
theorem Edge.ofAdj_eq_of_endpoints {G : SimpleGraph V} {u v : V} (h : G.Adj u v)
    (e : Edge G)
    (H : (u = e.1.1 ∧ v = e.1.2) ∨ (u = e.1.2 ∧ v = e.1.1)) :
    Edge.ofAdj h = e := by
  apply Subtype.ext
  rcases Edge.ofAdj_endpoints h with ⟨o1, o2⟩ | ⟨o1, o2⟩ <;>
    rcases H with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact Prod.ext (o1.trans hu) (o2.trans hv)
  · exfalso
    have hlt : (Edge.ofAdj h).1.1 < (Edge.ofAdj h).1.2 := (Edge.ofAdj h).2.1
    rw [o1, o2, hu, hv] at hlt
    exact absurd hlt (not_lt.mpr e.2.1.le)
  · exfalso
    have hlt : (Edge.ofAdj h).1.1 < (Edge.ofAdj h).1.2 := (Edge.ofAdj h).2.1
    rw [o1, o2, hu, hv] at hlt
    exact absurd hlt (not_lt.mpr e.2.1.le)
  · exact Prod.ext (o1.trans hv) (o2.trans hu)

omit [Fintype V] in
/-- Two `Edge.ofAdj` constructions agree when their adjacent pairs have the same
unordered endpoints: orienting `(u, v)` and `(u', v')` gives the same edge
whenever `{u, v} = {u', v'}`. -/
theorem Edge.ofAdj_eq_ofAdj {G : SimpleGraph V} {u v u' v' : V} (h1 : G.Adj u v)
    (h2 : G.Adj u' v')
    (H : (u = u' ∧ v = v') ∨ (u = v' ∧ v = u')) :
    Edge.ofAdj h1 = Edge.ofAdj h2 := by
  rw [Edge.ofAdj_eq_of_endpoints h1 (Edge.ofAdj h2)]
  rcases Edge.ofAdj_endpoints h2 with ⟨o1, o2⟩ | ⟨o1, o2⟩ <;> rw [o1, o2] <;> tauto

end ManyBody

namespace ManyBody

variable {V : Type*} [LinearOrder V] {G : SimpleGraph V}

/-- An edge crosses the boundary of the region `R` when exactly one of its
endpoints lies in `R`. -/
def IsRegionBoundaryEdge (R : Finset V) (f : Edge G) : Prop :=
  (f.1.1 ∈ R ∧ f.1.2 ∉ R) ∨ (f.1.1 ∉ R ∧ f.1.2 ∈ R)

instance (R : Finset V) (f : Edge G) : Decidable (IsRegionBoundaryEdge (G := G) R f) := by
  unfold IsRegionBoundaryEdge
  infer_instance

/-- An edge is incident to the region `R` when at least one endpoint lies in `R`. -/
def IsRegionIncidentEdge (R : Finset V) (e : Edge G) : Prop :=
  e.1.1 ∈ R ∨ e.1.2 ∈ R

instance (R : Finset V) (e : Edge G) : Decidable (IsRegionIncidentEdge (G := G) R e) := by
  unfold IsRegionIncidentEdge
  infer_instance

/-- An edge incident to each of two disjoint regions crosses the boundary of the second. -/
theorem isRegionBoundaryEdge_of_disjoint_incident (S T : Finset V)
    (hST : Disjoint S T) {e : Edge G}
    (hS : IsRegionIncidentEdge (G := G) S e)
    (hT : IsRegionIncidentEdge (G := G) T e) : IsRegionBoundaryEdge (G := G) T e := by
  have hdis := Finset.disjoint_left.mp hST
  rcases hS with hS1 | hS2 <;> rcases hT with hT1 | hT2
  · exact (hdis hS1 hT1).elim
  · exact Or.inr ⟨fun h => hdis hS1 h, hT2⟩
  · exact Or.inl ⟨hT1, fun h => hdis hS2 h⟩
  · exact (hdis hS2 hT2).elim

/-- A boundary edge of `R` has at least one endpoint in `R`. -/
theorem isRegionBoundaryEdge_touches (R : Finset V) {f : Edge G}
    (hf : IsRegionBoundaryEdge (G := G) R f) : IsRegionIncidentEdge (G := G) R f := by
  rcases hf with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact Or.inl h1
  · exact Or.inr h2

/-- Equal regions have the same boundary-edge predicate. -/
theorem isRegionBoundaryEdge_congr {S R : Finset V} (h : S = R) (e : Edge G) :
    IsRegionBoundaryEdge (G := G) S e ↔ IsRegionBoundaryEdge (G := G) R e := by
  rw [h]


end ManyBody
