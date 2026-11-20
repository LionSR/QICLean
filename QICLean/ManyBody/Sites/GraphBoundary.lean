/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.SymmDiff
import QICLean.ManyBody.Sites.GraphBall

/-!
# Edge and vertex boundaries of a region

For a graph `G` on the sites and a region `A`, the edge boundary `∂A` is the set of edges of `G`
with one endpoint in `A` and the other outside `A`, each counted once as an unordered pair. The
inner boundary consists of the sites of `A` adjacent to a site outside `A`, and the endpoint
boundary of the endpoints of the edges of `∂A`; it is the union of the inner boundaries of `A`
and of its complement.

The edge boundary is unchanged by exchanging the region and its complement, it is subadditive
under unions and differences, and a walk from `A` to its complement crosses it. In a graph of
degree at most `k`, every set of sites meeting each boundary edge carries at most `k` boundary
edges per site; in particular `|∂A| ≤ k |A|`, `|∂A| ≤ k |inner boundary|` and
`2 |∂A| ≤ k |endpoint boundary|`. A region whose edge boundary is empty is a union of connected
components. A graph isomorphism carries each boundary of a region to the same boundary of the
image region.

The edge boundary for the nearest-neighbour graph of a finite domain of the square lattice is
moved from `QICLean/ManyBody/Sites/Lattice/Plane.lean`, where it was `ManyBody.edgeBoundary Λ A`;
it is now `ManyBody.edgeBoundary (planeDomainGraph Λ) A`. The set lemmas, the vertex boundaries,
the degree counts and the empty-boundary lemmas are moved from TNLean,
`TNLean/PEPS/AreaLaw/EdgeBoundaryCalculus.lean`, `BoundaryConventions.lean`, `ZeroBoundary.lean`
and `CrossingBudget.lean` (`exists_cut_edge_near`) at commit `414a18fb88`. Changes: every
statement is for an arbitrary graph, and the degree bound four of the square lattice is a
hypothesis `∀ v, G.degree v ≤ k`.

## Main definitions

* `ManyBody.edgeBoundary` — the edges with exactly one endpoint in a region.
* `ManyBody.innerBoundary` — the sites of a region adjacent to its complement.
* `ManyBody.endpointBoundary` — the endpoints of the boundary edges.

## Main results

* `ManyBody.mk_mem_edgeBoundary_iff` — membership of an edge in the boundary.
* `ManyBody.edgeBoundary_compl`, `ManyBody.card_edgeBoundary_union_le`,
  `ManyBody.card_edgeBoundary_sdiff_le` — the set calculus of edge boundaries.
* `ManyBody.exists_edgeBoundary_of_walk`, `ManyBody.exists_edgeBoundary_near` — a walk leaving a
  region crosses its edge boundary.
* `ManyBody.card_edgeBoundary_le_of_endpoint_cover`, `ManyBody.card_edgeBoundary_le_mul_card`,
  `ManyBody.card_edgeBoundary_le_add_mul_card_symmDiff` — degree counts.
* `ManyBody.card_edgeBoundary_le_mul_card_innerBoundary`,
  `ManyBody.two_mul_card_edgeBoundary_le_mul_card_endpointBoundary` — the vertex-boundary
  formulations.
* `ManyBody.edgeBoundary_eq_empty_iff`, `ManyBody.subset_or_disjoint_of_edgeBoundary_eq_empty` —
  regions without boundary edges.
* `ManyBody.edgeBoundary_map`, `ManyBody.innerBoundary_map`, `ManyBody.endpointBoundary_map` —
  transport along graph isomorphisms.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Section 1 (the edge boundary `∂_Λ A`), Corollary 1.2 (`cor:rectangles`, the inner and
  endpoint boundaries), Lemma 2.2 (`lem:zero-boundary`) and `08-scanner.tex`, Lemma 9.1(2).
-/

open scoped symmDiff

namespace ManyBody

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {A B : Finset V} {x y : V}

/-! ### The edge boundary -/

variable (G) in
/-- The edge boundary `∂A`: the edges of `G` with one endpoint in `A` and the other outside
`A`, as unordered pairs. Source: area law, Section 1, the definition of `∂_Λ A`. -/
noncomputable def edgeBoundary (A : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e ↦ ∃ x ∈ A, ∃ y ∉ A, e = s(x, y)

theorem mem_edgeBoundary {e : Sym2 V} :
    e ∈ edgeBoundary G A ↔ e ∈ G.edgeSet ∧ ∃ x ∈ A, ∃ y ∉ A, e = s(x, y) := by
  classical
  simp only [edgeBoundary, Finset.mem_filter, SimpleGraph.mem_edgeFinset]

/-- An edge `{x, y}` crosses the boundary of `A` exactly when it is an edge of `G` and exactly
one of its endpoints lies in `A`. -/
theorem mk_mem_edgeBoundary_iff :
    s(x, y) ∈ edgeBoundary G A ↔ G.Adj x y ∧ (x ∈ A ∧ y ∉ A ∨ y ∈ A ∧ x ∉ A) := by
  rw [mem_edgeBoundary, SimpleGraph.mem_edgeSet]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨x', hx, y', hy, he⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
  · rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
    · exact ⟨x, hx, y, hy, rfl⟩
    · exact ⟨y, hy, x, hx, Sym2.eq_swap⟩

theorem edgeBoundary_subset_edgeFinset [Fintype G.edgeSet] :
    edgeBoundary G A ⊆ G.edgeFinset := fun _ he ↦
  SimpleGraph.mem_edgeFinset.mpr (mem_edgeBoundary.mp he).1

/-- The empty region has no boundary edges. -/
@[simp] theorem edgeBoundary_empty : edgeBoundary G ∅ = ∅ := by
  classical
  simp [edgeBoundary]

/-- The region of all sites has no boundary edges. -/
@[simp] theorem edgeBoundary_univ : edgeBoundary G Finset.univ = ∅ := by
  classical
  simp [edgeBoundary]

/-- Exchanging a region and its complement preserves the edge boundary. -/
@[simp] theorem edgeBoundary_compl [DecidableEq V] : edgeBoundary G Aᶜ = edgeBoundary G A := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    simp only [mk_mem_edgeBoundary_iff, Finset.mem_compl, not_not]
    tauto

/-- An edge crossing the boundary of a union crosses the boundary of one of the two regions. -/
theorem edgeBoundary_union_subset [DecidableEq V] :
    edgeBoundary G (A ∪ B) ⊆ edgeBoundary G A ∪ edgeBoundary G B := by
  classical
  intro e
  induction e using Sym2.ind with
  | h x y =>
    simp only [Finset.mem_union, mk_mem_edgeBoundary_iff]
    tauto

/-- An edge crossing the boundary of a difference crosses the boundary of one of the two
regions. -/
theorem edgeBoundary_sdiff_subset [DecidableEq V] :
    edgeBoundary G (A \ B) ⊆ edgeBoundary G A ∪ edgeBoundary G B := by
  classical
  intro e
  induction e using Sym2.ind with
  | h x y =>
    simp only [Finset.mem_union, mk_mem_edgeBoundary_iff, Finset.mem_sdiff]
    tauto

/-- An edge crossing the boundary of `A` crosses the boundary of `B` or that of the set `A ∆ B`
of sites where the two regions differ. -/
theorem edgeBoundary_subset_union_symmDiff [DecidableEq V] :
    edgeBoundary G A ⊆ edgeBoundary G B ∪ edgeBoundary G (A ∆ B) := by
  classical
  intro e
  induction e using Sym2.ind with
  | h x y =>
    simp only [Finset.mem_union, mk_mem_edgeBoundary_iff, Finset.mem_symmDiff]
    tauto

/-- The edge boundary is subadditive under unions. -/
theorem card_edgeBoundary_union_le [DecidableEq V] :
    (edgeBoundary G (A ∪ B)).card ≤ (edgeBoundary G A).card + (edgeBoundary G B).card := by
  classical
  exact (Finset.card_le_card edgeBoundary_union_subset).trans (Finset.card_union_le _ _)

/-- The edge boundary is subadditive under differences. -/
theorem card_edgeBoundary_sdiff_le [DecidableEq V] :
    (edgeBoundary G (A \ B)).card ≤ (edgeBoundary G A).card + (edgeBoundary G B).card := by
  classical
  exact (Finset.card_le_card edgeBoundary_sdiff_subset).trans (Finset.card_union_le _ _)

/-! ### Walks crossing the boundary -/

/-- A walk from a site of `A` to a site outside `A` crosses an edge `{u, v}` of `∂A` with
`u ∈ A` and `v ∉ A`, and its initial segment joins the starting site to `u` in at most as many
steps. Source: area law, Section 1, the definition of `∂_Λ A`. -/
theorem exists_edgeBoundary_of_walk (p : G.Walk x y) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ u v, u ∈ A ∧ v ∉ A ∧ s(u, v) ∈ edgeBoundary G A ∧
      ∃ p' : G.Walk x u, p'.length ≤ p.length := by
  classical
  obtain ⟨d, hd, hdA, hdA'⟩ := p.exists_boundary_dart (A : Set V) hx hy
  have hsupp := p.dart_fst_mem_support_of_mem_darts hd
  exact ⟨d.fst, d.snd, hdA, hdA', mk_mem_edgeBoundary_iff.mpr ⟨d.adj, Or.inl ⟨hdA, hdA'⟩⟩,
    p.takeUntil d.fst hsupp, p.length_takeUntil_le_length hsupp⟩

/-- **A boundary edge near a site.** If a site `a ∈ A` is within distance `r` of a site outside
`A`, then some edge `{u, v}` of `∂A` with `u ∈ A` and `v ∉ A` has `d(a, u) ≤ r`.
Source: area law, `03-quasilocal.tex`, lines 441–447. -/
theorem exists_edgeBoundary_near {a : V} {r : ℕ} (ha : a ∈ A) (hx : x ∉ A)
    (hax : G.edist a x ≤ r) :
    ∃ u v, u ∈ A ∧ v ∉ A ∧ s(u, v) ∈ edgeBoundary G A ∧ G.edist a u ≤ r := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top r) hax)
  obtain ⟨u, v, hu, hv, he, p', hp'⟩ := exists_edgeBoundary_of_walk p ha hx
  refine ⟨u, v, hu, hv, he, p'.edist_le.trans ?_⟩
  calc (p'.length : ℕ∞) ≤ p.length := by exact_mod_cast hp'
    _ = G.edist a x := hp
    _ ≤ r := hax

/-! ### Degree counts -/

section Degree

variable [DecidableRel G.Adj] {k : ℕ}

/-- **Endpoint covers.** In a graph of degree at most `k`, if every boundary edge of `A` has an
endpoint in `R`, then `A` has at most `k |R|` boundary edges.
Source: area law, `08-scanner.tex`, Lemma 9.1(2), lines 251–257. -/
theorem card_edgeBoundary_le_of_endpoint_cover (hdeg : ∀ v, G.degree v ≤ k) (R : Finset V)
    (hR : ∀ x ∈ A, ∀ y ∉ A, G.Adj x y → x ∈ R ∨ y ∈ R) :
    (edgeBoundary G A).card ≤ k * R.card := by
  classical
  have hsub : edgeBoundary G A ⊆ R.biUnion fun v ↦ G.incidenceFinset v := by
    intro e
    induction e using Sym2.ind with
    | h x y =>
      intro he
      obtain ⟨hxy, hcut⟩ := mk_mem_edgeBoundary_iff.mp he
      simp only [Finset.mem_biUnion, SimpleGraph.mem_incidenceFinset]
      rcases hcut with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · rcases hR x hx y hy hxy with h | h
        · exact ⟨x, h, (G.mem_incidenceSet x y).mpr hxy⟩
        · exact ⟨y, h, Sym2.eq_swap ▸ (G.mem_incidenceSet y x).mpr hxy.symm⟩
      · rcases hR y hy x hx hxy.symm with h | h
        · exact ⟨y, h, Sym2.eq_swap ▸ (G.mem_incidenceSet y x).mpr hxy.symm⟩
        · exact ⟨x, h, (G.mem_incidenceSet x y).mpr hxy⟩
  calc (edgeBoundary G A).card ≤ (R.biUnion fun v ↦ G.incidenceFinset v).card :=
        Finset.card_le_card hsub
    _ ≤ R.card * k := Finset.card_biUnion_le_card_mul _ _ _ fun v _ ↦
        (G.card_incidenceFinset_eq_degree v).trans_le (hdeg v)
    _ = k * R.card := Nat.mul_comm _ _

/-- In a graph of degree at most `k`, each site of a region carries at most `k` of its
boundary edges. -/
theorem card_edgeBoundary_le_mul_card (hdeg : ∀ v, G.degree v ≤ k) :
    (edgeBoundary G A).card ≤ k * A.card :=
  card_edgeBoundary_le_of_endpoint_cover hdeg A fun _ hx _ _ _ ↦ Or.inl hx

/-- **Changing sites.** In a graph of degree at most `k`, changing the sites of `A ∆ B` raises
the boundary by at most `k` edges per changed site.
Source: area law, `08-scanner.tex`, Lemma 9.1(2), lines 254–257. -/
theorem card_edgeBoundary_le_add_mul_card_symmDiff [DecidableEq V]
    (hdeg : ∀ v, G.degree v ≤ k) :
    (edgeBoundary G A).card ≤ (edgeBoundary G B).card + k * (A ∆ B).card :=
  (Finset.card_le_card edgeBoundary_subset_union_symmDiff).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (card_edgeBoundary_le_mul_card hdeg) _))

end Degree

/-! ### Regions without boundary edges -/

/-- Without boundary edges, adjacent sites lie on the same side of the region. -/
theorem mem_iff_of_adj_of_edgeBoundary_eq_empty (hA : edgeBoundary G A = ∅) (hxy : G.Adj x y) :
    x ∈ A ↔ y ∈ A := by
  have key : ∀ {a b : V}, G.Adj a b → a ∈ A → b ∉ A → False := fun hab ha hb ↦ by
    simpa [hA] using mk_mem_edgeBoundary_iff.mpr ⟨hab, Or.inl ⟨ha, hb⟩⟩
  exact ⟨fun hx ↦ by_contra (key hxy hx), fun hy ↦ by_contra (key hxy.symm hy)⟩

/-- Without boundary edges, reachable sites lie on the same side of the region. -/
theorem mem_iff_of_reachable_of_edgeBoundary_eq_empty (hA : edgeBoundary G A = ∅)
    (hxy : G.Reachable x y) : x ∈ A ↔ y ∈ A := by
  obtain ⟨w⟩ := hxy
  induction w with
  | nil => rfl
  | cons h _ ih => exact (mem_iff_of_adj_of_edgeBoundary_eq_empty hA h).trans ih

/-- A region has no boundary edges exactly when no edge joins it to its complement. -/
theorem edgeBoundary_eq_empty_iff :
    edgeBoundary G A = ∅ ↔ ∀ x y, G.Adj x y → (x ∈ A ↔ y ∈ A) := by
  refine ⟨fun hA _ _ ↦ mem_iff_of_adj_of_edgeBoundary_eq_empty hA, fun h ↦ ?_⟩
  refine Finset.eq_empty_iff_forall_notMem.mpr fun e ↦ ?_
  induction e using Sym2.ind with
  | h x y =>
    rw [mk_mem_edgeBoundary_iff]
    rintro ⟨hxy, ⟨hx, hy⟩ | ⟨hy, hx⟩⟩
    · exact hy ((h x y hxy).mp hx)
    · exact hx ((h x y hxy).mpr hy)

/-- **A region without boundary edges splits no connected set**: a set of sites any two of
which are joined by a walk lies inside the region or is disjoint from it.
Source: area law, Lemma 2.2 (`lem:zero-boundary`). -/
theorem subset_or_disjoint_of_edgeBoundary_eq_empty (hA : edgeBoundary G A = ∅) {X : Finset V}
    (hX : ∀ x ∈ X, ∀ y ∈ X, G.Reachable x y) : X ⊆ A ∨ Disjoint X A := by
  by_cases h : ∃ x ∈ X, x ∈ A
  · obtain ⟨x, hx, hxA⟩ := h
    exact Or.inl fun y hy ↦ (mem_iff_of_reachable_of_edgeBoundary_eq_empty hA (hX x hx y hy)).mp hxA
  · exact Or.inr (Finset.disjoint_left.mpr fun x hx hxA ↦ h ⟨x, hx, hxA⟩)

open scoped Classical in
/-- The sites of a set of connected components form a region without boundary edges. -/
theorem edgeBoundary_filter_connectedComponentMk_mem (s : Set G.ConnectedComponent) :
    edgeBoundary G (Finset.univ.filter fun x ↦ G.connectedComponentMk x ∈ s) = ∅ :=
  edgeBoundary_eq_empty_iff.mpr fun x y hxy ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.ConnectedComponent.eq.mpr hxy.reachable]

/-! ### Vertex boundaries -/

variable (G) in
/-- The inner boundary of `A`: the sites of `A` adjacent to a site outside `A`.
Source: area law, Corollary 1.2, the inner boundary. -/
noncomputable def innerBoundary (A : Finset V) : Finset V := by
  classical
  exact A.filter fun x ↦ ∃ y ∉ A, G.Adj x y

variable (G) in
/-- The endpoint boundary of `A`: both endpoints of every edge of `∂A`.
Source: area law, Corollary 1.2, the set `Z_A`. -/
noncomputable def endpointBoundary (A : Finset V) : Finset V := by
  classical
  exact (edgeBoundary G A).biUnion Sym2.toFinset

theorem mem_innerBoundary : x ∈ innerBoundary G A ↔ x ∈ A ∧ ∃ y ∉ A, G.Adj x y := by
  classical
  simp only [innerBoundary, Finset.mem_filter]

/-- A site lies in the endpoint boundary exactly when an edge joins it to a site on the other
side of the region. -/
theorem mem_endpointBoundary :
    x ∈ endpointBoundary G A ↔ ∃ y, G.Adj x y ∧ (x ∈ A ∧ y ∉ A ∨ y ∈ A ∧ x ∉ A) := by
  classical
  simp only [endpointBoundary, Finset.mem_biUnion, Sym2.mem_toFinset]
  constructor
  · rintro ⟨e, he, hxe⟩
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
    exact ⟨y, mk_mem_edgeBoundary_iff.mp he⟩
  · rintro ⟨y, hy⟩
    exact ⟨s(x, y), mk_mem_edgeBoundary_iff.mpr hy, Sym2.mem_mk_left x y⟩

theorem innerBoundary_subset : innerBoundary G A ⊆ A := fun _ hx ↦ (mem_innerBoundary.mp hx).1

@[simp] theorem innerBoundary_empty : innerBoundary G ∅ = ∅ := by
  classical
  simp [innerBoundary]

@[simp] theorem innerBoundary_univ : innerBoundary G Finset.univ = ∅ := by
  classical
  simp [innerBoundary]

@[simp] theorem endpointBoundary_empty : endpointBoundary G ∅ = ∅ := by
  classical
  simp [endpointBoundary]

@[simp] theorem endpointBoundary_univ : endpointBoundary G Finset.univ = ∅ := by
  classical
  simp [endpointBoundary]

/-- The endpoint boundary is the union of the inner boundaries of a region and of its
complement. -/
theorem endpointBoundary_eq_union [DecidableEq V] :
    endpointBoundary G A = innerBoundary G A ∪ innerBoundary G Aᶜ := by
  ext x
  simp only [mem_endpointBoundary, Finset.mem_union, mem_innerBoundary, Finset.mem_compl,
    not_not]
  constructor
  · rintro ⟨y, hxy, ⟨hx, hy⟩ | ⟨hy, hx⟩⟩
    · exact Or.inl ⟨hx, y, hy, hxy⟩
    · exact Or.inr ⟨hx, y, hy, hxy⟩
  · rintro (⟨hx, y, hy, hxy⟩ | ⟨hx, y, hy, hxy⟩)
    · exact ⟨y, hxy, Or.inl ⟨hx, hy⟩⟩
    · exact ⟨y, hxy, Or.inr ⟨hy, hx⟩⟩

@[simp] theorem endpointBoundary_compl [DecidableEq V] :
    endpointBoundary G Aᶜ = endpointBoundary G A := by
  rw [endpointBoundary_eq_union, endpointBoundary_eq_union, compl_compl, Finset.union_comm]

section Degree

variable [DecidableRel G.Adj] {k : ℕ}

/-- **Inner boundary.** In a graph of degree at most `k`, a region has at most `k` boundary
edges per site of its inner boundary.
Source: area law, Corollary 1.2, the first bound of its proof. -/
theorem card_edgeBoundary_le_mul_card_innerBoundary (hdeg : ∀ v, G.degree v ≤ k) :
    (edgeBoundary G A).card ≤ k * (innerBoundary G A).card :=
  card_edgeBoundary_le_of_endpoint_cover hdeg _ fun _ hx y hy hxy ↦
    Or.inl (mem_innerBoundary.mpr ⟨hx, y, hy, hxy⟩)

/-- **Endpoint boundary.** In a graph of degree at most `k`, counting both endpoints of every
boundary edge gives `2 |∂A| ≤ k |endpoint boundary|`.
Source: area law, Corollary 1.2, the second bound of its proof. -/
theorem two_mul_card_edgeBoundary_le_mul_card_endpointBoundary (hdeg : ∀ v, G.degree v ≤ k) :
    2 * (edgeBoundary G A).card ≤ k * (endpointBoundary G A).card := by
  classical
  have hdisj : Disjoint (innerBoundary G A) (innerBoundary G Aᶜ) :=
    Finset.disjoint_of_subset_left innerBoundary_subset
      (Finset.disjoint_of_subset_right innerBoundary_subset disjoint_compl_right)
  have h₁ := card_edgeBoundary_le_mul_card_innerBoundary (A := A) hdeg
  have h₂ := card_edgeBoundary_le_mul_card_innerBoundary (A := Aᶜ) hdeg
  rw [edgeBoundary_compl] at h₂
  rw [endpointBoundary_eq_union, Finset.card_union_of_disjoint hdisj, Nat.mul_add]
  omega

end Degree

/-! ### Transport along graph isomorphisms -/

section Map

variable {W : Type*} [Fintype W] {G' : SimpleGraph W}

/-- A graph isomorphism carries the edge boundary of a region onto the edge boundary of its
image. -/
theorem edgeBoundary_map (f : G ≃g G') (A : Finset V) :
    edgeBoundary G' (A.map f.toEquiv.toEmbedding) =
      (edgeBoundary G A).map f.toEquiv.toEmbedding.sym2Map := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨a, rfl⟩ := f.surjective x
    obtain ⟨b, rfl⟩ := f.surjective y
    simp only [Finset.mem_map, mk_mem_edgeBoundary_iff, f.map_adj_iff]
    constructor
    · intro h
      refine ⟨s(a, b), mk_mem_edgeBoundary_iff.mpr ?_, rfl⟩
      simpa [Finset.mem_map, RelIso.coe_toEmbedding] using h
    · rintro ⟨e, he, hfe⟩
      induction e using Sym2.ind with
      | h c d =>
        have hcd : s(f c, f d) = s(f a, f b) := hfe
        rw [mk_mem_edgeBoundary_iff] at he
        simp only [RelIso.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
        rcases Sym2.eq_iff.mp hcd with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · rw [f.injective h₁, f.injective h₂] at he
          exact he
        · rw [f.injective h₁, f.injective h₂] at he
          exact ⟨he.1.symm, he.2.symm⟩

/-- A graph isomorphism preserves the number of boundary edges. -/
theorem card_edgeBoundary_map (f : G ≃g G') (A : Finset V) :
    (edgeBoundary G' (A.map f.toEquiv.toEmbedding)).card = (edgeBoundary G A).card := by
  rw [edgeBoundary_map, Finset.card_map]

/-- A graph isomorphism carries the inner boundary of a region onto the inner boundary of its
image. -/
theorem innerBoundary_map (f : G ≃g G') (A : Finset V) :
    innerBoundary G' (A.map f.toEquiv.toEmbedding) =
      (innerBoundary G A).map f.toEquiv.toEmbedding := by
  ext x
  obtain ⟨a, rfl⟩ := f.surjective x
  simp only [Finset.mem_map, mem_innerBoundary, RelIso.coe_toEmbedding,
    EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
  refine and_congr_right fun _ ↦ ⟨fun ⟨y, hy, hxy⟩ ↦ ?_, fun ⟨b, hb, hab⟩ ↦ ?_⟩
  · obtain ⟨b, rfl⟩ := f.surjective y
    exact ⟨b, fun h ↦ hy ⟨b, h, rfl⟩, f.map_adj_iff.mp hxy⟩
  · refine ⟨f b, fun ⟨c, hc, hcb⟩ ↦ hb (f.injective hcb ▸ hc), f.map_adj_iff.mpr hab⟩

/-- A graph isomorphism carries the endpoint boundary of a region onto the endpoint boundary of
its image. -/
theorem endpointBoundary_map (f : G ≃g G') (A : Finset V) :
    endpointBoundary G' (A.map f.toEquiv.toEmbedding) =
      (endpointBoundary G A).map f.toEquiv.toEmbedding := by
  classical
  have hc : (A.map f.toEquiv.toEmbedding)ᶜ = Aᶜ.map f.toEquiv.toEmbedding := by
    ext x
    obtain ⟨a, rfl⟩ := f.surjective x
    simp
  rw [endpointBoundary_eq_union, endpointBoundary_eq_union, Finset.map_union, hc,
    innerBoundary_map, innerBoundary_map]

end Map

end ManyBody
