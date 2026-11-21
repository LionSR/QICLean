/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Group.Action.TypeTags
import QICLean.Algebra.Combinatorics.ZModDisplacement
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Basic.Real.Basic
import Mathlib.Order.SuccPred.ENat
import Mathlib.Basic.Real.ENatENNReal
import Mathlib.Topology.EMetricSpace.Defs
import QICLean.ManyBody.Sites.Cut

/-!
# Graph balls and neighbourhoods as regions

For a graph `G` on the sites, the closed ball `N_l(a) = {x : d_G(a, x) ≤ l}` of natural radius
`l` about a site `a` is Mathlib's open ball `SimpleGraph.ball a (l + 1)`. Statements about
regions take finite sets of sites, so `ManyBody.graphBall G a l` is that ball as a `Finset`;
`ManyBody.coe_graphBall` identifies the two. The closed neighbourhood
`N_l(S) = ⋃_{x ∈ S} N_l(x)` of a region `S` is `ManyBody.graphNeighborhood G S l`, and the
extended distance `d_G(x, S) = min_{y ∈ S} d_G(x, y)` from a site to a region is
`ManyBody.setEdist G S x`; a site lies in `N_l(S)` exactly when `d_G(x, S) ≤ l`.

The balls increase with the radius, a site at infinite distance lies in none of them, and on a
finite graph they stabilize on the connected component of the centre. Membership is measured by
the extended distance, so sites of other components never enter a ball, although their natural
distance has the value zero. The extended graph distance, read in `ℝ≥0∞`, is an extended
pseudometric on the sites, `ManyBody.graphPseudoEMetricSpace G`.

If two outer regions are disjoint and every ball of radius `ℓ + R` about either of two cores
lies in its outer region, then the radius-`ℓ` neighbourhood of the remaining sites and of the
supports crossing the first outer region avoids both cores, for supports of graph diameter at
most `R`.

Moved from TNLean, `TNLean/Circuit/LiebRobinson/GraphLocalization.lean` (the definition) and
`GraphBallStabilization.lean` at commit `71c1185e9352a3b5237b37a6840640751da6ca2d`. Changes:
the ball is defined from `SimpleGraph.ball` instead of as a filter of the sites. The
separation lemmas are moved from `TNLean/Circuit/LiebRobinson/SupportSeparation.lean` at the
same commit, with `ManyBody.crossingTerms` in place of `Entropy.crossingTerms`.

The neighbourhood of a region, the distance to a region and the extended pseudometric are moved
from TNLean, `TNLean/Lattice/FiniteDomain.lean` (`graphNeighborhood`),
`TNLean/PEPS/AreaLaw/FiniteSetTruncation.lean` (`setDist`) and
`TNLean/PEPS/AreaLaw/GraphExtendedMetric.lean` at commit `414a18fb88`. Changes: the
neighbourhood is stated for an arbitrary graph, as the union of graph balls, instead of by walks
in the plane domain graph; the distance to a region is renamed `setEdist`.

## Main definitions

* `ManyBody.graphBall` — the closed graph ball of natural radius, as a region.
* `ManyBody.graphNeighborhood` — the closed neighbourhood of a region.
* `ManyBody.setEdist` — the extended graph distance from a site to a region.
* `ManyBody.graphPseudoEMetricSpace` — the extended graph distance as an extended pseudometric.
* `ManyBody.IsGraphSeparated` — two regions at graph distance larger than a given radius.

## Main results

* `ManyBody.coe_graphBall`, `ManyBody.mem_graphBall` — the ball and its membership.
* `ManyBody.exists_graphBall_eq_reachable` — the balls stabilize on the component of the
  centre.
* `ManyBody.graphBall_subset_of_finite_distance_margin` — a real distance margin contains the
  balls of smaller radius.
* `ManyBody.mem_graphNeighborhood`, `ManyBody.mem_graphNeighborhood_iff_setEdist_le` —
  membership in a neighbourhood.
* `ManyBody.graphNeighborhood_graphNeighborhood_subset`, `ManyBody.graphNeighborhood_succ` —
  neighbourhoods compose by adding radii, and the neighbourhood of radius `l + 1` is the
  neighbourhood of radius `1` of the neighbourhood of radius `l`.
* `ManyBody.IsGraphSeparated.disjoint_graphNeighborhood` — regions separated by `2l` have
  disjoint neighbourhoods of radius `l`.
* `ManyBody.reset_graphNeighborhood_disjoint_cores` — neighbourhoods of crossing supports avoid
  interior cores.
-/

namespace ManyBody

variable {V : Type*} [Fintype V]

/-- The closed graph ball `N_l(a) = {x : d_G(a, x) ≤ l}`, the open ball of radius `l + 1`, as a
region. Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`03-quasilocal.tex`, line 17. -/
noncomputable def graphBall (G : SimpleGraph V) (a : V) (l : ℕ) : Finset V := by
  classical exact (G.ball a (l + 1)).toFinset

@[simp, norm_cast]
theorem coe_graphBall (G : SimpleGraph V) (a : V) (l : ℕ) :
    (graphBall G a l : Set V) = G.ball a (l + 1) := by
  classical
  simp [graphBall]

theorem mem_graphBall {G : SimpleGraph V} {a x : V} {l : ℕ} :
    x ∈ graphBall G a l ↔ G.edist a x ≤ l := by
  rw [← Finset.mem_coe, coe_graphBall, SimpleGraph.mem_ball, SimpleGraph.edist_comm]
  exact ENat.lt_add_one_iff (ENat.natCast_ne_top l)

/-- Graph balls increase with their radius. Source: area law, `09-amplification.tex`,
lines 124–132. -/
theorem graphBall_mono (G : SimpleGraph V) (a : V) : Monotone (graphBall G a) := by
  intro m n hmn x hx
  apply mem_graphBall.mpr
  exact (mem_graphBall.mp hx).trans (by exact_mod_cast hmn)

/-- A site at infinite distance belongs to no finite graph ball. Source: area law,
`09-amplification.tex`, lines 133–137. -/
theorem notMem_graphBall_of_edist_eq_top {G : SimpleGraph V} {a y : V}
    (hy : G.edist a y = ⊤) (n : ℕ) : y ∉ graphBall G a n := by
  intro hmem
  have hdist := mem_graphBall.mp hmem
  rw [hy] at hdist
  exact (not_le_of_gt (ENat.natCast_lt_top n)) hdist

/-- Beyond the maximum finite distance from the centre, its graph ball is exactly its reachable
set. No connectedness or global-diameter assumption is needed. Source: area law,
`09-amplification.tex`, lines 135–139. -/
theorem coe_graphBall_eq_reachable_of_sup_dist_le (G : SimpleGraph V) (a : V)
    {n : ℕ} (hn : Finset.univ.sup (G.dist a) ≤ n) :
    (graphBall G a n : Set V) = {x | G.Reachable a x} := by
  ext x
  change x ∈ graphBall G a n ↔ G.Reachable a x
  constructor
  · intro hx
    exact SimpleGraph.reachable_of_edist_ne_top
      (ne_of_lt ((mem_graphBall.mp hx).trans_lt (ENat.natCast_lt_top n)))
  · intro hx
    apply mem_graphBall.mpr
    rw [← hx.coe_dist_eq_edist]
    exact_mod_cast (Finset.le_sup (f := G.dist a) (Finset.mem_univ x)).trans hn

/-- The balls of a finite graph stabilize exactly on the component of the centre. Source: area
law, `09-amplification.tex`, lines 135–139. -/
theorem exists_graphBall_eq_reachable (G : SimpleGraph V) (a : V) :
    ∃ N, ∀ n ≥ N, (graphBall G a n : Set V) = {x | G.Reachable a x} :=
  ⟨Finset.univ.sup (G.dist a), fun _ hn ↦ coe_graphBall_eq_reachable_of_sup_dist_le G a hn⟩

/-- A strict real distance margin contains every closed ball whose natural radius is at most
that margin. Sites at infinite distance impose no condition.
TNLean one-dimensional note, `part2a_mps_information.tex`, lines 419–425. -/
theorem graphBall_subset_of_finite_distance_margin (G : SimpleGraph V) (D : Finset V) (x : V)
    (w : ℝ) (m : ℕ) (hm : (m : ℝ) ≤ w)
    (hmargin : ∀ y : V, y ∉ D → ∀ d : ℕ, G.edist x y = (d : ℕ∞) → w < (d : ℝ)) :
    graphBall G x m ⊆ D := by
  intro y hy
  by_contra hyD
  have hxy := mem_graphBall.mp hy
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top m) hxy)
  have hdm : d ≤ m := ENat.natCast_le_natCast.mp (hd ▸ hxy)
  exact (not_lt_of_ge ((Nat.cast_le.mpr hdm).trans hm)) (hmargin y hyD d hd.symm)

/-! ### Distance to a region -/

section SetEdist

variable {G : SimpleGraph V} {S : Finset V} {x y : V} {r : ℕ∞}

omit [Fintype V] in
variable (G) in
/-- The extended graph distance `d_G(x, S) = min_{y ∈ S} d_G(x, y)` from a site to a region. It
is infinite when no site of `S` can be reached from `x`, in particular when `S` is empty.
Source: area law, `03-quasilocal.tex`, line 418. -/
noncomputable def setEdist (S : Finset V) (x : V) : ℕ∞ := S.inf fun y ↦ G.edist x y

omit [Fintype V] in
theorem setEdist_le_edist (hy : y ∈ S) : setEdist G S x ≤ G.edist x y :=
  Finset.inf_le (f := fun y ↦ G.edist x y) hy

omit [Fintype V] in
theorem le_setEdist_iff : r ≤ setEdist G S x ↔ ∀ y ∈ S, r ≤ G.edist x y :=
  Finset.le_inf_iff

omit [Fintype V] in
@[simp] theorem setEdist_empty (G : SimpleGraph V) (x : V) : setEdist G ∅ x = ⊤ :=
  Finset.inf_empty

omit [Fintype V] in
/-- A finite distance to a region is attained at a site of the region. -/
theorem exists_mem_edist_eq_setEdist (hx : setEdist G S x ≠ ⊤) :
    ∃ y ∈ S, G.edist x y = setEdist G S x := by
  have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun h ↦ hx (by simp [h])
  obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_inf S hne fun y ↦ G.edist x y
  exact ⟨y, hy, he.symm⟩

omit [Fintype V] in
/-- The distance to a region is infinite exactly when no site of the region is reachable. -/
theorem setEdist_eq_top_iff : setEdist G S x = ⊤ ↔ ∀ y ∈ S, ¬ G.Reachable x y := by
  simp only [setEdist, Finset.inf_eq_top_iff, ← SimpleGraph.edist_ne_top_iff_reachable, not_not]

omit [Fintype V] in
/-- The distance to a region vanishes exactly at the sites of the region. -/
theorem setEdist_eq_zero_iff : setEdist G S x = 0 ↔ x ∈ S := by
  refine ⟨fun h ↦ ?_, fun h ↦ nonpos_iff_eq_zero.mp
    ((setEdist_le_edist h).trans_eq (SimpleGraph.edist_self))⟩
  obtain ⟨y, hy, he⟩ := exists_mem_edist_eq_setEdist (h.symm ▸ ENat.top_ne_zero.symm)
  rw [h, SimpleGraph.edist_eq_zero_iff] at he
  exact he ▸ hy

end SetEdist

/-! ### Neighbourhoods of a region -/

section Neighborhood

variable [DecidableEq V] {G : SimpleGraph V} {S T : Finset V} {x y : V} {l m : ℕ}

variable (G) in
/-- The closed graph neighbourhood `N_l(S) = {y : d_G(x, y) ≤ l for some x ∈ S}` of natural
radius `l` about a region `S`: the union of the closed graph balls about its sites. For the
nearest-neighbour graph of a finite domain of the square lattice it is the neighbourhood of the
area-law manuscript, measured by walks inside the domain.
Source: OpenAI, *A two-dimensional area law from a global spectral gap*, Section 2, the
induced-graph distance conventions. -/
noncomputable def graphNeighborhood (S : Finset V) (l : ℕ) : Finset V :=
  S.biUnion fun x ↦ graphBall G x l

theorem mem_graphNeighborhood : y ∈ graphNeighborhood G S l ↔ ∃ x ∈ S, G.edist x y ≤ l := by
  simp only [graphNeighborhood, Finset.mem_biUnion, mem_graphBall]

/-- Membership in a neighbourhood by walks: some walk of length at most `l` joins a site of the
region to the given site. -/
theorem mem_graphNeighborhood_iff_exists_walk :
    y ∈ graphNeighborhood G S l ↔ ∃ x ∈ S, ∃ p : G.Walk x y, p.length ≤ l := by
  rw [mem_graphNeighborhood]
  refine exists_congr fun x ↦ and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
      (ne_top_of_le_ne_top (ENat.natCast_ne_top l) h)
    exact ⟨p, by exact_mod_cast hp ▸ h⟩
  · obtain ⟨p, hp⟩ := h
    exact p.edist_le.trans (by exact_mod_cast hp)

/-- A site lies in the neighbourhood of radius `l` exactly when its distance to the region is
at most `l`. -/
theorem mem_graphNeighborhood_iff_setEdist_le :
    y ∈ graphNeighborhood G S l ↔ setEdist G S y ≤ l := by
  rw [mem_graphNeighborhood]
  constructor
  · rintro ⟨x, hx, h⟩
    exact (setEdist_le_edist hx).trans (by rwa [SimpleGraph.edist_comm])
  · intro h
    obtain ⟨x, hx, he⟩ := exists_mem_edist_eq_setEdist
      (ne_top_of_le_ne_top (ENat.natCast_ne_top l) h)
    exact ⟨x, hx, by rw [SimpleGraph.edist_comm, he]; exact h⟩

/-- A site outside the neighbourhood of radius `l` is at distance more than `l` from every site
of the region. -/
theorem lt_edist_of_notMem_graphNeighborhood (hy : y ∉ graphNeighborhood G S l) (hx : x ∈ S) :
    (l : ℕ∞) < G.edist x y :=
  lt_of_not_ge fun h ↦ hy (mem_graphNeighborhood.mpr ⟨x, hx, h⟩)

@[simp] theorem graphNeighborhood_singleton (a : V) :
    graphNeighborhood G {a} l = graphBall G a l :=
  Finset.singleton_biUnion

@[simp] theorem graphNeighborhood_empty : graphNeighborhood G ∅ l = ∅ :=
  Finset.biUnion_empty

/-- The neighbourhood of radius zero is the region itself. -/
@[simp] theorem graphNeighborhood_zero : graphNeighborhood G S 0 = S := by
  ext y
  simp [mem_graphNeighborhood]

theorem graphNeighborhood_union :
    graphNeighborhood G (S ∪ T) l = graphNeighborhood G S l ∪ graphNeighborhood G T l :=
  Finset.union_biUnion

theorem graphBall_subset_graphNeighborhood (hx : x ∈ S) :
    graphBall G x l ⊆ graphNeighborhood G S l :=
  Finset.subset_biUnion_of_mem (fun x ↦ graphBall G x l) hx

/-- A region lies in each of its neighbourhoods. -/
theorem subset_graphNeighborhood : S ⊆ graphNeighborhood G S l := fun x hx ↦
  mem_graphNeighborhood.mpr ⟨x, hx, by simp⟩

/-- Neighbourhoods grow with the region. -/
theorem graphNeighborhood_mono_left (h : S ⊆ T) :
    graphNeighborhood G S l ⊆ graphNeighborhood G T l :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

variable (G S) in
/-- Neighbourhoods grow with the radius. -/
theorem graphNeighborhood_mono : Monotone (graphNeighborhood G S) := fun _ _ h ↦
  Finset.biUnion_mono fun x _ ↦ graphBall_mono G x h

/-- The ball of radius `m` about a site of `N_l(S)` lies in `N_{l + m}(S)`. Source: area law,
`09-amplification.tex`, lines 232–234. -/
theorem graphBall_subset_graphNeighborhood_add (hx : x ∈ graphNeighborhood G S l) (m : ℕ) :
    graphBall G x m ⊆ graphNeighborhood G S (l + m) := by
  intro y hy
  obtain ⟨s, hs, hd⟩ := mem_graphNeighborhood.mp hx
  refine mem_graphNeighborhood.mpr ⟨s, hs, ?_⟩
  simpa only [Nat.cast_add] using G.edist_triangle.trans (add_le_add hd (mem_graphBall.mp hy))

/-- **Neighbourhoods compose by adding radii**: `N_m(N_l(S)) ⊆ N_{l + m}(S)`. -/
theorem graphNeighborhood_graphNeighborhood_subset :
    graphNeighborhood G (graphNeighborhood G S l) m ⊆ graphNeighborhood G S (l + m) :=
  Finset.biUnion_subset.mpr fun _ hx ↦ graphBall_subset_graphNeighborhood_add hx m

/-- **Neighbourhoods grow one step at a time**: `N_{l + 1}(S) = N_1(N_l(S))`. -/
theorem graphNeighborhood_succ :
    graphNeighborhood G S (l + 1) = graphNeighborhood G (graphNeighborhood G S l) 1 := by
  refine subset_antisymm (fun y hy ↦ ?_) graphNeighborhood_graphNeighborhood_subset
  obtain ⟨x, hx, p, hp⟩ := mem_graphNeighborhood_iff_exists_walk.mp hy
  cases h : p.reverse with
  | nil =>
    exact subset_graphNeighborhood (subset_graphNeighborhood hx)
  | @cons _ z _ hyz q =>
    have hq : q.length ≤ l := by
      have := congrArg SimpleGraph.Walk.length h
      rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_cons] at this
      omega
    refine mem_graphNeighborhood_iff_exists_walk.mpr ⟨z, ?_, .cons hyz.symm .nil, by simp⟩
    exact mem_graphNeighborhood_iff_exists_walk.mpr ⟨x, hx, q.reverse, by simpa using hq⟩

/-! ### Separated regions -/

variable (G) in
/-- Two regions are separated by `s` in the graph `G` when every site of the first is at graph
distance larger than `s` from every site of the second. -/
def IsGraphSeparated (S T : Finset V) (s : ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ T, (s : ℕ∞) < G.edist x y

omit [Fintype V] [DecidableEq V] in
/-- Separation is symmetric. -/
theorem IsGraphSeparated.symm {s : ℕ} (h : IsGraphSeparated G S T s) :
    IsGraphSeparated G T S s :=
  fun y hy x hx ↦ G.edist_comm ▸ h x hx y hy

/-- A site of `T` lies outside the neighbourhood of radius `s` of a region separated from `T`
by `s`. -/
theorem IsGraphSeparated.notMem_graphNeighborhood {s : ℕ} (h : IsGraphSeparated G S T s)
    (hy : y ∈ T) : y ∉ graphNeighborhood G S s := fun hmem ↦ by
  obtain ⟨x, hx, hxy⟩ := mem_graphNeighborhood.mp hmem
  exact (h x hx y hy).not_ge hxy

/-- Regions separated by `2l` have disjoint neighbourhoods of radius `l`. -/
theorem IsGraphSeparated.disjoint_graphNeighborhood (h : IsGraphSeparated G S T (2 * l)) :
    Disjoint (graphNeighborhood G S l) (graphNeighborhood G T l) := by
  rw [Finset.disjoint_left]
  intro z hzS hzT
  obtain ⟨x, hx, hxz⟩ := mem_graphNeighborhood.mp hzS
  obtain ⟨y, hy, hyz⟩ := mem_graphNeighborhood.mp hzT
  refine (h x hx y hy).not_ge ?_
  calc G.edist x y ≤ G.edist x z + G.edist z y := G.edist_triangle
    _ ≤ l + l := add_le_add hxz (by rwa [G.edist_comm])
    _ = ((2 * l : ℕ) : ℕ∞) := by push_cast; ring

/-- A neighbourhood has at most `|S| K` sites when each ball of its radius about a site of `S`
has at most `K` sites. -/
theorem card_graphNeighborhood_le {K : ℕ} (hBall : ∀ x ∈ S, (graphBall G x l).card ≤ K) :
    (graphNeighborhood G S l).card ≤ S.card * K :=
  Finset.card_biUnion_le_card_mul _ _ _ hBall

/-- **Labels anchored near a region.** If each site anchors at most `μ` labels and each ball of
radius `l` about a site of `S` has at most `K` sites, at most `|S| K μ` labels have their anchor
in `N_l(S)`. Source: area law, `09-amplification.tex`, line 228. -/
theorem card_filter_mem_graphNeighborhood_le {κ : Type*} [Fintype κ] (a : κ → V) {μ K : ℕ}
    (hfiber : ∀ x, (Finset.univ.filter fun i ↦ a i = x).card ≤ μ)
    (hBall : ∀ x ∈ S, (graphBall G x l).card ≤ K) :
    (Finset.univ.filter fun i ↦ a i ∈ graphNeighborhood G S l).card ≤ S.card * K * μ := by
  classical
  have hsub : (Finset.univ.filter fun i ↦ a i ∈ graphNeighborhood G S l) ⊆
      (graphNeighborhood G S l).biUnion fun x ↦ Finset.univ.filter fun i ↦ a i = x := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨a i, (Finset.mem_filter.mp hi).2, by simp⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le_card_mul _ _ _
    fun x _ ↦ hfiber x).trans ?_)
  exact Nat.mul_le_mul_right μ (card_graphNeighborhood_le hBall)

end Neighborhood

/-! ### The graph distance as an extended pseudometric -/

omit [Fintype V] in
open scoped ENNReal in
/-- The extended graph distance, read in `ℝ≥0∞` through the inclusion of `ℕ∞`, as an extended
pseudometric on the sites. Sites of different components are at infinite distance. It is not an
instance; `letI := graphPseudoEMetricSpace G` installs it for a given graph.
Source: area law, `09-amplification.tex`, lines 146–160. -/
@[instance_reducible]
noncomputable def graphPseudoEMetricSpace (G : SimpleGraph V) : PseudoEMetricSpace V :=
  .ofEDist (fun x y ↦ (G.edist x y : ℝ≥0∞))
    (fun x ↦ by simp only [G.edist_self, ENat.toENNReal_zero])
    (fun x y ↦ by rw [G.edist_comm])
    (fun x y z ↦ by
      simpa only [ENat.toENNReal_add] using ENat.toENNReal_mono G.edist_triangle)

omit [Fintype V] in
open scoped ENNReal in
@[simp] theorem graphPseudoEMetricSpace_edist (G : SimpleGraph V) (x y : V) :
    letI := graphPseudoEMetricSpace G
    edist x y = (G.edist x y : ℝ≥0∞) := rfl

omit [Fintype V] in
/-- Finite distance in the graph pseudometric is reachability. -/
@[simp] theorem graphPseudoEMetricSpace_edist_ne_top (G : SimpleGraph V) (x y : V) :
    letI := graphPseudoEMetricSpace G
    edist x y ≠ ⊤ ↔ G.Reachable x y := by
  simp only [graphPseudoEMetricSpace_edist, ENat.toENNReal_ne_top,
    G.edist_ne_top_iff_reachable]

omit [Fintype V] in
/-- The real graph pseudodistance is the natural graph distance. Both vanish between different
components, so a weighted kernel bound must check reachability separately. -/
@[simp] theorem graphPseudoEMetricSpace_edist_toReal (G : SimpleGraph V) (x y : V) :
    letI := graphPseudoEMetricSpace G
    (edist x y).toReal = (G.dist x y : ℝ) := by
  change (G.edist x y : ENNReal).toReal = ((G.edist x y).toNat : ℝ)
  induction G.edist x y using ENat.recTopCoe <;> simp

/-- The radius-`ℓ` neighbourhood of the sites outside `D ∪ C` and of the supports crossing `D`
avoids both cores when their radius-`ℓ + R` balls lie in the disjoint outer regions `D` and `C`
and every support has graph diameter at most `R`.
TNLean one-dimensional note, `part2a_mps_information.tex`, lines 419–425. -/
theorem reset_graphNeighborhood_disjoint_cores {κ : Type*} [DecidableEq V] [Fintype κ]
    (G : SimpleGraph V) (X : κ → Finset V) (R ℓ : ℕ)
    (hDiam : ∀ k, ∀ x ∈ X k, ∀ y ∈ X k, G.edist x y ≤ (R : ℕ∞))
    (D C R₀ C₀ : Finset V) (hDC : Disjoint D C)
    (hR : ∀ r ∈ R₀, graphBall G r (ℓ + R) ⊆ D)
    (hC : ∀ c ∈ C₀, graphBall G c (ℓ + R) ⊆ C) :
    let Q := (D ∪ C)ᶜ
    let crossing := crossingTerms X D
    let Z := crossing.biUnion X
    Disjoint (graphNeighborhood G (Q ∪ Z) ℓ) (R₀ ∪ C₀) := by
  intro Q crossing Z
  apply Finset.disjoint_left.mpr
  intro a ha hcore
  obtain ⟨z, hz, hza⟩ := mem_graphNeighborhood.mp ha
  have haz : G.edist a z ≤ (ℓ : ℕ∞) := by
    simpa only [SimpleGraph.edist_comm] using hza
  have hNear (y : V) (hzy : G.edist z y ≤ (R : ℕ∞)) : y ∈ graphBall G a (ℓ + R) :=
    mem_graphBall.mpr (by
      simpa only [Nat.cast_add] using
        (G.edist_triangle (u := a) (v := z) (w := y)).trans (add_le_add haz hzy))
  rcases Finset.mem_union.mp hz with hQ | hZ
  · rcases Finset.mem_union.mp hcore with haR | haC
    · exact Finset.mem_compl.mp hQ
        (Finset.mem_union_left C (hR a haR (hNear z (by simp))))
    · exact Finset.mem_compl.mp hQ
        (Finset.mem_union_right D (hC a haC (hNear z (by simp))))
  · obtain ⟨k, hk, hzX⟩ := Finset.mem_biUnion.mp hZ
    obtain ⟨⟨x, hx, hxD⟩, y, hy, hyD⟩ : (∃ x ∈ X k, x ∈ D) ∧ ∃ y ∈ X k, y ∉ D := by
      simpa only [crossing, crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and]
        using hk
    rcases Finset.mem_union.mp hcore with haR | haC
    · exact hyD (hR a haR (hNear y (hDiam k z hzX y hy)))
    · exact Finset.disjoint_left.mp hDC hxD (hC a haC (hNear x (hDiam k z hzX x hx)))

end ManyBody

namespace SimpleGraph

variable {V : Type*} {G : Type*} [Group G] [MulAction G V]

/-- **Site actions by graph automorphisms preserve distances.** If every `g` preserves
adjacency of the graph `Γ` on the sites, then `d(g • x, g • y) = d(x, y)`. For the
translations of a lattice this is the source's setting of a translationally invariant system
on a lattice: Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1603–1612. -/
theorem edist_smul_of_adj_iff (Γ : SimpleGraph V)
    (hΓ : ∀ (g : G) (x y : V), Γ.Adj (g • x) (g • y) ↔ Γ.Adj x y) (g : G) (x y : V) :
    Γ.edist (g • x) (g • y) = Γ.edist x y := by
  have hle : ∀ (g : G) (x y : V), Γ.edist (g • x) (g • y) ≤ Γ.edist x y := by
    intro g x y
    rcases eq_or_ne (Γ.edist x y) ⊤ with h | h
    · simp [h]
    · obtain ⟨w, hw⟩ := Γ.exists_walk_of_edist_ne_top h
      let φ : Γ →g Γ := ⟨(g • ·), (hΓ g _ _).mpr⟩
      rw [← hw]
      exact (Γ.edist_le (w.map φ)).trans_eq (by simp)
  refine le_antisymm (hle g x y) ?_
  simpa only [inv_smul_smul] using hle g⁻¹ (g • x) (g • y)

/-- The rotations of a ring of `n` sites, `x ↦ a + x`, are automorphisms of the cycle graph. -/
theorem cycleGraph_adj_smul {n : ℕ} [NeZero n] (a : Multiplicative (Fin n)) (x y : Fin n) :
    (cycleGraph n).Adj (a • x) (a • y) ↔ (cycleGraph n).Adj x y := by
  change (cycleGraph n).Adj (a.toAdd + x) (a.toAdd + y) ↔ _
  simp only [cycleGraph_adj', add_sub_add_left_eq_sub]


end SimpleGraph

namespace SimpleGraph

variable {V : Type*} {Γ : SimpleGraph V} {n R : ℕ}

/-- One step of the triangle inequality: crossing an edge changes the circular displacement
from a fixed site by at most \(R\). -/
private theorem natAbs_valMinAbs_sub_le_add_of_adj (π : V → ZMod n)
    (hπ : ∀ u v, Γ.Adj u v → (π v - π u).valMinAbs.natAbs ≤ R)
    (u w x : V) (h : Γ.Adj u w) :
    (π w - π x).valMinAbs.natAbs ≤ (π u - π x).valMinAbs.natAbs + R := by
  simpa only [add_comm (π u - π x) (π w - π u), sub_add_sub_cancel] using
    (ZMod.natAbs_valMinAbs_add_le (π u - π x) (π w - π u)).trans
      ((Int.natAbs_add_le _ _).trans (Nat.add_le_add_left (hπ u w h) _))

/-- Accumulating the one-edge step along a walk: the circular displacement grows by at most
\(R\) times the length of the walk. -/
private theorem natAbs_valMinAbs_sub_le_add_length_mul (π : V → ZMod n)
    (hπ : ∀ u v, Γ.Adj u v → (π v - π u).valMinAbs.natAbs ≤ R)
    (x : V) {u y : V} (p : Γ.Walk u y) :
    (π y - π x).valMinAbs.natAbs ≤
      (π u - π x).valMinAbs.natAbs + R * p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have hstep := natAbs_valMinAbs_sub_le_add_of_adj π hπ _ _ x h
    rw [SimpleGraph.Walk.length_cons, Nat.mul_succ]
    omega

/-- If each edge changes a cell coordinate by at most the positive integer \(R\), its
circular displacement is at most \(R\) times the graph distance. -/
theorem natAbs_valMinAbs_sub_le_edist (hR : 0 < R) (π : V → ZMod n)
    (hπ : ∀ u v, Γ.Adj u v → (π v - π u).valMinAbs.natAbs ≤ R) (x y : V) :
    ((π y - π x).valMinAbs.natAbs : ℕ∞) ≤ (R : ℕ∞) * Γ.edist x y := by
  rcases eq_or_ne (Γ.edist x y) ⊤ with h | h
  · simp [h, hR.ne']
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
    rw [← hp]
    have hw := natAbs_valMinAbs_sub_le_add_length_mul π hπ x p
    simp only [sub_self, ZMod.valMinAbs_zero, Int.natAbs_zero, zero_add] at hw
    exact_mod_cast hw


section Spacing

open ZMod

/-- The separated coordinates give graph separation for the same finite orbit.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem edist_pow_mul_ge_of_near {V Γ : Type*} [Group Γ] [MulAction Γ V]
    {n L m : ℕ} [NeZero n] (hL : 0 < L) (hn : 2 * (m + 1) * L ≤ n)
    (G : SimpleGraph V) (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1) (x y : V)
    (hnear : (π y - π x).valMinAbs.natAbs ≤ L / 2)
    {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    ((L / 2 : ℕ) : ℕ∞) ≤ G.edist x (e ^ (k * L) • y) := by
  have hkL : L ≤ k * L := Nat.le_mul_of_pos_left L hk
  have hkn : k * L + L ≤ n := by nlinarith [Nat.mul_le_mul_right L hkm]
  have hc := natAbs_valMinAbs_add_ge_of_near hL hkL hkn (π y - π x) hnear
  have hd := SimpleGraph.natAbs_valMinAbs_sub_le_edist (by decide : 0 < (1 : ℕ))
    π hπ x (e ^ (k * L) • y)
  rw [coordinate_pow_smul π e he] at hd
  have heq : π y - π x + ((k * L : ℕ) : ZMod n) =
      π y + ((k * L : ℕ) : ZMod n) - π x := by abel
  rw [heq] at hc
  simpa only [Nat.cast_one, one_mul] using (show
    ((L / 2 : ℕ) : ℕ∞) ≤
      ((π y + ((k * L : ℕ) : ZMod n) - π x).valMinAbs.natAbs : ℕ∞) by
        exact_mod_cast hc).trans hd

end Spacing

end SimpleGraph
