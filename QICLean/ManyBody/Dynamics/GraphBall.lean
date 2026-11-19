/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Group.Action.TypeTags
import QICLean.Algebra.ZModDisplacement
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Real.Basic
import Mathlib.Order.SuccPred.ENat
import QICLean.ManyBody.Sites.Cut

/-!
# Graph balls as regions

For a graph `G` on the sites, the closed ball `N_l(a) = {x : d_G(a, x) ≤ l}` of natural radius
`l` about a site `a` is Mathlib's open ball `SimpleGraph.ball a (l + 1)`. Statements about
regions take finite sets of sites, so `ManyBody.graphBall G a l` is that ball as a `Finset`;
`ManyBody.coe_graphBall` identifies the two.

The balls increase with the radius, a site at infinite distance lies in none of them, and on a
finite graph they stabilize on the connected component of the centre. Membership is measured by
the extended distance, so sites of other components never enter a ball, although their natural
distance has the value zero.

If two outer regions are disjoint and every ball of radius `ℓ + R` about either of two cores
lies in its outer region, then the radius-`ℓ` neighbourhood of the remaining sites and of the
supports crossing the first outer region avoids both cores, for supports of graph diameter at
most `R`.

Moved from TNLean, `TNLean/Circuit/LiebRobinson/GraphLocalization.lean` (the definition) and
`GraphBallStabilization.lean` at commit `71c1185e9352a3b5237b37a6840640751da6ca2d`. Changes:
the ball is defined from `SimpleGraph.ball` instead of as a filter of the sites. The
separation lemmas are moved from `TNLean/Circuit/LiebRobinson/SupportSeparation.lean` at the
same commit, with `ManyBody.crossingTerms` in place of `Entropy.crossingTerms`.

## Main definitions

* `ManyBody.graphBall` — the closed graph ball of natural radius, as a region.

## Main results

* `ManyBody.coe_graphBall`, `ManyBody.mem_graphBall` — the ball and its membership.
* `ManyBody.exists_graphBall_eq_reachable` — the balls stabilize on the component of the
  centre.
* `ManyBody.graphBall_subset_of_finite_distance_margin` — a real distance margin contains the
  balls of smaller radius.
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
    Disjoint ((Q ∪ Z).biUnion fun z ↦ graphBall G z ℓ) (R₀ ∪ C₀) := by
  intro Q crossing Z
  apply Finset.disjoint_left.mpr
  intro a ha hcore
  obtain ⟨z, hz, hza⟩ := Finset.mem_biUnion.mp ha
  have haz : G.edist a z ≤ (ℓ : ℕ∞) := by
    simpa only [SimpleGraph.edist_comm] using (mem_graphBall.mp hza)
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
  have hc := natAbs_valMinAbs_add_mul_ge_of_near hL hn (π y - π x) hnear hk hkm
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
