/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Order.SuccPred.ENat

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

Moved from TNLean, `TNLean/Circuit/LiebRobinson/GraphLocalization.lean` (the definition) and
`GraphBallStabilization.lean` at commit `71c1185e9352a3b5237b37a6840640751da6ca2d`. Changes:
the ball is defined from `SimpleGraph.ball` instead of as a filter of the sites.

## Main definitions

* `ManyBody.graphBall` — the closed graph ball of natural radius, as a region.

## Main results

* `ManyBody.coe_graphBall`, `ManyBody.mem_graphBall` — the ball and its membership.
* `ManyBody.exists_graphBall_eq_reachable` — the balls stabilize on the component of the
  centre.
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

end ManyBody
