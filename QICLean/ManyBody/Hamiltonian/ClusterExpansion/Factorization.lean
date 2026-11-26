/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ClusterExpansion.Factorization
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.ManyBody.Sites.Placement.Basic

/-!
# The cluster expansion of an interaction: supports and commutation

For an interaction `Φ` whose term `h_k` acts on the region `T k`, the operator `E_C` of a
set `C` of terms acts on `⋃_{k ∈ C} T k`, and terms that are not adjacent in the overlap graph
`SimpleGraph.overlapGraph T` commute. Hence the truncated operator `ρ(β, l)` of the overlap
graph is a sum, over the sets of terms with no large cluster, of products of commuting
operators each acting on the sites of one cluster (Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1108–1110 and 1268–1269), and a retained sum over a set of labels acts on
the union of their supports (ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013).

## Main results

* `ManyBody.ClusterExpansion.clusterOp_mem_supportedOperators`.
* `ManyBody.ClusterExpansion.commute_of_not_adj_overlapGraph`.
* `ManyBody.ClusterExpansion.truncatedExp_eq_sum_noncommProd_clusters_overlapGraph`.
* `ManyBody.ClusterExpansion.sum_retained_clusterOp_mem_supportedOperators`.

Moved from TNLean (`e113e005`): the section on supports of
`TNLean/Lattice/ClusterExpansion/ClusterFactorization.lean` and `RetainedClusterSupport.lean`.
Changes: the terms are those of an interaction `Φ : Interaction X T` on any finite basis types,
and `isSupportedOn_sum_retained_clusterOp` is stated as membership in `supportedOperators`.
-/

open Finset SimpleGraph _root_.ClusterExpansion

namespace ManyBody

namespace ClusterExpansion

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} [DecidableEq κ] {T : κ → Finset V}

/-- **`E_C` acts on the sites of the terms of `C`.** Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1268–1269. -/
theorem clusterOp_mem_supportedOperators (Φ : Interaction X T) (C : Finset κ) (β : ℝ) :
    clusterOp Φ.term C β ∈ supportedOperators X (C.biUnion T) := by
  refine sum_mem fun D hD ↦ SMulMemClass.smul_mem _ (exp_mem_supportedOperators ?_)
  refine neg_mem (Submodule.smul_of_tower_mem
    (Subalgebra.toSubmodule (supportedOperators X _).toSubalgebra) β (sum_mem fun k hk ↦ ?_))
  exact supportedOperators_mono (subset_biUnion_of_mem T (mem_powerset.1 hD hk)) (Φ.mem k)

omit [DecidableEq κ] in
/-- **Terms that do not overlap commute.** Two terms that are not adjacent in the overlap graph
are equal or act on disjoint regions, so they commute. This discharges the commutation
hypothesis of the cluster products. -/
theorem commute_of_not_adj_overlapGraph (Φ : Interaction X T) :
    ∀ j k, ¬ (overlapGraph T).Adj j k → Commute (Φ.term j) (Φ.term k) := by
  intro j k hjk
  by_cases hjk' : j = k
  · subst hjk'
    exact Commute.refl _
  refine commute_of_mem_supportedOperators_of_disjoint (Φ.mem j) (Φ.mem k) ?_
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  exact fun hne ↦ hjk ⟨hjk', hne⟩

open Classical in
/-- **`ρ(β, l)` as a sum of products over clusters, for an interaction** (Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1108–1110). With the clusters of the overlap
graph, `ρ(β, l) = ∑_A ∏_{C} E_C` over the sets `A` of terms with no large cluster, and each
`E_C` acts on `⋃_{k ∈ C} T k` (`clusterOp_mem_supportedOperators`). -/
theorem truncatedExp_eq_sum_noncommProd_clusters_overlapGraph [Fintype κ]
    (large : Finset κ → Prop) (Φ : Interaction X T) (β : ℝ) :
    truncatedExp (overlapGraph T) large Φ.term β =
      ∑ A with NoLargeCluster (overlapGraph T) large A,
        (clusters (overlapGraph T) A).noncommProd (fun C ↦ clusterOp Φ.term C β)
          (pairwise_commute_clusterOp_clusters _ (commute_of_not_adj_overlapGraph Φ) A β) :=
  truncatedExp_eq_sum_noncommProd_clusters _ large (commute_of_not_adj_overlapGraph Φ) β

open Classical in
/-- The retained sum over a set `B` of labels acts on the union of the supports of the labels
of `B`. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem sum_retained_clusterOp_mem_supportedOperators [Fintype κ] (G : SimpleGraph κ)
    [DecidableRel G.Adj]
    (large : Finset κ → Prop) (Φ : Interaction X T) (B : Finset κ) (β : ℝ) :
    ∑ A ∈ B.powerset with NoLargeCluster G large A, clusterOp Φ.term A β ∈
      supportedOperators X (B.biUnion T) := by
  refine sum_mem fun A hA ↦ ?_
  exact supportedOperators_mono (biUnion_subset_biUnion_of_subset_left T
    (mem_powerset.mp (mem_filter.mp hA).1)) (clusterOp_mem_supportedOperators Φ A β)

end ClusterExpansion

end ManyBody
