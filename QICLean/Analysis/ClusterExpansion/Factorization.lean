/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import QICLean.Analysis.ClusterExpansion.Truncation
import QICLean.Analysis.MandatoryExponentialNorm

/-!
# The cluster expansion as a sum of products over clusters

When terms that are not adjacent commute, the words with letter set `A` sum to the operator
`E_A`, and `E_A` factors as the product of `E_C` over the clusters `C` of `A`; so `ρ(β, l)` is a
sum over the sets of terms with no large cluster of products over their clusters (Hastings,
`proj3new.tex`, lines 1108–1110 and 1268–1269). This file proves that factorization, groups the
retained sum over mutually separated sets of terms and by the component meeting a given term
(ALVV, arXiv:1602.08828v2, `eq:rho-expansion`), and writes the discarded part through
inclusion and exclusion over mandatory labels and windows (ALVV, `thm:cluster-approx`).
The statements that the factors act on the sites of their terms are not part of this file.

Moved from TNLean (`e113e005`): `TNLean/Lattice/ClusterExpansion/ClusterFactorization.lean`
(without its section on supports), `SeparatedClusterSums.lean`, `CrossingComponentSum.lean`,
`MandatoryLabels.lean` and `WindowInclusionExclusion.lean`, in the namespace `ClusterExpansion`.
-/

/-!
## The truncated operator as a sum of products over clusters

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1090–1114), observes that "each term in
`ρ(β, l_proj)` is a product of operators, each operator acting on the sites within a given
cluster", and in the matrix product construction (lines 1256–1279) uses that "the sum of all terms
which include a given cluster is some operator acting on the sites in the cluster". This file
proves the algebraic content of these two remarks.

The terms are labelled by `κ`, and a graph `G` on `κ` records which terms overlap; the product
results assume that terms that do not overlap commute. For a set `A` of terms let
`E_A = clusterOp h A β` be the sum of the terms of the power series of `e^{-βH}` whose set of
letters is exactly `A`; by inclusion and exclusion,
`E_A = ∑_{D ⊆ A} (-1)^{|A \ D|} e^{-β H_D}`. Then

* `ρ(β, l) = ∑_A E_A`, the sum over the sets `A` of terms none of whose clusters is large;
* `E_{A ∪ B} = E_A E_B` when `A` and `B` are disjoint and the terms of `A` commute with those of
  `B`;
* hence `E_A` is the product, in any order, of `E_C` over the clusters `C` of `A`, and
  `ρ(β, l) = ∑_A ∏_{C cluster of A} E_C`.

That `E_C` acts on the sites of the terms of `C`, and that terms not adjacent in the overlap
graph commute, are statements about operators on sites and are not part of this file.

### Main results

* `ClusterExpansion.clusterOp`: the operator `E_A`.
* `ClusterExpansion.hasSum_words_clusterOp`: `E_A` as the sum of the words whose
  set of letters is `A`, weighted by `(-β)^n / n!`.
* `ClusterExpansion.truncatedExp_eq_sum_clusterOp`: `ρ(β, l) = ∑_A E_A` over the
  sets of terms with no large cluster.
* `ClusterExpansion.clusterOp_union`: `E_{A ∪ B} = E_A E_B` for disjoint sets of
  mutually commuting terms.
* `ClusterExpansion.clusters`, `biUnion_clusters`: the clusters of a set of terms
  partition it.
* `ClusterExpansion.clusterOp_eq_noncommProd_clusters`: `E_A` as the product of the
  `E_C` over the clusters `C` of `A`.
* `ClusterExpansion.truncatedExp_eq_sum_noncommProd_clusters`:
  `ρ(β, l) = ∑_A ∏_{C} E_C`.

### References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, lines 1090–1114 and 1256–1279.
-/

open Finset Matrix
open scoped Function

namespace ClusterExpansion

section Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- The operator `E_A`: the sum of the terms of the power series of `e^{-βH}`, `H = ∑_k h_k`,
whose set of letters is exactly `A`. By inclusion and exclusion over the letters it is
`∑_{D ⊆ A} (-1)^{|A \ D|} e^{-β H_D}` with `H_D = ∑_{k ∈ D} h_k`, the definition used here.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1268–1269. -/
noncomputable def clusterOp (h : κ → Matrix ι ι ℂ) (A : Finset κ) (β : ℝ) : Matrix ι ι ℂ :=
  ∑ D ∈ A.powerset, (-1 : ℂ) ^ #(A \ D) • NormedSpace.exp (-(β • ∑ k ∈ D, h k))

/-- `E_A` is the cluster part with the boundary `Aᶜ`: the words containing every term of `A` and
no other term. -/
theorem clusterOp_eq_clusterPart [Fintype κ] (h : κ → Matrix ι ι ℂ) (A : Finset κ) (β : ℝ) :
    clusterOp h A β = clusterPart (∑ k, h k) h Aᶜ A β := by
  rw [clusterPart_eq_sum_powerset, clusterOp]
  refine Finset.sum_congr rfl fun E hE ↦ ?_
  have h0 : ∑ k, h k - ∑ k ∈ Aᶜ, h k - ∑ k ∈ A, h k = 0 := by
    rw [← Finset.sum_add_sum_compl A h]
    abel
  rw [h0, smul_zero, zero_add, ← Finset.smul_sum, card_sdiff_of_subset (mem_powerset.1 hE)]

/-- **`E_A` as a word series.** The words of length `n` whose set of letters is exactly `A`,
weighted by `(-β)^n / n!`, sum to `E_A`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1268–1269. -/
theorem hasSum_words_clusterOp [Fintype κ] (h : κ → Matrix ι ι ℂ) (A : Finset κ) (β : ℝ) :
    HasSum (fun n ↦ ((-β) ^ n / n.factorial : ℝ) •
        ∑ w : Fin n → κ with univ.image w = A, (List.ofFn fun i ↦ h (w i)).prod)
      (clusterOp h A β) := by
  rw [clusterOp_eq_clusterPart]
  convert hasSum_words_clusterPart rfl
    (disjoint_left.2 fun _ h h' ↦ mem_compl.1 h h') β using 4 with n
  refine Finset.filter_congr fun w _ ↦ ?_
  constructor
  · rintro rfl
    exact ⟨Subset.rfl, disjoint_left.2 fun _ h h' ↦ mem_compl.1 h' h⟩
  · rintro ⟨h1, h2⟩
    refine Subset.antisymm (fun x hx ↦ ?_) h1
    by_contra hxA
    exact disjoint_left.1 h2 hx (mem_compl.2 hxA)

/-- `E_∅ = 1`. -/
@[simp]
theorem clusterOp_empty (h : κ → Matrix ι ι ℂ) (β : ℝ) : clusterOp h ∅ β = 1 := by
  simp [clusterOp]

end Operator

section Truncation

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (G : SimpleGraph κ) [DecidableRel G.Adj] (large : Finset κ → Prop)

open Classical in
/-- **`ρ(β, l)` as a sum over sets of terms.** The power series of `ρ(β, l)` sums to `∑_A E_A`,
the sum over the sets `A` of terms none of whose clusters is large. The words are grouped by
their set of letters. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1103–1107. -/
theorem hasSum_truncatedExpTerm_clusterOp (h : κ → Matrix ι ι ℂ) (β : ℝ) :
    HasSum (truncatedExpTerm G large h β)
      (∑ A with NoLargeCluster G large A, clusterOp h A β) := by
  have key : ∀ n, truncatedExpTerm G large h β n =
      ∑ A with NoLargeCluster G large A, ((-β) ^ n / n.factorial : ℝ) •
        ∑ w : Fin n → κ with univ.image w = A, (List.ofFn fun i ↦ h (w i)).prod := by
    intro n
    rw [truncatedExpTerm, ← Finset.smul_sum]
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun w : Fin n → κ ↦ univ.image w)
      (t := {A | NoLargeCluster G large A}) (fun w hw ↦ by simpa using hw)]
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    rw [Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun w _ ↦ ?_) fun _ _ ↦ rfl
    constructor
    · exact fun hw ↦ hw.2
    · intro hw
      refine ⟨?_, hw⟩
      rw [hw]
      simpa using hA
  rw [funext key]
  exact hasSum_sum fun A _ ↦ hasSum_words_clusterOp h A β

open Classical in
/-- **`ρ(β, l) = ∑_A E_A`**, the sum over the sets `A` of terms none of whose clusters is large.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1103–1107. -/
theorem truncatedExp_eq_sum_clusterOp (h : κ → Matrix ι ι ℂ) (β : ℝ) :
    truncatedExp G large h β = ∑ A with NoLargeCluster G large A, clusterOp h A β :=
  (hasSum_truncatedExpTerm_clusterOp G large h β).tsum_eq

end Truncation

section Factorization

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- **`E_{A ∪ B} = E_A E_B`** for disjoint sets `A`, `B` of terms such that every term of `A`
commutes with every term of `B`. The subsets of `A ∪ B` are the unions `D₁ ∪ D₂` with `D₁ ⊆ A`,
`D₂ ⊆ B`, and `e^{-β (H_{D₁} + H_{D₂})} = e^{-β H_{D₁}} e^{-β H_{D₂}}`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1108–1110. -/
theorem clusterOp_union (h : κ → Matrix ι ι ℂ) {A B : Finset κ} (hAB : Disjoint A B)
    (hc : ∀ j ∈ A, ∀ k ∈ B, Commute (h j) (h k)) (β : ℝ) :
    clusterOp h (A ∪ B) β = clusterOp h A β * clusterOp h B β := by
  rw [clusterOp, clusterOp, clusterOp, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p ↦ p.1 ∪ p.2) (fun D ↦ (D ∩ A, D ∩ B)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_product, mem_powerset] at hp ⊢
    exact union_subset_union hp.1 hp.2
  · intro D hD
    simp only [mem_product, mem_powerset] at hD ⊢
    exact ⟨inter_subset_right, inter_subset_right⟩
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    obtain ⟨D₁, D₂⟩ := p
    have h1 : D₂ ∩ A = ∅ :=
      disjoint_iff_inter_eq_empty.1 (hAB.symm.mono_left hp.2)
    have h2 : D₁ ∩ B = ∅ := disjoint_iff_inter_eq_empty.1 (hAB.mono_left hp.1)
    simp only [union_inter_distrib_right, h1, h2, union_empty, empty_union,
      inter_eq_left.2 hp.1, inter_eq_left.2 hp.2]
  · intro D hD
    simp only [mem_powerset] at hD
    simp only [← inter_union_distrib_left, inter_eq_left.2 hD]
  · rintro ⟨D₁, D₂⟩ hp
    simp only [mem_product, mem_powerset] at hp
    have hD : Disjoint D₁ D₂ := (hAB.mono_left hp.1).mono_right hp.2
    have hcD : Commute (-(β • ∑ k ∈ D₁, h k)) (-(β • ∑ k ∈ D₂, h k)) :=
      (((Commute.sum_left _ _ _ fun j hj ↦ Commute.sum_right _ _ _ fun k hk ↦
        hc j (hp.1 hj) k (hp.2 hk)).smul_left β).smul_right β).neg_left.neg_right
    have hcard : #((A ∪ B) \ (D₁ ∪ D₂)) = #(A \ D₁) + #(B \ D₂) := by
      rw [card_sdiff_of_subset (union_subset_union hp.1 hp.2), card_sdiff_of_subset hp.1,
        card_sdiff_of_subset hp.2, card_union_of_disjoint hAB, card_union_of_disjoint hD]
      have := card_le_card hp.1
      have := card_le_card hp.2
      omega
    simp only
    rw [smul_mul_smul_comm, ← pow_add, ← hcard, ← Matrix.exp_add_of_commute _ _ hcD,
      sum_union hD, smul_add, neg_add]

/-- Disjoint sets of mutually commuting terms give commuting operators `E_A`, `E_B`. -/
theorem commute_clusterOp (h : κ → Matrix ι ι ℂ) {A B : Finset κ} (hAB : Disjoint A B)
    (hc : ∀ j ∈ A, ∀ k ∈ B, Commute (h j) (h k)) (β : ℝ) :
    Commute (clusterOp h A β) (clusterOp h B β) := by
  change _ * _ = _ * _
  rw [← clusterOp_union h hAB hc, ← clusterOp_union h hAB.symm
    (fun k hk j hj ↦ (hc j hj k hk).symm), union_comm]

/-- **`E` of a union is the product over the parts.** For a family `S` of pairwise disjoint
sets of terms, with the terms of distinct members commuting, `E_{⋃S}` is the product, in any
order, of `E_C` over `C ∈ S`. -/
theorem clusterOp_biUnion (h : κ → Matrix ι ι ℂ) (S : Finset (Finset κ))
    (hS : (S : Set (Finset κ)).Pairwise fun C C' ↦
      Disjoint C C' ∧ ∀ j ∈ C, ∀ k ∈ C', Commute (h j) (h k)) (β : ℝ) :
    clusterOp h (S.biUnion id) β =
      S.noncommProd (fun C ↦ clusterOp h C β)
        (hS.mono' fun _ _ hCC' ↦ commute_clusterOp h hCC'.1 hCC'.2 β) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert C S hC ih =>
    have hS' : (S : Set (Finset κ)).Pairwise fun C C' ↦
        Disjoint C C' ∧ ∀ j ∈ C, ∀ k ∈ C', Commute (h j) (h k) :=
      hS.mono (coe_subset.2 (subset_insert C S))
    have hCS : ∀ C' ∈ S, Disjoint C C' ∧ ∀ j ∈ C, ∀ k ∈ C', Commute (h j) (h k) :=
      fun C' hC' ↦ hS (mem_insert_self C S) (mem_insert_of_mem hC')
        (fun hCC' ↦ hC (hCC' ▸ hC'))
    rw [noncommProd_insert_of_notMem _ _ _ _ hC, biUnion_insert, id,
      clusterOp_union h ((disjoint_biUnion_right C S id).2 fun C' hC' ↦ (hCS C' hC').1), ih hS']
    intro j hj k hk
    obtain ⟨C', hC', hkC'⟩ := mem_biUnion.1 hk
    exact (hCS C' hC').2 j hj k hkC'

end Factorization

section Clusters

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (G : SimpleGraph κ) [DecidableRel G.Adj]

open Classical in
/-- The clusters of a set `A` of terms: the connected subsets of `A` to which no other term of `A`
is adjacent. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1096–1102. -/
noncomputable def clusters (A : Finset κ) : Finset (Finset κ) :=
  {C ∈ A.powerset | IsCluster G A C}

theorem mem_clusters {A C : Finset κ} : C ∈ clusters G A ↔ IsCluster G A C := by
  classical
  simp only [clusters, mem_filter, mem_powerset, and_iff_right_iff_imp]
  exact fun hC ↦ hC.1

/-- Every term of `A` lies in a cluster of `A`: a connected subset of `A` containing it with the
largest number of terms. -/
theorem exists_isCluster_mem {A : Finset κ} {k : κ} (hk : k ∈ A) :
    ∃ C, IsCluster G A C ∧ k ∈ C := by
  classical
  set T : Finset (Finset κ) := {C ∈ A.powerset | k ∈ C ∧ (G.induce (C : Set κ)).Connected}
  have hT : ({k} : Finset κ) ∈ T := by
    simp only [T, mem_filter, mem_powerset, singleton_subset_iff, mem_singleton, true_and]
    rw [coe_singleton]
    exact ⟨hk, (SimpleGraph.connected_iff _).2 ⟨.of_subsingleton, ⟨⟨k, rfl⟩⟩⟩⟩
  obtain ⟨C, hCT, hmax⟩ := Finset.exists_max_image T card ⟨_, hT⟩
  simp only [T, mem_filter, mem_powerset] at hCT
  refine ⟨C, ⟨hCT.1, hCT.2.2, Finset.disjoint_left.2 fun j hjA hjB ↦ ?_⟩, hCT.2.1⟩
  obtain ⟨hjC, i, hi, hji⟩ := (mem_boundary G).1 hjB
  have hconn : (G.induce ((insert j C : Finset κ) : Set κ)).Connected := by
    have := SimpleGraph.connected_induce_union (G := G) hCT.2.2.preconnected
      (t := {j}) (.of_subsingleton) hi rfl hji.symm
    rwa [coe_insert, Set.insert_eq, Set.union_comm]
  have hmem : insert j C ∈ T := by
    simp only [T, mem_filter, mem_powerset]
    exact ⟨insert_subset hjA hCT.1, mem_insert_of_mem hCT.2.1, hconn⟩
  have := hmax _ hmem
  rw [card_insert_of_notMem hjC] at this
  omega

/-- **The clusters of `A` partition `A`.** -/
theorem biUnion_clusters (A : Finset κ) : (clusters G A).biUnion id = A := by
  refine Finset.Subset.antisymm (biUnion_subset.2 fun C hC ↦ ((mem_clusters G).1 hC).1)
    fun k hk ↦ ?_
  obtain ⟨C, hC, hkC⟩ := exists_isCluster_mem G hk
  exact mem_biUnion.2 ⟨C, (mem_clusters G).2 hC, hkC⟩

/-- Distinct clusters of `A` are disjoint, and no term of one is adjacent to a term of the
other. -/
theorem pairwise_clusters (A : Finset κ) :
    (clusters G A : Set (Finset κ)).Pairwise fun C C' ↦
      Disjoint C C' ∧ ∀ j ∈ C, ∀ k ∈ C', ¬ G.Adj j k := by
  intro C hC C' hC' hne
  rw [mem_coe, mem_clusters] at hC hC'
  have hd : Disjoint C C' := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    by_contra hn
    exact hne (eq_of_isCluster_of_inter_nonempty G hC hC' (nonempty_iff_ne_empty.2 hn))
  refine ⟨hd, fun j hj k hk hjk ↦ ?_⟩
  have hb : k ∈ boundary G C :=
    (mem_boundary G).2 ⟨Finset.disjoint_right.1 hd hk, j, hj, hjk.symm⟩
  exact Finset.disjoint_left.1 hC.2.2 (hC'.1 hk) hb

end Clusters

section ClusterProduct

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (G : SimpleGraph κ) [DecidableRel G.Adj] (large : Finset κ → Prop)

/-- The operators `E_C` of the clusters of `A` commute when non-overlapping terms commute. -/
theorem pairwise_commute_clusterOp_clusters {h : κ → Matrix ι ι ℂ}
    (hcomm : ∀ j k, ¬ G.Adj j k → Commute (h j) (h k)) (A : Finset κ) (β : ℝ) :
    (clusters G A : Set (Finset κ)).Pairwise
      (Commute on fun C ↦ clusterOp h C β) :=
  (pairwise_clusters G A).mono' fun _ _ hCC' ↦
    commute_clusterOp h hCC'.1 (fun j hj k hk ↦ hcomm j k (hCC'.2 j hj k hk)) β

/-- **`E_A` as a product over the clusters of `A`.** If terms that do not overlap commute, then
`E_A` is the product, in any order, of `E_C` over the clusters `C` of `A`; `E_C` is built only
from the terms of `C`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1108–1110 and
1258–1259. -/
theorem clusterOp_eq_noncommProd_clusters {h : κ → Matrix ι ι ℂ}
    (hcomm : ∀ j k, ¬ G.Adj j k → Commute (h j) (h k)) (A : Finset κ) (β : ℝ) :
    clusterOp h A β =
      (clusters G A).noncommProd (fun C ↦ clusterOp h C β)
        (pairwise_commute_clusterOp_clusters G hcomm A β) := by
  conv_lhs => rw [← biUnion_clusters G A]
  exact clusterOp_biUnion h _ ((pairwise_clusters G A).mono' fun _ _ hCC' ↦
    ⟨hCC'.1, fun j hj k hk ↦ hcomm j k (hCC'.2 j hj k hk)⟩) β

open Classical in
/-- **`ρ(β, l)` as a sum of products over clusters** (Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1108–1110). If terms that do not overlap commute, then
`ρ(β, l) = ∑_A ∏_{C} E_C`, the sum over the sets `A` of terms with no large cluster of the
product over the clusters `C` of `A`. -/
theorem truncatedExp_eq_sum_noncommProd_clusters {h : κ → Matrix ι ι ℂ}
    (hcomm : ∀ j k, ¬ G.Adj j k → Commute (h j) (h k)) (β : ℝ) :
    truncatedExp G large h β =
      ∑ A with NoLargeCluster G large A,
        (clusters G A).noncommProd (fun C ↦ clusterOp h C β)
          (pairwise_commute_clusterOp_clusters G hcomm A β) := by
  rw [truncatedExp_eq_sum_clusterOp]
  exact Finset.sum_congr rfl fun A _ ↦ clusterOp_eq_noncommProd_clusters G hcomm A β

end ClusterProduct


end ClusterExpansion

/-!
## Retained cluster sums over separated label supports

The factors in the separated expansion are actual finite sums of the existing exact-label
coefficients. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, source lines 1971–2013.
-/

open Finset

namespace ClusterExpansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph κ) [DecidableRel G.Adj]

open Classical in
/-- Exact factorization of the retained finite sum on two separated allowed label sets.
The factors are constructed by summing the existing coefficients over their respective supports.
Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, source lines 1971–2013. -/
theorem sum_retained_clusterOp_union_eq_mul (large : Finset κ → Prop)
    (h : κ → Matrix ι ι ℂ)
    (hcomm : ∀ j k, ¬ G.Adj j k → Commute (h j) (h k))
    {B C : Finset κ} (hBC : Disjoint B C)
    (hsep : ∀ b ∈ B, ∀ c ∈ C, ¬ G.Adj b c) (β : ℝ) :
    (∑ A ∈ (B ∪ C).powerset with NoLargeCluster G large A, clusterOp h A β) =
      (∑ A ∈ B.powerset with NoLargeCluster G large A, clusterOp h A β) *
        ∑ A ∈ C.powerset with NoLargeCluster G large A, clusterOp h A β := by
  classical
  have hsplit (A : Finset κ) (hA : A ⊆ B ∪ C) : (A ∩ B) ∪ (A ∩ C) = A := by
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hA]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun A ↦ (A ∩ B, A ∩ C)) (fun p ↦ p.1 ∪ p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨hAsub, hgood⟩ := mem_filter.mp hA
    have hg := (noLargeCluster_union_iff_of_no_adj G large
      (A := A ∩ B) (B := A ∩ C)
      (fun b hb c hc ↦ hsep b (mem_inter.mp hb).2 c (mem_inter.mp hc).2)).mp
        (by rwa [hsplit A (mem_powerset.mp hAsub)])
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr inter_subset_right, hg.1⟩,
      mem_filter.mpr ⟨mem_powerset.mpr inter_subset_right, hg.2⟩⟩
  · rintro ⟨A, D⟩ hAD
    simp only [mem_product, mem_filter, mem_powerset] at hAD ⊢
    exact ⟨union_subset_union hAD.1.1 hAD.2.1,
      (noLargeCluster_union_iff_of_no_adj G large
        (fun a ha d hd ↦ hsep a (hAD.1.1 ha) d (hAD.2.1 hd))).mpr ⟨hAD.1.2, hAD.2.2⟩⟩
  · exact fun A hA ↦ hsplit A (mem_powerset.mp (mem_filter.mp hA).1)
  · rintro ⟨A, D⟩ hAD
    simp only [mem_product, mem_filter, mem_powerset] at hAD
    have hDB : D ∩ B = ∅ := disjoint_iff_inter_eq_empty.mp (hBC.symm.mono_left hAD.2.1)
    have hAC : A ∩ C = ∅ := disjoint_iff_inter_eq_empty.mp (hBC.mono_left hAD.1.1)
    simp only [union_inter_distrib_right, hDB, hAC, inter_eq_left.mpr hAD.1.1,
      inter_eq_left.mpr hAD.2.1, union_empty, empty_union]
  · intro A hA
    rw [← clusterOp_union h ((hBC.mono_left inter_subset_right).mono_right inter_subset_right)
      (fun j hj k hk ↦ hcomm j k (hsep j (mem_inter.mp hj).2 k (mem_inter.mp hk).2)) β,
      hsplit A (mem_powerset.mp (mem_filter.mp hA).1)]

end ClusterExpansion

/-!
## The retained expansion grouped by the component containing a given label

The component and its remaining allowed labels are constructed from actual graph clusters.
This is the finite structural step in ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, source lines 1971–2013.
-/

open Finset

namespace ClusterExpansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph κ) [DecidableRel G.Adj]

private theorem no_adj_of_subset_exterior {C B : Finset κ}
    (hB : B ⊆ (C ∪ boundary G C)ᶜ) : ∀ c ∈ C, ∀ b ∈ B, ¬ G.Adj c b := by
  intro c hc b hb hcb
  have hbnot := Finset.mem_compl.mp (hB hb)
  have hbC : b ∉ C := fun h ↦ hbnot (mem_union_left _ h)
  exact hbnot (mem_union_right _ ((mem_boundary G).mpr ⟨hbC, c, hc, hcb.symm⟩))

private theorem sdiff_subset_exterior_of_isCluster {A C : Finset κ}
    (hC : IsCluster G A C) : A \ C ⊆ (C ∪ boundary G C)ᶜ := by
  intro x hx
  refine Finset.mem_compl.mpr fun h ↦ ?_
  exact (Finset.mem_union.mp h).elim (Finset.mem_sdiff.mp hx).2
    (fun hxB ↦ Finset.disjoint_left.mp hC.2.2 (Finset.mem_sdiff.mp hx).1 hxB)

open Classical in
/-- The retained supports containing a label are grouped by their unique component containing
that label. The remaining factor is the actual retained finite sum on the complement of the
component and its boundary. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`,
source lines 1971–2013. -/
theorem sum_retained_clusterOp_containing_eq (large : Finset κ → Prop)
    (h : κ → Matrix ι ι ℂ)
    (hcomm : ∀ j k, ¬ G.Adj j k → Commute (h j) (h k)) (p : κ) (β : ℝ) :
    (∑ A : Finset κ with NoLargeCluster G large A ∧ p ∈ A, clusterOp h A β) =
      ∑ C ∈ (univ : Finset (Finset κ)).filter (fun C : Finset κ ↦
          p ∈ C ∧ (G.induce (C : Set κ)).Connected ∧ ¬ large C),
        clusterOp h C β *
          ∑ B ∈ ((C ∪ boundary G C)ᶜ).powerset with NoLargeCluster G large B,
            clusterOp h B β := by
  classical
  let comp := fun A : Finset κ ↦ if hp : p ∈ A then
    (exists_isCluster_mem G hp).choose else ∅
  have hcomp {A : Finset κ} (hp : p ∈ A) : IsCluster G A (comp A) ∧ p ∈ comp A := by
    simpa only [comp, dite_eq_left hp] using (exists_isCluster_mem G hp).choose_spec
  have hcover {A : Finset κ} (hp : p ∈ A) : comp A ∪ (A \ comp A) = A :=
    Finset.union_sdiff_of_subset (hcomp hp).1.1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun A ↦ Sigma.mk (comp A) (A \ comp A))
    (fun t ↦ t.1 ∪ t.2) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    have hg := (mem_filter.mp hA).2
    have hc := hcomp hg.2
    have hext := sdiff_subset_exterior_of_isCluster G hc.1
    have hgoodB : NoLargeCluster G large (A \ comp A) :=
      ((noLargeCluster_union_iff_of_no_adj G large (no_adj_of_subset_exterior G hext)).mp
        (by rw [hcover hg.2]; exact hg.1)).2
    exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _, hc.2, hc.1.2.1, hg.1 _ hc.1⟩,
      mem_filter.mpr ⟨mem_powerset.mpr hext, hgoodB⟩⟩
  · rintro ⟨C, B⟩ hCB
    obtain ⟨hCmem, hBmem⟩ := mem_sigma.mp hCB
    have hc := (mem_filter.mp hCmem).2
    have hb := mem_filter.mp hBmem
    exact mem_filter.mpr ⟨mem_univ _,
      (noLargeCluster_union_iff_of_no_adj G large
        (no_adj_of_subset_exterior G (mem_powerset.mp hb.1))).mpr
          ⟨(noLargeCluster_iff_not_large_of_connected G large hc.2.1).mpr hc.2.2, hb.2⟩,
      mem_union_left _ hc.1⟩
  · exact fun A hA ↦ hcover (mem_filter.mp hA).2.2
  · rintro ⟨C, B⟩ hCB
    obtain ⟨hCmem, hBmem⟩ := mem_sigma.mp hCB
    have hc := (mem_filter.mp hCmem).2
    have hb := mem_powerset.mp (mem_filter.mp hBmem).1
    have hpc : p ∈ C ∪ B := mem_union_left _ hc.1
    have hcluster : IsCluster G (C ∪ B) C :=
      (isCluster_union_iff_of_no_adj G (no_adj_of_subset_exterior G hb)).mpr
        (.inl (isCluster_self_of_connected G hc.2.1))
    have heq : comp (C ∪ B) = C := eq_of_isCluster_of_inter_nonempty G (hcomp hpc).1
      hcluster ⟨p, mem_inter.mpr ⟨(hcomp hpc).2, hc.1⟩⟩
    have hd : Disjoint C B := Finset.disjoint_left.mpr fun x hxC hxB ↦
      Finset.mem_compl.mp (hb hxB) (mem_union_left _ hxC)
    simp only [heq, Finset.union_sdiff_cancel_left hd]
  · intro A hA
    have hp := (mem_filter.mp hA).2.2
    have hext := sdiff_subset_exterior_of_isCluster G (hcomp hp).1
    rw [← clusterOp_union h Finset.disjoint_sdiff
      (fun j hj k hk ↦ hcomm j k (no_adj_of_subset_exterior G hext j hj k hk)) β, hcover hp]

end ClusterExpansion

/-!
## Mandatory labels in the existing cluster expansion

The empty-boundary cluster part inherits the energy-normalized operator norm
bound. When the background is the full sum of the interactions, it is the sum
of the existing exact-support coefficients over supports containing the
required labels. The word-series identities are those
of Hastings, arXiv:cond-mat/0508554v3, source lines 1174–1177 and 1268–1269.

**Local fix (energy normalization and interaction labels):** these are
auxiliary results for a corrected interaction-label expansion related
to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`, lines 1270–1291 and 1935–1968.
The false printed spatial approximation estimate remains distinct; see
https://sirui-lu.com/TNLean/paper-gaps/alvv16_cluster_approximation.pdf. No spatial cut or matrix
product operator construction is concluded here.
-/

open Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ClusterExpansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
/-- The existing empty-boundary cluster part satisfies the corrected
energy-normalized mandatory-label estimate. Auxiliary to ALVV,
arXiv:1602.08828v2, `thm:cluster-approx`, lines 1270–1291 and 1935–1968;
Hastings, arXiv:cond-mat/0508554v3, source lines 1174–1177. -/
theorem norm_clusterPart_empty_boundary_le_of_lower_bound
    (H : Matrix ι ι ℂ) (h : κ → Matrix ι ι ℂ) (U : Finset κ)
    (hH : H.IsHermitian) (hh : ∀ i ∈ U, (h i).IsHermitian)
    (hnorm : ∀ i ∈ U, ‖h i‖ ≤ 1) (lambda β : ℝ)
    (hlo : (lambda : ℂ) • 1 ≤ H) (hβ : 0 ≤ β) :
    Real.exp (β * lambda) * ‖clusterPart H h ∅ U β‖ ≤ (Real.exp β - 1) ^ U.card := by
  simpa only [clusterPart, Finset.sum_empty, sub_zero] using
    Matrix.norm_sum_powerset_exp_sub_le_of_lower_bound H h U hH hh hnorm lambda β hlo hβ

/-- Summing the existing exact-support coefficients over supports containing
all required labels gives the existing empty-boundary cluster part.
Hastings, arXiv:cond-mat/0508554v3, source lines 1174–1177 and 1268–1269. -/
theorem clusterPart_empty_boundary_eq_sum_clusterOp [Fintype κ]
    (h : κ → Matrix ι ι ℂ) (U : Finset κ) (β : ℝ) :
    clusterPart (∑ i, h i) h ∅ U β = ∑ A : Finset κ with U ⊆ A, clusterOp h A β := by
  classical
  have hp := hasSum_words_clusterPart (H := ∑ i, h i) (h := h) (B := ∅) (C := U)
    rfl (by simp) β
  simp only [Finset.disjoint_empty_right, and_true] at hp
  apply hp.unique
  convert (hasSum_sum (s := {A : Finset κ | U ⊆ A}) fun A _ ↦
    hasSum_words_clusterOp h A β) using 1
  funext n
  rw [← Finset.smul_sum]
  congr 1
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun w : Fin n → κ ↦ univ.image w)
    (t := {A : Finset κ | U ⊆ A}) (fun w hw ↦ by simpa using hw)]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  rw [Finset.filter_filter]
  exact Finset.sum_congr (Finset.filter_congr fun w _ ↦
    ⟨fun hw ↦ hw.2, fun hw ↦ ⟨hw.symm ▸ (Finset.mem_filter.mp hA).2, hw⟩⟩)
    (fun _ _ ↦ rfl)


end ClusterExpansion

/-!
## Inclusion and exclusion for mandatory windows

A finite family of required windows specifies a set of discarded label supports.
Mathlib's finite inclusion--exclusion identity, followed by the existing mandatory-support
identity, expresses the discarded operator as an alternating sum of the existing cluster parts.
The identity is valid for arbitrary complex matrices and every real parameter.

These are finite identities auxiliary to the cluster expansion in ALVV,
arXiv:1602.08828v2, `thm:cluster-approx`, source lines 1935–1968. The second theorem explicitly
assumes an avoidance characterization of the selected supports. The actual path characterization
is proved separately in `PathIntervals`; no spatial estimate is assumed here.
-/

open Finset

namespace ClusterExpansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
private theorem badSupport_indicator (W : Finset (Finset κ)) (A : Finset κ)
    (f : Finset κ → Matrix ι ι ℂ) :
    (if ∃ I ∈ W, I ⊆ A then f A else 0) =
      ∑ F ∈ W.powerset with F.Nonempty,
        (-1 : ℤ) ^ (F.card + 1) • (if F.biUnion id ⊆ A then f A else 0) := by
  classical
  have hi := Finset.indicator_biUnion_eq_sum_powerset W
    (fun I : Finset κ ↦ {A : Finset κ | I ⊆ A}) f A
  simpa only [Set.indicator, Set.mem_iUnion, Set.mem_ofPred_eq,
    Set.mem_iInter, Finset.biUnion_subset, id_eq, exists_prop] using hi

/-- Inclusion and exclusion over a finite family of mandatory windows, expressed using the
existing cluster part. This finite identity is auxiliary to the corrected interaction-label
truncation in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem sum_clusterOp_bad_windows_eq (h : κ → Matrix ι ι ℂ)
    (W : Finset (Finset κ)) (β : ℝ) :
    (∑ A : Finset κ with ∃ I ∈ W, I ⊆ A, clusterOp h A β) =
      ∑ F ∈ W.powerset with F.Nonempty,
        (-1 : ℤ) ^ (F.card + 1) •
          clusterPart (∑ i, h i) h ∅ (F.biUnion id) β := by
  classical
  rw [Finset.sum_filter]
  simp_rw [badSupport_indicator W _ (fun A ↦ clusterOp h A β)]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum, ← Finset.sum_filter,
    ← clusterPart_empty_boundary_eq_sum_clusterOp]

/-- A window characterization of discarded supports gives an exact inclusion--exclusion
formula for the existing truncated exponential. This is a finite identity; no spatial estimate
or matrix product representation is assumed. Auxiliary to ALVV, arXiv:1602.08828v2,
`thm:cluster-approx`. -/
theorem exp_sub_truncatedExp_eq_sum_clusterPart_windows
    (G : SimpleGraph κ) [DecidableRel G.Adj] (large : Finset κ → Prop)
    (W : Finset (Finset κ))
    (hW : ∀ A, NoLargeCluster G large A ↔ ¬ ∃ I ∈ W, I ⊆ A)
    (h : κ → Matrix ι ι ℂ) (β : ℝ) :
    NormedSpace.exp (-(β • ∑ i, h i)) - truncatedExp G large h β =
      ∑ F ∈ W.powerset with F.Nonempty,
        (-1 : ℤ) ^ (F.card + 1) •
          clusterPart (∑ i, h i) h ∅ (F.biUnion id) β := by
  classical
  have hfull : NormedSpace.exp (-(β • ∑ i, h i)) = ∑ A : Finset κ, clusterOp h A β := by
    simpa [clusterPart] using clusterPart_empty_boundary_eq_sum_clusterOp h ∅ β
  rw [hfull, truncatedExp_eq_sum_clusterOp]
  rw [← sum_clusterOp_bad_windows_eq]
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := (univ : Finset (Finset κ)))
    (p := NoLargeCluster G large) (f := fun A ↦ clusterOp h A β)
  rw [← hsplit, add_sub_cancel_left]
  simp_rw [hW, not_not]

end ClusterExpansion
