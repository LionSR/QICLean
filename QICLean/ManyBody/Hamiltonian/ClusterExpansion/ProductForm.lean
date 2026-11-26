/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ClusterExpansion.Temperature
import QICLean.ManyBody.Hamiltonian.ClusterExpansion.Factorization
import QICLean.ManyBody.Sites.Product.ProductForm

/-!
# The truncated operator of an interaction in matrix product form

Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1256–1279, shows that the truncated operator `ρ(β, l_proj)` "can be exactly written in a
matrix product form", the form of eq. `mpf` (lines 1024–1039). For an interaction `Φ` whose term
`h_k` acts on `T k`, a reflexive locality relation `near` and the overlap graph of the
supports, a cluster is large when two sites of its supports are not related by `near`
(`IsLargeSupport`). The index at a site records the cluster containing it, if any, and a
matrix-unit label; the coefficient at a site checks that the recorded cluster is valid and
recorded at every site of its supports, and at one anchor site carries the matrix element of
`E_C`. Labels off a cluster are those of a fixed configuration `z`, as in
`ManyBody.ProductForm.ofSupported`, so the basis types may vary with the site.

The last section takes even powers (eq. `mplt`, lines 1303–1317): `ρ(β, l)^m` is in product form
and positive semidefinite for even `m`.

## Main results

* `ManyBody.ClusterExpansion.truncatedExp_eq_mul`: the terms acting on no site split off.
* `ManyBody.ClusterExpansion.hasProductForm_sum_clusterOp`,
  `ManyBody.ClusterExpansion.hasProductForm_truncatedExp`: `ρ(β, l)` has a matrix product form
  with the coefficient neighbourhoods `near`.
* `ManyBody.HasProductForm.pow_of_even`: even powers of a Hermitian operator in product form.
* `ManyBody.ClusterExpansion.hasProductForm_truncatedExp_pow_of_even`,
  `hasProductForm_truncatedExp_of_dist_le`, `hasProductForm_truncatedExp_pow_of_even_of_dist_le`.

Moved from TNLean (`e113e005`): `TNLean/Lattice/ClusterExpansion/TruncatedProductForm.lean`,
`TruncatedAllTemperatures.lean`, and `HasProductForm.pow_of_even` of
`ClusterExpansion/AllTemperatures.lean`. Changes: the terms are those of `Φ : Interaction X T`
on any finite basis types; the coefficient `clusterCoeff` takes the reference configuration `z` for
the labels off the cluster instead of reusing the label at the anchor site, which needed a
common dimension; `piKronecker` is `Matrix.piKronecker`.
-/

universe u

open Finset Matrix SimpleGraph _root_.ClusterExpansion
open scoped Function

namespace ManyBody

section PowOfEven

open scoped MatrixOrder ComplexOrder

/-- **Eq. `mplt` keeps the matrix product form.** For a Hermitian `ρ` in product form and
even `m`, the power `ρ^m` is positive semidefinite and in product form with the same
coefficient neighbourhoods, the `m` indices at each site being grouped into one.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1303–1317.

**Local fix (positivity at every temperature):** the source states positive definiteness,
which would need the base to be invertible; the statement here is positive
semidefiniteness, as documented in `docs/paper-gaps/hastings05_mplt_positivity.tex`. -/
theorem HasProductForm.pow_of_even {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type u}
    [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] {near : V → V → Prop}
    {ρ : Matrix (Config X) (Config X) ℂ} (hρ : HasProductForm X near ρ) (hH : ρ.IsHermitian)
    {m : ℕ} (hm : Even m) : HasProductForm X near (ρ ^ m) ∧ (ρ ^ m).PosSemidef :=
  ⟨hρ.pow m, _root_.ClusterExpansion.posSemidef_pow_of_even hH hm⟩

end PowOfEven

namespace ClusterExpansion

/-- Entries of a supported operator depend only on the labels on its region, for pairs of
configurations that agree with each other off the region. -/
private theorem apply_eq_apply_of_mem_supportedOperators {V : Type*} [Fintype V] [DecidableEq V]
    {X : V → Type u} [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] {D : Finset V}
    {A : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X D) {u v x y : Config X}
    (hux : ∀ j ∈ D, u j = x j) (hvy : ∀ j ∈ D, v j = y j) (huv : ∀ j ∉ D, u j = v j)
    (hxy : ∀ j ∉ D, x j = y j) : A u v = A x y :=
  IsSupportedOn.apply_eq hA hux hvy fun j hj ↦ ⟨fun _ ↦ hxy j hj, fun _ ↦ huv j hj⟩

section Entry

variable {V ι : Type*} [Fintype V] [DecidableEq V] {X : V → Type u} [∀ v, Fintype (X v)] [∀ v,
    DecidableEq (X v)]

/-- **Entries of a product of operators on disjoint sets of sites.** If the operators `O C`,
`C ∈ S`, act on pairwise disjoint sets `Y C`, the `(u, v)` entry of their product is the diagonal
check `u = v` off `⋃_C Y C` times the product over `C` of the entries of `O C` between `u` and the
configuration equal to `v` on `Y C` and to `u` elsewhere. -/
theorem noncommProd_apply_of_pairwiseDisjoint (Y : ι → Finset V)
    (O : ι → Matrix (Config X) (Config X) ℂ) (S : Finset ι)
    (hO : ∀ C ∈ S, O C ∈ supportedOperators X (Y C : Finset V))
    (hS : (S : Set ι).PairwiseDisjoint Y) (hc : (S : Set ι).Pairwise (Commute on O))
    (u v : Config X) :
    S.noncommProd O hc u v =
      (∏ j ∈ (S.biUnion Y)ᶜ, if u j = v j then 1 else 0) *
        ∏ C ∈ S, O C u (fun j ↦ if j ∈ Y C then v j else u j) := by
  classical
  induction S using Finset.induction_on generalizing u with
  | empty => simp [one_apply, Finset.prod_boole, funext_iff]
  | insert C S hC ih =>
    have hS' : (S : Set ι).PairwiseDisjoint Y := hS.subset (by simp)
    have hCS : ∀ C' ∈ S, Disjoint (Y C) (Y C') := fun C' hC' ↦
      hS (by simp) (by simp [hC']) fun h ↦ hC (h ▸ hC')
    have hXC : Disjoint (Y C) (S.biUnion Y) := (disjoint_biUnion_right _ _ _).2 hCS
    have hO' : ∀ C' ∈ S, O C' ∈ supportedOperators X (Y C' : Finset V) :=
      fun C' hC' ↦ hO C' (mem_insert_of_mem hC')
    rw [noncommProd_insert_of_notMem _ _ _ _ hC, Matrix.mul_apply]
    set w : Config X := fun j ↦ if j ∈ Y C then v j else u j with hw
    rw [Finset.sum_eq_single w]
    · rw [ih hO' hS' _ w, biUnion_insert, Finset.prod_insert hC]
      have h1 : (∏ j ∈ (S.biUnion Y)ᶜ, if w j = v j then (1 : ℂ) else 0) =
          ∏ j ∈ (Y C ∪ S.biUnion Y)ᶜ, if u j = v j then 1 else 0 := by
        rw [← Finset.prod_subset (s₁ := (Y C ∪ S.biUnion Y)ᶜ)
          (compl_subset_compl.2 subset_union_right) fun j hj hj' ↦ ?_]
        · refine Finset.prod_congr rfl fun j hj ↦ ?_
          have : j ∉ Y C := fun h ↦ (mem_compl.1 hj) (mem_union_left _ h)
          simp [hw, this]
        · have : j ∈ Y C := by
            by_contra hjC
            exact hj' (mem_compl.2 fun h ↦ (mem_union.1 h).elim hjC (mem_compl.1 hj))
          simp [hw, this]
      have h2 : ∀ C' ∈ S, O C' w (fun j ↦ if j ∈ Y C' then v j else w j) =
          O C' u (fun j ↦ if j ∈ Y C' then v j else u j) := by
        intro C' hC'
        refine apply_eq_apply_of_mem_supportedOperators (hO' C' hC') (fun j hj ↦ ?_)
          (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j hj ↦ ?_)
        · have : j ∉ Y C := fun h ↦ disjoint_left.1 (hCS C' hC') h hj
          simp [hw, this]
        · simp [show j ∈ Y C' from hj]
        · simp [show j ∉ Y C' from hj]
        · simp [show j ∉ Y C' from hj]
      rw [h1, Finset.prod_congr rfl h2]
      ring
    · intro w' _ hw'
      by_cases hoff : ∃ j ∉ (Y C : Set V), u j ≠ w' j
      · obtain ⟨j, hj, hne⟩ := hoff
        rw [apply_eq_zero_of_mem_supportedOperators (hO C (mem_insert_self C S)) hj hne,
          zero_mul]
      · push Not at hoff
        obtain ⟨j, hj⟩ := Function.ne_iff.1 hw'
        have hjX : j ∈ Y C := by
          by_contra hjX
          exact hj (by simp [hw, hjX, hoff j hjX])
        rw [ih hO' hS' _ w', Finset.prod_eq_zero (i := j)
          (mem_compl.2 fun h ↦ disjoint_left.1 hXC hjX h), zero_mul, mul_zero]
        simp only [hw, hjX, ite_true] at hj
        simp [hj]
    · simp

end Entry

section Split

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type u} [∀ v, Fintype (X v)] [∀ v,
    DecidableEq (X v)] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A set `C` of terms is large when the union of its supports contains two sites
that do not satisfy the locality relation `near`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1103–1107. -/
def IsLargeSupport (near : V → V → Prop) (T : κ → Finset V) (C : Finset κ) : Prop :=
  ∃ a ∈ C.biUnion T, ∃ b ∈ C.biUnion T, ¬ near a b

omit [Fintype V] in
/-- Terms acting on no site do not affect whether a set of terms has a large cluster: such a
term is adjacent to nothing, so it forms a cluster by itself, which is not large. -/
theorem noLargeCluster_iff_filter (T : κ → Finset V) (near : V → V → Prop) (A : Finset κ) :
    NoLargeCluster (overlapGraph T) (IsLargeSupport near T) A ↔
      NoLargeCluster (overlapGraph T) (IsLargeSupport near T)
        {k ∈ A | (T k).Nonempty} := by
  constructor
  · intro hA C hC hlarge
    refine hA C ⟨hC.1.trans (filter_subset _ _), hC.2.1, disjoint_left.2 fun j hjA hjB ↦ ?_⟩
      hlarge
    obtain ⟨-, x, hx⟩ := (mem_boundary_overlapGraph T).1 hjB
    exact disjoint_left.1 hC.2.2 (mem_filter.2 ⟨hjA, x, (mem_inter.1 hx).1⟩) hjB
  · intro hA C hC hlarge
    obtain ⟨a, ha, -⟩ := id hlarge
    obtain ⟨k, hkC, hak⟩ := mem_biUnion.1 ha
    have hsub : C ⊆ {k ∈ A | (T k).Nonempty} := by
      intro j hj
      refine mem_filter.2 ⟨hC.1 hj, ?_⟩
      by_contra hj0
      have hne : (⟨j, hj⟩ : (C : Set κ)) ≠ ⟨k, hkC⟩ := fun h ↦
        hj0 ⟨a, by rw [show j = k from congrArg Subtype.val h]; exact hak⟩
      obtain ⟨w, hadj, -, -⟩ :=
        SimpleGraph.Walk.exists_eq_cons_of_ne hne (hC.2.1.preconnected _ _).some
      exact hj0 ((SimpleGraph.comap_adj.1 hadj).2.mono inter_subset_left)
    exact hA C ⟨hsub, hC.2.1, hC.2.2.mono_left (filter_subset _ _)⟩ hlarge

open Classical in
/-- `ρ(β, l)` is the product of the sum of `E_A` over the sets `A` of terms acting on no site
(a multiple of the identity) and the sum of `E_A` over the sets `A` of terms acting on some site
with no large cluster. -/
theorem truncatedExp_eq_mul (T : κ → Finset V)
    (Φ : Interaction X T)
    (near : V → V → Prop) (β : ℝ) :
    truncatedExp (overlapGraph T) (IsLargeSupport near T) Φ.term β =
      (∑ A with ∀ k ∈ A, ¬ (T k).Nonempty, clusterOp Φ.term A β) *
        ∑ A with (∀ k ∈ A, (T k).Nonempty) ∧
          NoLargeCluster (overlapGraph T) (IsLargeSupport near T) A, clusterOp Φ.term A β :=
              by
  rw [truncatedExp_eq_sum_clusterOp, Finset.sum_mul_sum, ← Finset.sum_product']
  have hf0 : ∀ A₀ A₁ : Finset κ, (∀ k ∈ A₀, ¬ (T k).Nonempty) →
      (∀ k ∈ A₁, (T k).Nonempty) → {k ∈ A₀ ∪ A₁ | ¬ (T k).Nonempty} = A₀ := by
    intro A₀ A₁ h₀ h₁
    rw [filter_union, filter_true_of_mem h₀, filter_false_of_mem fun k hk h ↦ h (h₁ k hk),
      union_empty]
  have hf1 : ∀ A₀ A₁ : Finset κ, (∀ k ∈ A₀, ¬ (T k).Nonempty) →
      (∀ k ∈ A₁, (T k).Nonempty) → {k ∈ A₀ ∪ A₁ | (T k).Nonempty} = A₁ := by
    intro A₀ A₁ h₀ h₁
    rw [filter_union, filter_true_of_mem h₁, filter_false_of_mem h₀, empty_union]
  refine Finset.sum_nbij' (fun A ↦ ({k ∈ A | ¬ (T k).Nonempty}, {k ∈ A | (T k).Nonempty}))
    (fun p ↦ p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [mem_filter, mem_univ, true_and, mem_product] at hA ⊢
    exact ⟨fun k hk ↦ hk.2, fun k hk ↦ hk.2,
      (noLargeCluster_iff_filter T near A).1 hA⟩
  · rintro ⟨A₀, A₁⟩ hp
    simp only [mem_filter, mem_univ, true_and, mem_product] at hp ⊢
    rw [noLargeCluster_iff_filter, hf1 A₀ A₁ hp.1 hp.2.1]
    exact hp.2.2
  · intro A _
    exact (union_comm _ _).trans (filter_union_filter_not_eq (fun k ↦ (T k).Nonempty) A)
  · rintro ⟨A₀, A₁⟩ hp
    simp only [mem_filter, mem_univ, true_and, mem_product] at hp
    exact Prod.ext (hf0 A₀ A₁ hp.1 hp.2.1) (hf1 A₀ A₁ hp.1 hp.2.1)
  · intro A _
    rw [← clusterOp_union Φ.term (disjoint_filter_filter_not _ _ _).symm fun j hj k _ ↦ ?_,
      (union_comm _ _).trans (filter_union_filter_not_eq (fun k ↦ (T k).Nonempty) A)]
    exact commute_of_not_adj_overlapGraph Φ j k fun hadj ↦
      (mem_filter.1 hj).2 (hadj.2.mono inter_subset_left)

end Split

section Core

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type u} [∀ v, Fintype (X v)] [∀ v,
    DecidableEq (X v)] {κ : Type*} [Fintype κ] [DecidableEq κ]
  (T : κ → Finset V) (near : V → V → Prop)

/-- A *valid cluster*: a nonempty connected set of terms, each acting on some site, whose
supports contain only pairs of sites satisfying `near`. These are the clusters
recorded by the indices of the matrix product form.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1096–1107. -/
def IsValidCluster (C : Finset κ) : Prop :=
  (∀ k ∈ C, (T k).Nonempty) ∧ ((overlapGraph T).induce (C : Set κ)).Connected ∧
    ¬ IsLargeSupport near T C

open Classical in
/-- The families of valid clusters with pairwise disjoint supports. -/
noncomputable def validFamilies : Finset (Finset (Finset κ)) :=
  {S | (∀ C ∈ S, IsValidCluster T near C) ∧
    (S : Set (Finset κ)).PairwiseDisjoint (·.biUnion T)}

variable {T near}

omit [Fintype V] in
theorem mem_validFamilies {S : Finset (Finset κ)} :
    S ∈ validFamilies T near ↔ (∀ C ∈ S, IsValidCluster T near C) ∧
      (S : Set (Finset κ)).PairwiseDisjoint (·.biUnion T) := by
  classical
  simp [validFamilies]

omit [Fintype V] [Fintype κ] [DecidableEq κ] in
/-- The supports of a valid cluster form a nonempty set of sites. -/
theorem IsValidCluster.nonempty_biUnion {C : Finset κ} (hC : IsValidCluster T near C) :
    (C.biUnion T).Nonempty := by
  obtain ⟨⟨k, hk⟩⟩ := hC.2.1.nonempty
  obtain ⟨x, hx⟩ := hC.1 k hk
  exact ⟨x, mem_biUnion.2 ⟨k, hk, hx⟩⟩

omit [Fintype V] [Fintype κ] [DecidableEq κ] in
/-- Two sites in the supports of a valid cluster satisfy the locality relation. -/
theorem IsValidCluster.related {C : Finset κ} (hC : IsValidCluster T near C)
    {a b : V} (ha : a ∈ C.biUnion T) (hb : b ∈ C.biUnion T) :
    near a b := by
  by_contra hw
  exact hC.2.2 ⟨a, ha, b, hb, hw⟩

omit [Fintype V] in
/-- A member of a family of valid clusters with disjoint supports is a cluster of the union of
the family. -/
theorem isCluster_of_mem_validFamilies {S : Finset (Finset κ)} (hS : S ∈ validFamilies T near)
    {C : Finset κ} (hC : C ∈ S) : IsCluster (overlapGraph T) (S.biUnion id) C := by
  rw [mem_validFamilies] at hS
  refine ⟨subset_biUnion_of_mem id hC, (hS.1 C hC).2.1, disjoint_left.2 fun j hjA hjB ↦ ?_⟩
  obtain ⟨C', hC', hjC'⟩ := mem_biUnion.1 hjA
  obtain ⟨hjC, x, hx⟩ := (mem_boundary_overlapGraph T).1 hjB
  by_cases hCC' : C' = C
  · exact hjC (hCC' ▸ hjC')
  exact disjoint_left.1 (hS.2 hC' hC hCC') (mem_biUnion.2 ⟨j, hjC', (mem_inter.1 hx).1⟩)
    (mem_inter.1 hx).2

omit [Fintype V] in
/-- The clusters of the union of a family of valid clusters with disjoint supports are the
members of the family. -/
theorem clusters_biUnion_of_mem_validFamilies {S : Finset (Finset κ)}
    (hS : S ∈ validFamilies T near) : clusters (overlapGraph T) (S.biUnion id) = S := by
  ext D
  rw [mem_clusters]
  refine ⟨fun hD ↦ ?_, isCluster_of_mem_validFamilies hS⟩
  obtain ⟨⟨k, hk⟩⟩ := hD.2.1.nonempty
  obtain ⟨C, hC, hkC⟩ := mem_biUnion.1 (hD.1 hk)
  rwa [eq_of_isCluster_of_inter_nonempty _ hD (isCluster_of_mem_validFamilies hS hC)
    ⟨k, mem_inter.2 ⟨hk, hkC⟩⟩]

omit [Fintype V] in
/-- The clusters of any set of terms have pairwise disjoint supports. -/
theorem pairwiseDisjoint_clusters (A : Finset κ) :
    (clusters (overlapGraph T) A : Set (Finset κ)).PairwiseDisjoint (·.biUnion T) := by
  intro C hC C' hC' hne
  obtain ⟨hdisj, hnadj⟩ := pairwise_clusters _ A hC hC' hne
  refine disjoint_left.2 fun x hx hx' ↦ ?_
  obtain ⟨j, hj, hxj⟩ := mem_biUnion.1 hx
  obtain ⟨k, hk, hxk⟩ := mem_biUnion.1 hx'
  exact hnadj j hj k hk ⟨fun h ↦ disjoint_left.1 hdisj hj (h ▸ hk), x, mem_inter.2 ⟨hxj, hxk⟩⟩

open Classical in
/-- **The sum over sets of terms as a sum over families of clusters.** The sets `A` of terms
acting on some site with no large cluster correspond to the families of valid clusters with
disjoint supports, `A ↦ clusters A`, and the entries of `E_A` factor over the clusters.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1108–1110 and 1268–1270. -/
theorem sum_clusterOp_apply (Φ : Interaction X T) (β : ℝ)
    (u v : Config X) :
    (∑ A with (∀ k ∈ A, (T k).Nonempty) ∧
        NoLargeCluster (overlapGraph T) (IsLargeSupport near T) A, clusterOp Φ.term A β) u v =
      ∑ S ∈ validFamilies T near,
        (∏ j ∈ (S.biUnion (·.biUnion T))ᶜ, if u j = v j then 1 else 0) *
          ∏ C ∈ S, clusterOp Φ.term C β u (fun j ↦ if j ∈ C.biUnion T then v j else u j) := by
  rw [Matrix.sum_apply]
  refine Finset.sum_nbij' (fun A ↦ clusters (overlapGraph T) A) (fun S ↦ S.biUnion id)
    ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [mem_filter, mem_univ, true_and] at hA
    rw [mem_validFamilies]
    refine ⟨fun C hC ↦ ?_, pairwiseDisjoint_clusters A⟩
    rw [mem_clusters] at hC
    exact ⟨fun k hk ↦ hA.1 k (hC.1 hk), hC.2.1, hA.2 C hC⟩
  · intro S hS
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun k hk ↦ ?_, fun D hD ↦ ?_⟩
    · obtain ⟨C, hC, hkC⟩ := mem_biUnion.1 hk
      exact ((mem_validFamilies.1 hS).1 C hC).1 k hkC
    · rw [← mem_clusters, clusters_biUnion_of_mem_validFamilies hS] at hD
      exact ((mem_validFamilies.1 hS).1 D hD).2.2
  · intro A _
    exact biUnion_clusters _ A
  · intro S hS
    exact clusters_biUnion_of_mem_validFamilies hS
  · intro A _
    rw [clusterOp_eq_noncommProd_clusters _ (commute_of_not_adj_overlapGraph Φ) A β,
      noncommProd_apply_of_pairwiseDisjoint _ _ _
        (fun C _ ↦ clusterOp_mem_supportedOperators Φ C β) (pairwiseDisjoint_clusters A)]

variable (T near)

/-- The *anchor* of a set of terms: a chosen site of the union of their supports, at which the
coefficient carrying the matrix element of `E_C` is placed. When the supports are empty, which
does not happen for a valid cluster, it is the given site `i`, so no site of the domain need be
chosen in advance. -/
noncomputable def anchor (C : Finset κ) (i : V) : V :=
  if hC : (C.biUnion T).Nonempty then hC.choose else i

open Classical in
/-- The coefficient function at site `i`. The index at a site records the cluster containing it,
if any, and a matrix-unit label. A site recording no cluster checks that its label is diagonal. A
site recording the cluster `C` checks that `C` is valid, that `i` lies in its supports and that
every site of its supports records `C`; at the anchor of `C` it carries the matrix element of
`E_C` read off the labels on the supports of `C`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1259–1272. -/
noncomputable def clusterCoeff (z : Config X) (h : κ → Matrix (Config X) (Config X) ℂ)
    (β : ℝ) (i : V) (α : (j : V) → Option (Finset κ) × (X j × X j)) : ℂ :=
  (α i).1.elim (if (α i).2.1 = (α i).2.2 then 1 else 0) fun C ↦
    if IsValidCluster T near C ∧ i ∈ C.biUnion T ∧ ∀ j ∈ C.biUnion T, (α j).1 = some C then
      if i = anchor T C i then
        clusterOp h C β (fun j ↦ if j ∈ C.biUnion T then (α j).2.1 else z j)
          (fun j ↦ if j ∈ C.biUnion T then (α j).2.2 else z j)
      else 1
    else 0

variable {T near}

omit [Fintype κ] in
/-- The coefficient function at `i` reads only indices at sites related to `i`:
the sites in the supports of the cluster recorded at `i`. -/
theorem isLocalCoefficient_clusterCoeff
    (z : Config X) (h : κ → Matrix (Config X) (Config X) ℂ) (β : ℝ) (i : V)
    (hnear : ∀ i, near i i) :
    IsLocalCoefficient near i (clusterCoeff T near z h β i) := by
  classical
  intro α α' hαα'
  have hi : α i = α' i := hαα' i (hnear i)
  unfold clusterCoeff
  rw [hi]
  rcases hc : (α' i).1 with _ | C
  · rfl
  simp only [Option.elim]
  by_cases hv : IsValidCluster T near C ∧ i ∈ C.biUnion T
  · have hnear : ∀ j ∈ C.biUnion T, α j = α' j :=
      fun j hj ↦ hαα' j (hv.1.related hv.2 hj)
    have hrow : (fun j ↦ if j ∈ C.biUnion T then (α j).2.1 else z j) =
        fun j ↦ if j ∈ C.biUnion T then (α' j).2.1 else z j := by
      funext j
      split_ifs with hj
      · rw [hnear j hj]
      · rfl
    have hcol : (fun j ↦ if j ∈ C.biUnion T then (α j).2.2 else z j) =
        fun j ↦ if j ∈ C.biUnion T then (α' j).2.2 else z j := by
      funext j
      split_ifs with hj
      · rw [hnear j hj]
      · rfl
    have hall : (∀ j ∈ C.biUnion T, (α j).1 = some C) ↔
        ∀ j ∈ C.biUnion T, (α' j).1 = some C :=
      forall₂_congr fun j hj ↦ by rw [hnear j hj]
    simp only [hrow, hcol, hall]
  · have hn : ∀ γ : (j : V) → Option (Finset κ) × (X j × X j),
        ¬ (IsValidCluster T near C ∧ i ∈ C.biUnion T ∧
          ∀ j ∈ C.biUnion T, (γ j).1 = some C) := fun _ h ↦ hv ⟨h.1, h.2.1⟩
    simp only [hn, ↓reduceIte]

/-- The entries of a sum `∑_α F(α) ⊗_j |a_j⟩⟨b_j|` over indices carrying a matrix-unit label:
the labels are forced to be the row and column configurations. -/
theorem sum_smul_piKronecker_single_apply {I : Type*} [Fintype I]
    (F : ((j : V) → I × (X j × X j)) → ℂ) (u v : Config X) :
    (∑ α, F α • piKronecker fun j ↦ single (α j).2.1 (α j).2.2 (1 : ℂ)) u v =
      ∑ c : V → I, F fun j ↦ (c j, (u j, v j)) := by
  classical
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, piKronecker_apply, smul_eq_mul]
  rw [← (Equiv.arrowProdEquivProdArrow _ _ _).symm.sum_comp, Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun c ↦ ?_
  rw [Finset.sum_eq_single (fun j ↦ (u j, v j))]
  · simp [Equiv.arrowProdEquivProdArrow]
  · intro ℓ _ hℓ
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hℓ
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    rw [single_apply]
    split_ifs with h
    · exact absurd (Prod.ext h.1 h.2) hj
    · rfl
  · simp

omit [Fintype V] [Fintype κ] [DecidableEq κ] in
/-- The anchor of a valid cluster is a fixed site of its supports, independent of `i`. -/
theorem anchor_eq {C : Finset κ} (hC : IsValidCluster T near C) (i : V) :
    anchor T C i = hC.nonempty_biUnion.choose :=
  dite_eq_left hC.nonempty_biUnion

variable (T near)

/-- An assignment of clusters to sites is *consistent* when every recorded cluster is valid,
contains the site in its supports, and is recorded at every site of its supports. -/
def IsClusterAssignment (c : V → Option (Finset κ)) : Prop :=
  ∀ i C, c i = some C →
    IsValidCluster T near C ∧ i ∈ C.biUnion T ∧ ∀ j ∈ C.biUnion T, c j = some C

open Classical in
/-- The clusters recorded by an assignment of clusters to sites. -/
noncomputable def recordedClusters (c : V → Option (Finset κ)) : Finset (Finset κ) :=
  {C | ∃ i, c i = some C}

open Classical in
/-- The assignment recording at each site the member of `S` whose supports contain it. -/
noncomputable def clusterAssignment (S : Finset (Finset κ)) (i : V) : Option (Finset κ) :=
  if hS : ∃ C ∈ S, i ∈ C.biUnion T then some hS.choose else none

variable {T near}

omit [DecidableEq V] in
theorem mem_recordedClusters {c : V → Option (Finset κ)} {C : Finset κ} :
    C ∈ recordedClusters c ↔ ∃ i, c i = some C := by
  classical
  simp [recordedClusters]

omit [Fintype V] [Fintype κ] [DecidableEq κ] in
theorem clusterAssignment_eq_some_of_mem {S : Finset (Finset κ)}
    (hS : (S : Set (Finset κ)).PairwiseDisjoint (·.biUnion T)) {C : Finset κ} (hC : C ∈ S)
    {i : V} (hi : i ∈ C.biUnion T) : clusterAssignment T S i = some C := by
  unfold clusterAssignment
  split_ifs with hex
  · obtain ⟨hC', hi'⟩ := hex.choose_spec
    by_contra hne
    exact disjoint_left.1 (hS hC' hC fun h ↦ hne (congrArg some h)) hi' hi
  · exact absurd ⟨C, hC, hi⟩ hex

omit [Fintype V] [Fintype κ] [DecidableEq κ] in
theorem clusterAssignment_eq_some {S : Finset (Finset κ)} {C : Finset κ} {i : V}
    (h : clusterAssignment T S i = some C) : C ∈ S ∧ i ∈ C.biUnion T := by
  unfold clusterAssignment at h
  split_ifs at h with hex
  · obtain rfl := Option.some.inj h
    exact hex.choose_spec

omit [Fintype V] [Fintype κ] [DecidableEq κ] in
theorem clusterAssignment_eq_none {S : Finset (Finset κ)} {i : V}
    (h : ∀ C ∈ S, i ∉ C.biUnion T) : clusterAssignment T S i = none := by
  unfold clusterAssignment
  split_ifs with hex
  · obtain ⟨C, hC, hi⟩ := hex
    exact absurd hi (h C hC)
  · rfl

theorem recordedClusters_mem_validFamilies {c : V → Option (Finset κ)}
    (hc : IsClusterAssignment T near c) : recordedClusters c ∈ validFamilies T near := by
  rw [mem_validFamilies]
  refine ⟨fun C hC ↦ ?_, fun C hC C' hC' hne ↦ ?_⟩
  · obtain ⟨i, hi⟩ := mem_recordedClusters.1 hC
    exact (hc i C hi).1
  · obtain ⟨i, hi⟩ := mem_recordedClusters.1 hC
    obtain ⟨i', hi'⟩ := mem_recordedClusters.1 hC'
    refine disjoint_left.2 fun x hx hx' ↦ hne ?_
    exact Option.some.inj (((hc i C hi).2.2 x hx).symm.trans ((hc i' C' hi').2.2 x hx'))

open Classical in
/-- **The sum over assignments.** For fixed labels, the products of the coefficient functions
vanish except at consistent assignments of clusters to sites, which correspond to the families
of valid clusters with disjoint supports; at such an assignment the product is the diagonal check
off the supports times the matrix elements of the `E_C`. -/
theorem sum_prod_clusterCoeff (z : Config X) (Φ : Interaction X T) (β : ℝ)
    (u v : Config X) :
    ∑ c : V → Option (Finset κ), ∏ i, clusterCoeff T near z Φ.term β i (fun j ↦ (c j, (u j, v
        j))) =
      ∑ S ∈ validFamilies T near,
        (∏ j ∈ (S.biUnion (·.biUnion T))ᶜ, if u j = v j then 1 else 0) *
          ∏ C ∈ S, clusterOp Φ.term C β u (fun j ↦ if j ∈ C.biUnion T then v j else u j) := by
  have hzero : ∀ c : V → Option (Finset κ),
      ∏ i, clusterCoeff T near z Φ.term β i (fun j ↦ (c j, (u j, v j))) ≠ 0 →
        IsClusterAssignment T near c := by
    intro c hc i C hci
    by_contra hn
    exact hc (Finset.prod_eq_zero (mem_univ i)
      (by simp only [clusterCoeff, hci, Option.elim, hn, ↓reduceIte]))
  have hval : ∀ S ∈ validFamilies T near,
      ∏ i, clusterCoeff T near z Φ.term β i (fun j ↦ (clusterAssignment T S j, (u j, v j))) =
        (∏ j ∈ (S.biUnion (·.biUnion T))ᶜ, if u j = v j then 1 else 0) *
          ∏ C ∈ S, clusterOp Φ.term C β u (fun j ↦ if j ∈ C.biUnion T then v j else u j) := by
    intro S hS
    rw [mem_validFamilies] at hS
    rw [← Finset.prod_mul_prod_compl (S.biUnion (·.biUnion T)), mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      have hn : clusterAssignment T S i = none := clusterAssignment_eq_none
        fun C hC hiC ↦ mem_compl.1 hi (mem_biUnion.2 ⟨C, hC, hiC⟩)
      simp only [clusterCoeff, hn, Option.elim]
    · rw [Finset.prod_biUnion hS.2]
      refine Finset.prod_congr rfl fun C hC ↦ ?_
      have hc : ∀ i ∈ C.biUnion T, clusterAssignment T S i = some C :=
        fun i hi ↦ clusterAssignment_eq_some_of_mem hS.2 hC hi
      have hcoeff : ∀ i ∈ C.biUnion T,
          clusterCoeff T near z Φ.term β i (fun j ↦ (clusterAssignment T S j, (u j, v j))) =
            if i = (hS.1 C hC).nonempty_biUnion.choose then
              clusterOp Φ.term C β (fun j ↦ if j ∈ C.biUnion T then u j else z j)
                (fun j ↦ if j ∈ C.biUnion T then v j else z j)
            else 1 := by
        intro i hi
        have hcnd : IsValidCluster T near C ∧ i ∈ C.biUnion T ∧
            ∀ j ∈ C.biUnion T, clusterAssignment T S j = some C := ⟨hS.1 C hC, hi, hc⟩
        simp only [clusterCoeff, hc i hi, Option.elim, anchor_eq (hS.1 C hC)]
        split_ifs <;> rfl
      have hanc := (hS.1 C hC).nonempty_biUnion.choose_spec
      rw [Finset.prod_congr rfl hcoeff, Finset.prod_ite_eq']
      simp only [hanc, ↓reduceIte]
      refine apply_eq_apply_of_mem_supportedOperators (clusterOp_mem_supportedOperators Φ C β)
        (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j hj ↦ ?_)
      · simp [show j ∈ C.biUnion T from hj]
      · simp [show j ∈ C.biUnion T from hj]
      · simp [show j ∉ C.biUnion T from hj]
      · simp [show j ∉ C.biUnion T from hj]
  have hleft : ∀ c, IsClusterAssignment T near c →
      clusterAssignment T (recordedClusters c) = c := by
    intro c hc
    have hpd := (mem_validFamilies.1 (recordedClusters_mem_validFamilies hc)).2
    funext i
    rcases hci : c i with _ | C
    · refine clusterAssignment_eq_none fun C hC hiC ↦ ?_
      obtain ⟨i', hi'⟩ := mem_recordedClusters.1 hC
      have := (hc i' C hi').2.2 i hiC
      rw [hci] at this
      exact absurd this (by simp)
    · exact clusterAssignment_eq_some_of_mem hpd (mem_recordedClusters.2 ⟨i, hci⟩)
        (hc i C hci).2.1
  rw [← Finset.sum_filter_of_ne fun c _ hc ↦ hzero c hc]
  refine Finset.sum_nbij' recordedClusters (clusterAssignment T) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    exact recordedClusters_mem_validFamilies (mem_filter.1 hc).2
  · intro S hS
    rw [mem_validFamilies] at hS
    refine mem_filter.2 ⟨mem_univ _, fun i C he ↦ ?_⟩
    obtain ⟨hC, hi⟩ := clusterAssignment_eq_some he
    exact ⟨hS.1 C hC, hi, fun j hj ↦ clusterAssignment_eq_some_of_mem hS.2 hC hj⟩
  · intro c hc
    exact hleft c (mem_filter.1 hc).2
  · intro S hS
    rw [mem_validFamilies] at hS
    ext C
    rw [mem_recordedClusters]
    constructor
    · rintro ⟨i, hi⟩
      exact (clusterAssignment_eq_some hi).1
    · intro hC
      obtain ⟨x, hx⟩ := (hS.1 C hC).nonempty_biUnion
      exact ⟨x, clusterAssignment_eq_some_of_mem hS.2 hC hx⟩
  · intro c hc
    have hc' := (mem_filter.1 hc).2
    rw [← hval _ (recordedClusters_mem_validFamilies hc'), hleft c hc']

/-- The product form whose site index records its cluster, if any, and a matrix-unit
label. Hastings, arXiv:cond-mat/0508554v3, lines 1259–1272. -/
noncomputable def clusterProductForm (T : κ → Finset V) (near : V → V → Prop)
    (hnear : ∀ i, near i i) (z : Config X) (Φ : Interaction X T) (β : ℝ) :
    open Classical in ProductForm X near
      (∑ A with (∀ k ∈ A, (T k).Nonempty) ∧
        NoLargeCluster (overlapGraph T) (IsLargeSupport near T) A, clusterOp Φ.term A β) := by
  classical
  let e := Fintype.equivFin (Finset κ)
  refine {
    Index := fun j ↦ Option (Fin (Fintype.card (Finset κ))) × (X j × X j)
    siteOp := fun _ a ↦ single a.2.1 a.2.2 1
    coeff := fun i α ↦ clusterCoeff T near z Φ.term β i fun j ↦ ((α j).1.map e.symm, (α j).2)
    coeff_local := fun i α α' hαα' ↦
      isLocalCoefficient_clusterCoeff z Φ.term β i hnear _ _ fun j hj ↦ by rw [hαα' j hj]
    eq_sum := ?_ }
  ext u v
  rw [sum_clusterOp_apply Φ β u v, ← sum_prod_clusterCoeff z Φ β u v,
    sum_smul_piKronecker_single_apply]
  exact (Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) (Equiv.optionCongr e.symm)) _ _
    fun c ↦ rfl).symm

/-- **The product form of the clusters of terms acting on some site.** The sum of `E_A` over the
sets `A` of terms acting on some site with no large cluster has a matrix product
form with coefficient neighborhoods `near`. The index at a site records its cluster, if any,
and a matrix-unit label. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1256–1279. -/
theorem hasProductForm_sum_clusterOp (hnear : ∀ i, near i i)
    (Φ : Interaction X T) (β : ℝ) :
    open Classical in HasProductForm X near
      (∑ A with (∀ k ∈ A, (T k).Nonempty) ∧
        NoLargeCluster (overlapGraph T) (IsLargeSupport near T) A, clusterOp Φ.term A β) := by
  by_cases hconfig : Nonempty (Config X)
  · exact ⟨clusterProductForm T near hnear hconfig.some Φ β⟩
  · have : IsEmpty (Config X) := not_nonempty_iff.mp hconfig
    exact hasProductForm_of_isEmpty near _

end Core

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type u} [∀ v, Fintype (X v)] [∀ v,
    DecidableEq (X v)] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The truncated operator in matrix product form** (Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1256–1279). For terms `h k` acting on the sites `T k` of a nonempty
finite site set, terms adjacent when their supports meet, and clusters large when their
supports contain two sites not satisfying `near`, the truncated operator has a matrix product
form with coefficient neighborhoods `near`. The relation is assumed reflexive. No
Hermiticity, nonempty term supports, or connectivity of the site set is assumed. -/
theorem hasProductForm_truncatedExp [Nonempty V] (T : κ → Finset V)
    (Φ : Interaction X T)
    (near : V → V → Prop) (hnear : ∀ i, near i i) (β : ℝ) :
    HasProductForm X near
      (truncatedExp (overlapGraph T) (IsLargeSupport near T) Φ.term β) := by
  classical
  rw [truncatedExp_eq_mul T Φ near β]
  refine HasProductForm.mul ?_ (hasProductForm_sum_clusterOp hnear Φ β)
  refine hasProductForm_of_mem_supportedOperators_radius (D := ∅) (Classical.arbitrary _)
    (by simp) ?_
  refine sum_mem fun A hA ↦
    supportedOperators_mono ?_ (clusterOp_mem_supportedOperators Φ A β)
  intro x hx
  obtain ⟨k, hk, hxk⟩ := mem_biUnion.1 hx
  exact absurd ⟨x, hxk⟩ ((mem_filter.1 hA).2 k hk)

end Main


/-!
## The truncated operator at every temperature

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1303–1317), sets
`ρ(β, l_proj) = ρ(β/n, l_proj)^n` (eq. `mplt`) with `n` even, and states that this power is
positive and in the matrix product form of eq. `mpf`, the `n` indices at each site being grouped
into one. This file proves both for the actual truncated operator of the cluster expansion: it is
in product form of range `l` (`hasProductForm_truncatedExp`) and Hermitian when the terms are
(`isHermitian_truncatedExp`), so `HasProductForm.pow_of_even` applies.

**Local fix (positivity at every temperature):** the source states positive definiteness; the
result is positive semidefiniteness. Documented in `docs/paper-gaps/hastings05_mplt_positivity.tex`.

The product form holds on every nonempty finite site set with reflexive locality, and
therefore on every finite metric lattice. The local index ranges of its powers are proved
in `ManyBody/Hamiltonian/ClusterExpansion/IndexCount.lean`, with the lattice-volume interpretation
recorded in `docs/paper-gaps/hastings05_planar_domain_scope.tex`.

### Main results

* `HasProductForm.pow_of_even`: even powers of a Hermitian operator in product form.
* `hasProductForm_truncatedExp_pow_of_even`: for even `m`,
  `ρ(β, l)^m` is in product form of range `l` and positive semidefinite.

### References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, eq. `mplt`, lines 1303–1317.
-/

section AllTemperatures

open scoped MatrixOrder ComplexOrder

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type u} [∀ v, Fintype (X v)] [∀ v,
    DecidableEq (X v)] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Eq. `mplt` for the truncated operator** (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1303–1317). Let the finite site set be nonempty, let the locality relation be reflexive,
let each term `h k` be Hermitian and act on the sites `T k`, and let `m` be even. Then
`ρ(β, l)^m` is in matrix product form with the same locality relation and
positive semidefinite. With `β/n` in place of `β` and `m = n`, this is the matrix product form and
the positivity of `ρ(β, l_proj) = ρ(β/n, l_proj)^n`; the source states positive definiteness, see
the section docstring. -/
theorem hasProductForm_truncatedExp_pow_of_even [Nonempty V] (T : κ → Finset V)
    (Φ : Interaction X T)
    (hherm : ∀ k, (Φ.term k).IsHermitian) (near : V → V → Prop) (hnear : ∀ i, near i i)
    (β : ℝ) {m : ℕ} (hm : Even m) :
    HasProductForm X near
        ((truncatedExp (overlapGraph T) (IsLargeSupport near T) Φ.term β) ^ m) ∧
      ((truncatedExp (overlapGraph T) (IsLargeSupport near T) Φ.term β) ^ m).PosSemidef :=
  (hasProductForm_truncatedExp T Φ near hnear β).pow_of_even
    (isHermitian_truncatedExp _ _ hherm β) hm

/-- The source's diameter truncation on an arbitrary finite pseudometric site set has
matrix product form of range `l`. Hastings, arXiv:cond-mat/0508554v3, lines 1256–1279. -/
theorem hasProductForm_truncatedExp_of_dist_le [PseudoMetricSpace V] [Nonempty V]
    (T : κ → Finset V) (Φ : Interaction X T)
    {l : ℝ} (hl : 0 ≤ l) (β : ℝ) :
    HasProductForm X (fun i j ↦ dist i j ≤ l)
      (truncatedExp (overlapGraph T) (IsLargeDiam T l) Φ.term β) := by
  have hlarge : IsLargeSupport (fun i j ↦ dist i j ≤ l) T = IsLargeDiam T l := by
    funext C
    simp only [IsLargeSupport, IsLargeDiam, not_le]
  rw [← hlarge]
  exact hasProductForm_truncatedExp T Φ (fun i j ↦ dist i j ≤ l)
    (fun i ↦ by simpa using hl) β

/-- At every temperature, the even power of the source's diameter-truncated operator on
an arbitrary finite metric lattice is positive semidefinite and retains its matrix product
form. Hastings, arXiv:cond-mat/0508554v3, eq. `mplt`, lines 1303–1317. -/
theorem hasProductForm_truncatedExp_pow_of_even_of_dist_le
    [PseudoMetricSpace V] [Nonempty V] (T : κ → Finset V)
    (Φ : Interaction X T)
    (hherm : ∀ k, (Φ.term k).IsHermitian) {l : ℝ} (hl : 0 ≤ l) (β : ℝ)
    {m : ℕ} (hm : Even m) :
    HasProductForm X (fun i j ↦ dist i j ≤ l)
        ((truncatedExp (overlapGraph T) (IsLargeDiam T l) Φ.term β) ^ m) ∧
      ((truncatedExp (overlapGraph T) (IsLargeDiam T l) Φ.term β) ^ m).PosSemidef :=
  (hasProductForm_truncatedExp_of_dist_le T Φ hl β).pow_of_even
    (isHermitian_truncatedExp _ _ hherm β) hm

end AllTemperatures

end ClusterExpansion

end ManyBody
