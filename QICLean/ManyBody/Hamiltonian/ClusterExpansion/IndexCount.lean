/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Hamiltonian.ClusterExpansion.ProductForm
import QICLean.ManyBody.Dynamics.MetricGraph

/-!
# Local index ranges of the truncated cluster expansion

Only clusters containing a site can occur as its cluster index in Hastings' matrix product
form. The retained clusters have bounded diameter, so their interaction centres lie in a ball
about that site. Counting subsets of those centres gives a local index bound
`(1 + 2^M) |X i|²`, independently of the total size of the system (Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1259–1279 and 1318–1320).

**Local fix (volume growth):** the source's exponential bound in the dimension-th power of the
truncation length uses polynomial growth of lattice balls. The metric alone does not imply this
growth; the general statement counts local interaction centres, and the dimensional corollaries
state the volume hypothesis explicitly. Documented in
`docs/paper-gaps/hastings05_planar_domain_scope.tex`.

## Main results

* `ManyBody.ClusterExpansion.localClusterProductForm`,
  `ManyBody.ClusterExpansion.card_index_localClusterProductForm_le`.
* `ManyBody.ClusterExpansion.exists_productForm_truncatedExp_card_index` and its power, and the
  forms under polynomial growth, `…_of_polynomial_growth`.

Moved from TNLean (`e113e005`): `TNLean/Lattice/ClusterExpansion/LocalIndexCount.lean`. Changes:
the terms are those of `Φ : Interaction X T`, the local dimension `q` is the size of `X i`
at each site, and `[NeZero q]` is `[∀ v, Nonempty (X v)]`.
-/

universe u

open Finset Matrix _root_.ClusterExpansion
open scoped MatrixOrder ComplexOrder

namespace ManyBody

namespace ClusterExpansion

variable {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ]
  {X : V → Type u} [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]

open Classical in
/-- The index values at a site that record no cluster or a valid cluster containing it.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1259–1275. -/
noncomputable def clusterIndexSet (T : κ → Finset V) (near : V → V → Prop) (i : V) :
    Finset (Option (Fin (Fintype.card (Finset κ))) × (X i × X i)) :=
  Finset.univ.filter fun a ↦ a.1.elim True fun k ↦
    IsValidCluster T near ((Fintype.equivFin (Finset κ)).symm k) ∧
      i ∈ ((Fintype.equivFin (Finset κ)).symm k).biUnion T

/-- An index not recording a cluster containing its site has zero coefficient.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1259–1275. -/
theorem coeff_clusterProductForm_eq_zero_of_not_mem_clusterIndexSet
    (T : κ → Finset V) (near : V → V → Prop) (hnear : ∀ i, near i i) (z : Config X)
    (Φ : Interaction X T)
    (β : ℝ) (i : V)
    (α : (j : V) → Option (Fin (Fintype.card (Finset κ))) × (X j × X j))
    (hα : α i ∉ clusterIndexSet T near i) :
    (clusterProductForm T near hnear z Φ β).coeff i α = 0 := by
  classical
  have hbad : ¬ (α i).1.elim True (fun k ↦
      IsValidCluster T near ((Fintype.equivFin (Finset κ)).symm k) ∧
        i ∈ ((Fintype.equivFin (Finset κ)).symm k).biUnion T) := by
    simpa only [clusterIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hα
  change clusterCoeff T near z Φ.term β i
    (fun j ↦ ((α j).1.map (Fintype.equivFin (Finset κ)).symm, (α j).2)) = 0
  cases hc : (α i).1 with
  | none => exact (hbad (by simp only [hc, Option.elim_none])).elim
  | some k =>
    have hbad' : ¬ (IsValidCluster T near ((Fintype.equivFin (Finset κ)).symm k) ∧
        i ∈ ((Fintype.equivFin (Finset κ)).symm k).biUnion T) := by
      simpa only [hc, Option.elim_some] using hbad
    simp only [clusterCoeff, hc, Option.map_some, Option.elim_some]
    exact ite_eq_right fun h ↦ hbad' ⟨h.1, h.2.1⟩

/-- The cluster product form with only the index values allowed at each site.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1259–1279. -/
noncomputable def localClusterProductForm (T : κ → Finset V) (near : V → V → Prop)
    (hnear : ∀ i, near i i) (z : Config X) (Φ : Interaction X T) (β : ℝ) :
    open Classical in ProductForm X near
      (∑ A with (∀ k ∈ A, (T k).Nonempty) ∧
        NoLargeCluster (SimpleGraph.overlapGraph T) (IsLargeSupport near T) A, clusterOp
            Φ.term A β) :=
  (clusterProductForm T near hnear z Φ β).restrict (clusterIndexSet T near)
    (fun i α hα ↦ coeff_clusterProductForm_eq_zero_of_not_mem_clusterIndexSet
      T near hnear z Φ β i α hα)

omit [Fintype V] [DecidableEq κ] [∀ v, DecidableEq (X v)] in
/-- If all valid clusters containing a site use terms from `K`, that site's allowed
index set has at most `(1 + 2^|K|) q²` values. Empty-support terms cannot belong to a valid
cluster and do not contribute labels. Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_clusterIndexSet_le (T : κ → Finset V) (near : V → V → Prop) (i : V)
    (K : Finset κ)
    (hK : ∀ C, IsValidCluster T near C → i ∈ C.biUnion T → C ⊆ K) :
    (clusterIndexSet (X := X) T near i).card ≤ (2 ^ K.card + 1) * (Fintype.card (X i) *
        Fintype.card (X i)) := by
  classical
  let e := Fintype.equivFin (Finset κ)
  let L : Finset (Fin (Fintype.card (Finset κ))) := Finset.univ.filter fun k ↦
    IsValidCluster T near (e.symm k) ∧ i ∈ (e.symm k).biUnion T
  have hIndex : clusterIndexSet (X := X) T near i =
      (insert none (L.image some)).product (Finset.univ : Finset (X i × X i)) := by
    ext a
    rcases a with ⟨a, b⟩
    cases a <;> simp [clusterIndexSet, L, e]
  have hsub : L.image e.symm ⊆ K.powerset := by
    intro C hC
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨hv, hi⟩ := (Finset.mem_filter.mp hk).2
    exact Finset.mem_powerset.mpr (hK _ hv hi)
  have hcard : L.card ≤ 2 ^ K.card := by
    calc
      L.card = (L.image e.symm).card :=
        (Finset.card_image_of_injective _ e.symm.injective).symm
      _ ≤ K.powerset.card := Finset.card_le_card hsub
      _ = 2 ^ K.card := Finset.card_powerset K
  rw [hIndex, Finset.product_eq_sprod, Finset.card_product,
    Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ (Option.some_injective _)]
  simpa only [Finset.card_univ, Fintype.card_prod] using
    Nat.mul_le_mul_right (Fintype.card (X i) * Fintype.card (X i)) (Nat.add_le_add_right hcard 1)

omit [Fintype V] [DecidableEq κ] in
/-- Every term of a valid cluster containing `i` has its centre within `l + R` of `i`.
Centres need not belong to their term supports. Empty supports are excluded by cluster
validity. Hastings, arXiv:cond-mat/0508554v3, lines 1103–1107 and 1273–1275. -/
theorem IsValidCluster.subset_centres_ball [PseudoMetricSpace V]
    {T : κ → Finset V} {c : κ → V} {R l : ℝ}
    (hR : ∀ k j, j ∈ T k → dist (c k) j ≤ R)
    {C : Finset κ} (hC : IsValidCluster T (fun a b ↦ dist a b ≤ l) C)
    {i : V} (hi : i ∈ C.biUnion T) :
    C ⊆ Finset.univ.filter (fun k ↦ dist i (c k) ≤ l + R) := by
  intro k hk
  obtain ⟨j, hj⟩ := hC.1 k hk
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩
  have hlocal : dist i j ≤ l := hC.related hi (Finset.mem_biUnion.mpr ⟨k, hk, hj⟩)
  have hcentre : dist j (c k) ≤ R := by rw [dist_comm]; exact hR k j hj
  exact (dist_triangle i j (c k)).trans (add_le_add hlocal hcentre)

omit [Fintype V] [DecidableEq κ] [∀ v, DecidableEq (X v)] in
/-- A site's cluster index range is bounded by the number of interaction centres in a
local ball, rather than by the total number of terms.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_clusterIndexSet_le_ball [PseudoMetricSpace V]
    (T : κ → Finset V) (c : κ → V) (R l : ℝ)
    (hR : ∀ k j, j ∈ T k → dist (c k) j ≤ R) (i : V) :
    (clusterIndexSet (X := X) T (fun a b ↦ dist a b ≤ l) i).card ≤
      (2 ^ (Finset.univ.filter (fun k ↦ dist i (c k) ≤ l + R)).card + 1) * (Fintype.card (X i) *
          Fintype.card (X i)) :=
  card_clusterIndexSet_le T _ i _ fun _ hC hi ↦ hC.subset_centres_ball hR hi

/-- The restricted product form uses only the locally allowed index values, with their
actual cardinalities. Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_index_localClusterProductForm_le (T : κ → Finset V)
    (near : V → V → Prop) (hnear : ∀ i, near i i) (z : Config X)
    (Φ : Interaction X T) (β : ℝ)
    (i : V) (K : Finset κ)
    (hK : ∀ C, IsValidCluster T near C → i ∈ C.biUnion T → C ⊆ K) :
    Fintype.card ((localClusterProductForm T near hnear z Φ β).Index i) ≤
      (2 ^ K.card + 1) * (Fintype.card (X i) * Fintype.card (X i)) := by
  exact (ProductForm.card_index_restrict _ _ _ i).trans_le
    (card_clusterIndexSet_le T near i K hK)

/-- The actual diameter-truncated operator has a product form whose index range at `i`
is bounded by `(1 + 2^M) q²`, where `M` counts interaction centres within `l + R` of `i`.
Scalar terms with empty support contribute a scalar factor and no index components.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1256–1279. -/
theorem exists_productForm_truncatedExp_card_index [PseudoMetricSpace V]
    [Nonempty V] [∀ v, Nonempty (X v)] (T : κ → Finset V) (c : κ → V) (R l : ℝ)
    (hR : ∀ k j, j ∈ T k → dist (c k) j ≤ R) (hl : 0 ≤ l)
    (Φ : Interaction X T) (β : ℝ) :
    ∃ P : ProductForm X (fun i j ↦ dist i j ≤ l)
        (truncatedExp (SimpleGraph.overlapGraph T) (IsLargeDiam T l) Φ.term β),
      ∀ i, Fintype.card (P.Index i) ≤
        (2 ^ (Finset.univ.filter (fun k ↦ dist i (c k) ≤ l + R)).card + 1) * (Fintype.card (X i) *
            Fintype.card (X i)) := by
  classical
  let near : V → V → Prop := fun i j ↦ dist i j ≤ l
  have hnear : ∀ i, near i i := fun i ↦ by simpa only [near, dist_self] using hl
  have hlarge : IsLargeSupport near T = IsLargeDiam T l := by
    funext C
    simp only [IsLargeSupport, IsLargeDiam, near, not_le]
  rw [← hlarge, truncatedExp_eq_mul T Φ near β]
  let ρ₀ : Matrix (Config X) (Config X) ℂ :=
    ∑ A with ∀ k ∈ A, ¬ (T k).Nonempty, clusterOp Φ.term A β
  have h₀ : ρ₀ ∈ supportedOperators X (∅ : Finset V) := by
    refine sum_mem fun A hA ↦ supportedOperators_mono ?_
      (clusterOp_mem_supportedOperators Φ A β)
    intro x hx
    obtain ⟨k, hk, hxk⟩ := mem_biUnion.1 hx
    exact absurd ⟨x, hxk⟩ ((mem_filter.1 hA).2 k hk)
  let z : Config X := fun _ ↦ Classical.arbitrary _
  let P₀ := ProductForm.ofSupported (near := near) (D := ∅) z (Classical.arbitrary V) (by simp) h₀
  let P₁ := localClusterProductForm T near hnear z Φ β
  refine ⟨P₀.mul P₁, fun i ↦ ?_⟩
  change Fintype.card (P₀.Index i × P₁.Index i) ≤ _
  rw [Fintype.card_prod]
  have hP₀ : Fintype.card (P₀.Index i) = 1 := by
    simpa only [Finset.notMem_empty, ite_false] using
      ProductForm.card_index_ofSupported (near := near) (D := ∅) z (Classical.arbitrary V)
        (by simp) h₀ i
  rw [hP₀, one_mul]
  exact card_index_localClusterProductForm_le T near hnear z Φ β i _
    fun _ hC hi ↦ hC.subset_centres_ball hR hi

/-- The every-temperature construction preserves the local index bound to the power
equal to the number of factors. Its even powers are positive semidefinite.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1311–1320. -/
theorem exists_productForm_truncatedExp_pow_card_index [PseudoMetricSpace V]
    [Nonempty V] [∀ v, Nonempty (X v)] (T : κ → Finset V) (c : κ → V) (R l : ℝ)
    (hR : ∀ k j, j ∈ T k → dist (c k) j ≤ R) (hl : 0 ≤ l)
    (Φ : Interaction X T)
    (hHerm : ∀ k, (Φ.term k).IsHermitian) (β : ℝ) {m : ℕ} (hm : Even m) :
    ∃ P : ProductForm X (fun i j ↦ dist i j ≤ l)
        ((truncatedExp (SimpleGraph.overlapGraph T) (IsLargeDiam T l) Φ.term β) ^ m),
      ((truncatedExp (SimpleGraph.overlapGraph T) (IsLargeDiam T l) Φ.term β) ^
          m).PosSemidef ∧
        ∀ i, Fintype.card (P.Index i) ≤
          ((2 ^ (Finset.univ.filter (fun k ↦ dist i (c k) ≤ l + R)).card + 1) * (Fintype.card (X
              i) * Fintype.card (X i))) ^ m := by
  obtain ⟨P, hP⟩ := exists_productForm_truncatedExp_card_index T c R l hR hl Φ β
  refine ⟨P.pow m, posSemidef_pow_of_even (isHermitian_truncatedExp _ _ hHerm β) hm,
    fun i ↦ ?_⟩
  exact (ProductForm.card_index_pow P m i).trans_le (Nat.pow_le_pow_left (hP i) m)

/-- On a lattice with polynomial ball growth, the truncated operator has index range
exponential in the dimension-th power of the truncation length. The volume hypothesis
counts interaction labels, allowing more than one term at a centre.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem exists_productForm_truncatedExp_card_index_of_polynomial_growth
    [PseudoMetricSpace V] [Nonempty V] [∀ v, Nonempty (X v)]
    (T : κ → Finset V) (c : κ → V) (R l : ℝ)
    (hR : ∀ k j, j ∈ T k → dist (c k) j ≤ R) (hl : 0 ≤ l)
    (C D : ℕ)
    (hvolume : ∀ i, (Finset.univ.filter (fun k ↦ dist i (c k) ≤ l + R)).card ≤
      C * (⌈l + R⌉₊ + 1) ^ D)
    (Φ : Interaction X T) (β : ℝ) :
    ∃ P : ProductForm X (fun i j ↦ dist i j ≤ l)
        (truncatedExp (SimpleGraph.overlapGraph T) (IsLargeDiam T l) Φ.term β),
      ∀ i, Fintype.card (P.Index i) ≤
        (Fintype.card (X i) * Fintype.card (X i)) * (1 + 2 ^ (C * (⌈l + R⌉₊ + 1) ^ D)) := by
  obtain ⟨P, hP⟩ := exists_productForm_truncatedExp_card_index T c R l hR hl Φ β
  refine ⟨P, fun i ↦ (hP i).trans ?_⟩
  rw [Nat.mul_comm (Fintype.card (X i) * Fintype.card (X i)), Nat.add_comm 1]
  exact Nat.mul_le_mul_right (Fintype.card (X i) * Fintype.card (X i))
    (Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) (hvolume i)) 1)

/-- Polynomial ball growth yields the every-temperature index range exponential in the
number of factors times the dimension-th power of the truncation length.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1318–1320. -/
theorem exists_productForm_truncatedExp_pow_card_index_of_polynomial_growth
    [PseudoMetricSpace V] [Nonempty V] [∀ v, Nonempty (X v)]
    (T : κ → Finset V) (c : κ → V) (R l : ℝ)
    (hR : ∀ k j, j ∈ T k → dist (c k) j ≤ R) (hl : 0 ≤ l)
    (C D : ℕ)
    (hvolume : ∀ i, (Finset.univ.filter (fun k ↦ dist i (c k) ≤ l + R)).card ≤
      C * (⌈l + R⌉₊ + 1) ^ D)
    (Φ : Interaction X T)
    (hHerm : ∀ k, (Φ.term k).IsHermitian) (β : ℝ) {m : ℕ} (hm : Even m) :
    ∃ P : ProductForm X (fun i j ↦ dist i j ≤ l)
        ((truncatedExp (SimpleGraph.overlapGraph T) (IsLargeDiam T l) Φ.term β) ^ m),
      ((truncatedExp (SimpleGraph.overlapGraph T) (IsLargeDiam T l) Φ.term β) ^
          m).PosSemidef ∧
        ∀ i, Fintype.card (P.Index i) ≤
          ((Fintype.card (X i) * Fintype.card (X i)) * (1 + 2 ^ (C * (⌈l + R⌉₊ + 1) ^ D))) ^ m := by
  obtain ⟨P, hP⟩ := exists_productForm_truncatedExp_card_index_of_polynomial_growth
    T c R l hR hl C D hvolume Φ β
  refine ⟨P.pow m, posSemidef_pow_of_even (isHermitian_truncatedExp _ _ hHerm β) hm,
    fun i ↦ ?_⟩
  exact (ProductForm.card_index_pow P m i).trans_le (Nat.pow_le_pow_left (hP i) m)

end ClusterExpansion

end ManyBody
