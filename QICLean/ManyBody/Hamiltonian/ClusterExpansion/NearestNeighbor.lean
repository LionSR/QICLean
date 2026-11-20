/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ClusterExpansion.Path
import QICLean.Algebra.OperatorSchmidtBounds
import QICLean.ManyBody.Sites.OperatorSchmidtRank
import QICLean.ManyBody.Hamiltonian.ClusterExpansion.Factorization
import QICLean.ManyBody.Sites.Lattice.Chain

/-!
# The cluster expansion of a nearest-neighbour chain

For a chain of `N + 1` sites with interaction terms on the bonds `{i, i + 1}`, the overlap graph of
the bonds is the path graph of the labels. The truncated expansion at clusters of `r` labels then
splits into a no-crossing product and a sum over the components crossing a given bond, whose side
sums act on the two sides of the cut; an interval of fewer than `r` labels acts on at most `r`
sites. Hence the truncation has operator Schmidt rank at most `r² q^r` at every interior cut
(ALVV, arXiv:1602.08828v2, `thm:cluster` and `eq:rho-expansion`, lines 1298–1303 and 1971–2013,
corrected to interaction labels).

**Local fix (interaction-label cutoff):** these results use the components of the label path,
not the minimal physical support of a word product; a component of `s` labels is designated on
`s + 1` sites. The printed physical-support estimate is distinct, see
https://sirui-lu.com/TNLean/paper-gaps/alvv16_cluster_approximation.pdf.

## Main results

* `ManyBody.ClusterExpansion.truncatedExp_nearestNeighbor_eq_crossing_components`.
* `ManyBody.ClusterExpansion.retained_nearestNeighbor_interval_mem_supportedOperators` and its
  left and right forms.
* `ManyBody.ClusterExpansion.operatorSchmidtRank_truncatedExp_nearestNeighbor_le`.

Moved from TNLean (`e113e005`): `TNLean/Lattice/ClusterExpansion/NearestNeighborPath.lean`,
`NearestNeighborSupport.lean`, `NearestNeighborIntervalRank.lean` and
`NearestNeighborTruncationRank.lean`. Changes: the terms are those of an interaction on the bonds
`ManyBody.chainBond N` of `ManyBody/Sites/Lattice/Chain.lean`, which also holds the overlap
graph of the bonds and the size of their union; the support statements hold for any finite
basis types and are stated as membership in `supportedOperators` (renamed from
`isSupportedOn_retained_…`); the rank statements are on `Fin q` sites and state the cut
through `ManyBody.cutEquiv`.
-/

open Finset SimpleGraph Matrix _root_.ClusterExpansion

namespace ManyBody

namespace ClusterExpansion

section Path

variable {N : ℕ} {X : Fin (N + 1) → Type*} [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]

/-- Terms on the bonds commute at labels that are not adjacent on the path. -/
theorem commute_nearestNeighbor_of_not_adj (Φ : Interaction X (chainBond N)) :
    ∀ j k, ¬ (pathGraph N).Adj j k → Commute (Φ.term j) (Φ.term k) := by
  simpa only [overlapGraph_chainBond_eq_pathGraph] using commute_of_not_adj_overlapGraph Φ

open Classical in
/-- The nearest-neighbour label truncation splits into one no-crossing product and the sum over
the components crossing a given bond. Supporting the interaction-label version of ALVV,
arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem truncatedExp_nearestNeighbor_eq_crossing_components {r : ℕ}
    (Φ : Interaction X (chainBond N)) (p : Fin N) (β : ℝ) :
    let F := fun B : Finset (Fin N) ↦
      ∑ A ∈ B.powerset with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A,
        clusterOp Φ.term A β
    truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) Φ.term β =
      F {j ∈ univ | j.val < p.val} * F {j ∈ univ | p.val < j.val} +
        ∑ C ∈ (univ : Finset (Finset (Fin N))).filter (fun C : Finset (Fin N) ↦
            p ∈ C ∧ ((pathGraph N).induce (C : Set (Fin N))).Connected ∧ C.card < r),
          clusterOp Φ.term C β *
            (F {j ∈ univ | ∀ c ∈ C, j.val + 1 < c.val} *
              F {j ∈ univ | ∀ c ∈ C, c.val + 1 < j.val}) :=
  truncatedExp_pathGraph_eq_crossing_components Φ.term (commute_nearestNeighbor_of_not_adj Φ) p β

open Classical in
/-- A retained sum over the labels in a physical interval acts only on that interval. Supporting
ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem retained_nearestNeighbor_interval_mem_supportedOperators {r : ℕ}
    (Φ : Interaction X (chainBond N)) (B : Finset (Fin N)) (a b : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val + 1 < b) (β : ℝ) :
    ∑ A ∈ B.powerset with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A,
        clusterOp Φ.term A β ∈
      supportedOperators X {v ∈ (univ : Finset (Fin (N + 1))) | a ≤ v.val ∧ v.val < b} := by
  refine supportedOperators_mono ?_
    (sum_retained_clusterOp_mem_supportedOperators (pathGraph N) (fun C ↦ r ≤ C.card) Φ B β)
  intro v hv
  obtain ⟨i, hi, hvi⟩ := mem_biUnion.mp hv
  have hb := hB i hi
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  simp only [chainBond, mem_insert, mem_singleton] at hvi
  rcases hvi with rfl | rfl <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

open Classical in
/-- The retained sum of labels strictly left of a bond acts on the left side of its cut.
Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem retained_nearestNeighbor_left_mem_supportedOperators {r : ℕ}
    (Φ : Interaction X (chainBond N)) (p : Fin N) (B : Finset (Fin N)) (hB : ∀ i ∈ B, i.val < p.val)
    (β : ℝ) :
    ∑ A ∈ B.powerset with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A,
        clusterOp Φ.term A β ∈
      supportedOperators X {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val} := by
  refine supportedOperators_mono ?_ (retained_nearestNeighbor_interval_mem_supportedOperators
    Φ B 0 (p.val + 1) (fun i hi ↦ ⟨Nat.zero_le _, Nat.add_lt_add_right (hB i hi) 1⟩) β)
  exact fun v hv ↦ mem_filter.mpr ⟨mem_univ _, Nat.le_of_lt_succ (mem_filter.mp hv).2.2⟩

open Classical in
/-- The retained sum of labels strictly right of a bond acts on the right side of its cut.
Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem retained_nearestNeighbor_right_mem_supportedOperators {r : ℕ}
    (Φ : Interaction X (chainBond N)) (p : Fin N) (B : Finset (Fin N)) (hB : ∀ i ∈ B, p.val < i.val)
    (β : ℝ) :
    ∑ A ∈ B.powerset with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A,
        clusterOp Φ.term A β ∈
      supportedOperators X {v ∈ (univ : Finset (Fin (N + 1))) | p.val < v.val} := by
  refine supportedOperators_mono ?_ (retained_nearestNeighbor_interval_mem_supportedOperators
    Φ B (p.val + 1) (N + 1)
    (fun i hi ↦ ⟨Nat.succ_le_of_lt (hB i hi), Nat.add_lt_add_right i.isLt 1⟩) β)
  exact fun v hv ↦ mem_filter.mpr ⟨mem_univ _, Nat.lt_of_succ_le (mem_filter.mp hv).2.1⟩

end Path

section Rank

variable {N q : ℕ}

/-- The exact-label coefficient of an interval with fewer than `r` labels has operator Schmidt
rank at most `q ^ r` at every cut. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`,
lines 1971–2013. -/
theorem operatorSchmidtRank_clusterOp_nearestNeighbor_le {r : ℕ} (hq : 1 ≤ q)
    (Φ : Interaction (fun _ : Fin (N + 1) ↦ Fin q) (chainBond N)) {C : Finset (Fin N)}
    (hC : ((pathGraph N).induce (C : Set (Fin N))).Connected) (hshort : C.card < r)
    (A : Finset (Fin (N + 1))) (β : ℝ) :
    operatorSchmidtRank (reindex (cutEquiv (fun _ ↦ Fin q) A) (cutEquiv (fun _ ↦ Fin q) A)
      (clusterOp Φ.term C β)) ≤ q ^ r :=
  (ManyBody.IsSupportedOn.operatorSchmidtRank_cutOperator_le_pow_card hq (A := A)
    (clusterOp_mem_supportedOperators Φ C β)).trans
    (Nat.pow_le_pow_right hq ((card_biUnion_chainBond_le hC).trans (Nat.succ_le_of_lt hshort)))

open Classical in
/-- The nearest-neighbour truncation has operator Schmidt rank at most one plus the number of
crossing intervals times the interval rank. Supporting ALVV, arXiv:1602.08828v2, `thm:cluster`,
lines 1298–1303 and 1971–2013. -/
theorem operatorSchmidtRank_truncatedExp_nearestNeighbor_le_count {r : ℕ} (hq : 1 ≤ q)
    (Φ : Interaction (fun _ : Fin (N + 1) ↦ Fin q) (chainBond N)) (p : Fin N) (β : ℝ) :
    operatorSchmidtRank
      (reindex (cutEquiv (fun _ ↦ Fin q) {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val})
        (cutEquiv (fun _ ↦ Fin q) {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val})
        (truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) Φ.term β)) ≤
      1 + (r - 1) ^ 2 * q ^ r := by
  classical
  let A := {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val}
  let R := {v ∈ (univ : Finset (Fin (N + 1))) | p.val < v.val}
  let F := fun B : Finset (Fin N) ↦
    ∑ S ∈ B.powerset with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) S,
      clusterOp Φ.term S β
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (cutEquiv (fun _ : Fin (N + 1) ↦ Fin q) A)
  have hleft (B : Finset (Fin N)) (hB : ∀ i ∈ B, i.val < p.val) :
      operatorSchmidtRank (φ (F B)) ≤ 1 :=
    ManyBody.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one
      (retained_nearestNeighbor_left_mem_supportedOperators Φ p B hB β) (.inl Finset.Subset.rfl)
  have hright (B : Finset (Fin N)) (hB : ∀ i ∈ B, p.val < i.val) :
      operatorSchmidtRank (φ (F B)) ≤ 1 := by
    have hd : Disjoint R A :=
      Finset.disjoint_left.mpr fun v hvR hvA ↦
        (not_lt_of_ge (mem_filter.mp hvA).2) (mem_filter.mp hvR).2
    exact ManyBody.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one
      (retained_nearestNeighbor_right_mem_supportedOperators Φ p B hB β) (.inr hd)
  have hprod (B D : Finset (Fin N)) (hB : ∀ i ∈ B, i.val < p.val)
      (hD : ∀ i ∈ D, p.val < i.val) : operatorSchmidtRank (φ (F B * F D)) ≤ 1 := by
    rw [map_mul]
    exact (Matrix.operatorSchmidtRank_mul_le _ _).trans
      (Nat.mul_le_mul (hleft B hB) (hright D hD))
  let T := (univ : Finset (Finset (Fin N))).filter (fun C : Finset (Fin N) ↦
    p ∈ C ∧ ((pathGraph N).induce (C : Set (Fin N))).Connected ∧ C.card < r)
  have hcross (C : Finset (Fin N)) (hCmem : C ∈ T) :
      operatorSchmidtRank (φ (clusterOp Φ.term C β *
        (F {j ∈ univ | ∀ c ∈ C, j.val + 1 < c.val} *
          F {j ∈ univ | ∀ c ∈ C, c.val + 1 < j.val}))) ≤ q ^ r := by
    have hc := (mem_filter.mp hCmem).2
    have hpairs := hprod {j ∈ univ | ∀ c ∈ C, j.val + 1 < c.val}
      {j ∈ univ | ∀ c ∈ C, c.val + 1 < j.val}
      (fun i hi ↦ by have := (mem_filter.mp hi).2 p hc.1; omega)
      (fun i hi ↦ by have := (mem_filter.mp hi).2 p hc.1; omega)
    have he := operatorSchmidtRank_clusterOp_nearestNeighbor_le hq Φ hc.2.1 hc.2.2 A β
    change operatorSchmidtRank (φ (clusterOp Φ.term C β)) ≤ q ^ r at he
    rw [map_mul]
    simpa only [Nat.mul_one] using (Matrix.operatorSchmidtRank_mul_le _ _).trans
      (Nat.mul_le_mul he hpairs)
  have hdec : truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) Φ.term β =
      F {j ∈ univ | j.val < p.val} * F {j ∈ univ | p.val < j.val} +
        ∑ C ∈ T, clusterOp Φ.term C β *
          (F {j ∈ univ | ∀ c ∈ C, j.val + 1 < c.val} *
            F {j ∈ univ | ∀ c ∈ C, c.val + 1 < j.val}) :=
    truncatedExp_nearestNeighbor_eq_crossing_components Φ p β
  change operatorSchmidtRank (φ (truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) Φ.term β)) ≤ _
  rw [hdec, map_add, map_sum]
  refine (Matrix.operatorSchmidtRank_add_le _ _).trans
    ((Nat.add_le_add (hprod _ _ (fun i hi ↦ (mem_filter.mp hi).2)
      (fun i hi ↦ (mem_filter.mp hi).2)) (Matrix.operatorSchmidtRank_sum_le T _)).trans ?_)
  refine (Nat.add_le_add_left (Finset.sum_le_sum hcross) 1).trans ?_
  simpa [T] using Nat.add_le_add_left
    (Nat.mul_le_mul_right (q ^ r) (card_crossing_intervals_le p r)) 1

open Classical in
/-- The nearest-neighbour label truncation has operator Schmidt rank at most `r² q^r` at every
interior cut. Supporting the corrected interaction-label form of ALVV, arXiv:1602.08828v2,
`thm:cluster`, lines 1298–1303 and 1971–2013. -/
theorem operatorSchmidtRank_truncatedExp_nearestNeighbor_le {r : ℕ} (hq : 1 ≤ q) (hr : 0 < r)
    (Φ : Interaction (fun _ : Fin (N + 1) ↦ Fin q) (chainBond N)) (p : Fin N) (β : ℝ) :
    operatorSchmidtRank
      (reindex (cutEquiv (fun _ ↦ Fin q) {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val})
        (cutEquiv (fun _ ↦ Fin q) {v ∈ (univ : Finset (Fin (N + 1))) | v.val ≤ p.val})
        (truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) Φ.term β)) ≤ r ^ 2 * q ^ r := by
  refine (operatorSchmidtRank_truncatedExp_nearestNeighbor_le_count hq Φ p β).trans ?_
  have hpow : 1 ≤ q ^ r := one_le_pow₀ hq
  have hsq : 1 + (r - 1) ^ 2 ≤ r ^ 2 := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  calc
    1 + (r - 1) ^ 2 * q ^ r ≤ (1 + (r - 1) ^ 2) * q ^ r := by nlinarith
    _ ≤ r ^ 2 * q ^ r := Nat.mul_le_mul_right _ hsq

end Rank

end ClusterExpansion

end ManyBody
