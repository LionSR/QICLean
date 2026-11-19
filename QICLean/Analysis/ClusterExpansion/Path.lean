/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.SuccPred.Archimedean
import QICLean.Algebra.UnionCoefficientBound
import QICLean.Analysis.ClusterExpansion.Factorization

/-!
# The cluster expansion on a path of terms

For terms `h_0, …, h_{N-1}` adjacent along the path graph, as for a nearest-neighbour chain, the
connected sets of terms are intervals. This file describes the windows and intervals of labels,
the separation of the two sides of an interval, the weights of unions of windows, the number of
crossing intervals, the grouping of the retained expansion by the component crossing a given
label (ALVV, arXiv:1602.08828v2, `thm:cluster` and `eq:rho-expansion`), and the
energy-normalized tail of the expansion truncated at clusters of `r` labels (a correction to
ALVV, `thm:cluster-approx`).

Moved from TNLean (`e113e005`): `TNLean/Lattice/ClusterExpansion/PathIntervals.lean`,
`PathSeparation.lean`, `PathWindowWeights.lean`, `CrossingIntervalCount.lean`,
`PathCrossingExpansion.lean` and `NormalizedPathTail.lean`, in the namespace
`ClusterExpansion`.
-/

/-!
## Intervals in the path of interaction labels

The connected supports in the path graph are exactly its nonempty order intervals.
Every interval with at least `r > 0` labels contains an actual length-`r` window.
Their left endpoints give distinct labels, and every nonempty interval is determined by its
two endpoints. The resulting families characterize the existing cluster cutoff and contain the
actual components of unions of windows.

These are auxiliary geometric results for the interaction-label expansion related to ALVV,
arXiv:1602.08828v2, `thm:cluster-approx`, source lines 1935–1968. The cutoff here counts interaction
labels, rather than the induced physical-site support in the printed statement.
-/

open Finset SimpleGraph

namespace ClusterExpansion

variable {N : ℕ}

/-- A connected support in the path of interaction labels contains every label between two
of its labels. This is the one-dimensional geometry used in the corrected interaction-label
version of ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem ordConnected_of_pathGraph_connected {C : Finset (Fin N)}
    (hC : ((pathGraph N).induce (C : Set (Fin N))).Connected) :
    (C : Set (Fin N)).OrdConnected := by
  refine ⟨fun a ha b hb k hk ↦ ?_⟩
  by_contra hkC
  have key : ∀ (u v : (C : Set (Fin N))), ((pathGraph N).induce (C : Set (Fin N))).Walk u v →
      (u : Fin N).val < k.val → (v : Fin N).val < k.val := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u w v hadj p ih =>
      intro hu
      apply ih
      have hw : (w : Fin N).val ≠ k.val := fun heq ↦ hkC (Fin.ext heq ▸ w.property)
      have hadj' : (u : Fin N).val + 1 = (w : Fin N).val ∨
          (w : Fin N).val + 1 = (u : Fin N).val := pathGraph_adj.mp hadj
      omega
  have ha_ne : a.val ≠ k.val := fun heq ↦ hkC (Fin.ext heq ▸ ha)
  obtain ⟨p⟩ := hC.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  exact (not_lt_of_ge hk.2) (key _ _ p (lt_of_le_of_ne hk.1 ha_ne))

/-- Every nonempty interval of interaction labels is connected in the label path.
Auxiliary to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem pathGraph_connected_of_ordConnected {C : Finset (Fin N)}
    (hC : (C : Set (Fin N)).OrdConnected) (hne : C.Nonempty) :
    ((pathGraph N).induce (C : Set (Fin N))).Connected := by
  let := hC
  have hcov : (Set.range (OrderEmbedding.subtype (· ∈ (C : Set (Fin N))))).OrdConnected := by
    simpa using hC
  have heq : (pathGraph N).induce (C : Set (Fin N)) = hasse (C : Set (Fin N)) := by
    ext u v
    change ((u : Fin N) ⋖ (v : Fin N) ∨ (v : Fin N) ⋖ (u : Fin N)) ↔ (u ⋖ v ∨ v ⋖ u)
    exact or_congr
      (Set.OrdConnected.apply_covBy_apply_iff
        (OrderEmbedding.subtype (· ∈ (C : Set (Fin N)))) hcov)
      (Set.OrdConnected.apply_covBy_apply_iff
        (OrderEmbedding.subtype (· ∈ (C : Set (Fin N)))) hcov)
  rw [heq]
  have : Nonempty (C : Set (Fin N)) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  exact ⟨preconnected_hasse_of_succOrder _⟩

/-- A nonempty interval is determined by its endpoints. Auxiliary to the interaction-label
geometry in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem eq_Icc_of_ordConnected {C : Finset (Fin N)}
    (hC : (C : Set (Fin N)).OrdConnected) (hne : C.Nonempty) :
    C = Icc (C.min' hne) (C.max' hne) := by
  ext k
  exact ⟨fun hk ↦ mem_Icc.mpr ⟨C.min'_le k hk, C.le_max' k hk⟩,
    fun hk ↦ hC.out' (C.min'_mem hne) (C.max'_mem hne) (mem_Icc.mp hk)⟩

/-- An interval with at least `r > 0` labels contains an interval with exactly `r` labels.
Auxiliary to the interaction-label cutoff in ALVV, arXiv:1602.08828v2,
`thm:cluster-approx`. -/
theorem exists_interval_subset_card {C : Finset (Fin N)}
    (hC : (C : Set (Fin N)).OrdConnected) {r : ℕ} (hr : 0 < r) (hcard : r ≤ C.card) :
    ∃ I : Finset (Fin N), I ⊆ C ∧ (I : Set (Fin N)).OrdConnected ∧ I.card = r := by
  have hne : C.Nonempty := Finset.card_pos.mp (hr.trans_le hcard)
  have heq := eq_Icc_of_ordConnected hC hne
  have hlen : r ≤ (C.max' hne).val + 1 - (C.min' hne).val := by
    rw [← Fin.card_Icc, ← heq]
    exact hcard
  let c : Fin N := ⟨(C.min' hne).val + r - 1, by
    have hmax := (C.max' hne).isLt
    omega⟩
  refine ⟨Icc (C.min' hne) c, ?_, ?_, ?_⟩
  · intro k hk
    exact hC.out' (C.min'_mem hne) (C.max'_mem hne)
      ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans (show c ≤ C.max' hne by
        change (C.min' hne).val + r - 1 ≤ (C.max' hne).val
        omega)⟩
  · rw [coe_Icc]
    infer_instance
  · rw [Fin.card_Icc]
    dsimp [c]
    omega

open Classical in
/-- The actual intervals containing exactly `r` interaction labels. Auxiliary to the corrected
interaction-label cutoff in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
noncomputable def pathWindows (N r : ℕ) : Finset (Finset (Fin N)) :=
  {I | (I : Set (Fin N)).OrdConnected ∧ I.card = r}

/-- Membership in the family of length-`r` interaction-label windows. -/
theorem mem_pathWindows {r : ℕ} {I : Finset (Fin N)} :
    I ∈ pathWindows N r ↔ (I : Set (Fin N)).OrdConnected ∧ I.card = r := by
  classical
  simp [pathWindows]

open Classical in
/-- Discarded path supports are precisely those containing a length-`r` window. The graph
components and the windows are constructed from the actual label path. Auxiliary to the corrected
interaction-label cutoff in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem noLargeCluster_pathGraph_iff {r : ℕ} (hr : 0 < r) (A : Finset (Fin N)) :
    NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A ↔
      ¬ ∃ I ∈ pathWindows N r, I ⊆ A := by
  classical
  constructor
  · intro hno ⟨I, hIW, hIA⟩
    have hI := mem_pathWindows.mp hIW
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (hI.2.symm ▸ hr)
    obtain ⟨C, hC, hxC⟩ := exists_isCluster_mem (pathGraph N) (hIA hx)
    have hIC : I ⊆ C := subset_of_connected_of_disjoint_boundary (pathGraph N)
      (pathGraph_connected_of_ordConnected hI.1 ⟨x, hx⟩)
      ⟨x, mem_inter.mpr ⟨hx, hxC⟩⟩ (hC.2.2.mono_left hIA)
    exact hno C hC (hI.2 ▸ Finset.card_le_card hIC)
  · intro hno C hC hsize
    obtain ⟨I, hIC, hIord, hIcard⟩ := exists_interval_subset_card
      (ordConnected_of_pathGraph_connected hC.2.1) hr hsize
    exact hno ⟨I, mem_pathWindows.mpr ⟨hIord, hIcard⟩, hIC.trans hC.1⟩

private theorem eq_of_interval_min_card {I J : Finset (Fin N)}
    (hI : (I : Set (Fin N)).OrdConnected) (hJ : (J : Set (Fin N)).OrdConnected)
    (hneI : I.Nonempty) (hneJ : J.Nonempty) (hmin : I.min' hneI = J.min' hneJ)
    (hcard : I.card = J.card) : I = J := by
  have hIeq := eq_Icc_of_ordConnected hI hneI
  have hJeq := eq_Icc_of_ordConnected hJ hneJ
  have hlenI : I.card = (I.max' hneI).val + 1 - (I.min' hneI).val :=
    (congrArg Finset.card hIeq).trans (Fin.card_Icc _ _)
  have hlenJ : J.card = (J.max' hneJ).val + 1 - (J.min' hneJ).val :=
    (congrArg Finset.card hJeq).trans (Fin.card_Icc _ _)
  have hleI : (I.min' hneI).val ≤ (I.max' hneI).val := I.min'_le _ (I.max'_mem hneI)
  have hleJ : (J.min' hneJ).val ≤ (J.max' hneJ).val := J.min'_le _ (J.max'_mem hneJ)
  have hmax : I.max' hneI = J.max' hneJ := by
    apply Fin.ext
    have hm := congrArg Fin.val hmin
    omega
  exact hIeq.trans ((congrArg₂ Icc hmin hmax).trans hJeq.symm)

/-- The length-`r` windows have distinct chosen labels belonging to them: their left endpoints.
The choice is over the actual family, so an empty chain requires no chosen label. Auxiliary to the
corrected coefficient estimate in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem pathWindows_exists_marker {r : ℕ} (hr : 0 < r) :
    ∃ marker : pathWindows N r → Fin N,
      (∀ I : pathWindows N r, marker I ∈ (I : Finset (Fin N))) ∧ Function.Injective marker := by
  classical
  have hne : ∀ I : pathWindows N r, (I : Finset (Fin N)).Nonempty := fun I ↦
    Finset.card_pos.mp ((mem_pathWindows.mp I.property).2.symm ▸ hr)
  refine ⟨fun I ↦ I.val.min' (hne I), fun I ↦ I.val.min'_mem (hne I), ?_⟩
  intro I J hij
  apply Subtype.ext
  exact eq_of_interval_min_card (mem_pathWindows.mp I.property).1
    (mem_pathWindows.mp J.property).1 (hne I) (hne J) hij
    ((mem_pathWindows.mp I.property).2.trans (mem_pathWindows.mp J.property).2.symm)

open Classical in
/-- The nonempty intervals containing at least `r` interaction labels. Auxiliary to the corrected
interaction-label estimate in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
noncomputable def pathIntervals (N r : ℕ) : Finset (Finset (Fin N)) :=
  {I | I.Nonempty ∧ (I : Set (Fin N)).OrdConnected ∧ r ≤ I.card}

/-- Membership in the family of intervals above the interaction-label cutoff. -/
theorem mem_pathIntervals {r : ℕ} {I : Finset (Fin N)} :
    I ∈ pathIntervals N r ↔ I.Nonempty ∧ (I : Set (Fin N)).OrdConnected ∧ r ≤ I.card := by
  classical
  simp [pathIntervals]

/-- Every interval is determined by its two endpoints, so there are at most `N²` intervals
above any cutoff. Auxiliary to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem card_pathIntervals_le (N r : ℕ) : (pathIntervals N r).card ≤ N ^ 2 := by
  classical
  let f : pathIntervals N r → Fin N × Fin N := fun I ↦
    (I.val.min' (mem_pathIntervals.mp I.property).1,
      I.val.max' (mem_pathIntervals.mp I.property).1)
  have hinj : Function.Injective f := by
    intro I J hij
    apply Subtype.ext
    have hi := mem_pathIntervals.mp I.property
    have hj := mem_pathIntervals.mp J.property
    exact (eq_Icc_of_ordConnected hi.2.1 hi.1).trans
      ((congrArg₂ Icc (congrArg Prod.fst hij) (congrArg Prod.snd hij)).trans
        (eq_Icc_of_ordConnected hj.2.1 hj.1).symm)
  simpa [pow_two] using Fintype.card_le_of_injective f hinj

open Classical in
/-- Every component of a union of length-`r` windows is an interval of at least `r` labels.
The components are the existing graph clusters, not an additional supplied decomposition.
Auxiliary to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem clusters_biUnion_pathWindows_subset {r : ℕ}
    {F : Finset (Finset (Fin N))} (hF : F ⊆ pathWindows N r) :
    clusters (pathGraph N) (F.biUnion id) ⊆ pathIntervals N r := by
  classical
  intro C hCmem
  have hC := (mem_clusters (pathGraph N)).mp hCmem
  obtain ⟨x⟩ := hC.2.1.nonempty
  obtain ⟨I, hIF, hxI⟩ := mem_biUnion.mp (hC.1 x.property)
  have hI := mem_pathWindows.mp (hF hIF)
  have hIU : I ⊆ F.biUnion id := fun k hk ↦ mem_biUnion.mpr ⟨I, hIF, hk⟩
  have hIC : I ⊆ C := subset_of_connected_of_disjoint_boundary (pathGraph N)
    (pathGraph_connected_of_ordConnected hI.1 ⟨x, hxI⟩)
    ⟨x, mem_inter.mpr ⟨hxI, x.property⟩⟩ (hC.2.2.mono_left hIU)
  exact mem_pathIntervals.mpr ⟨⟨x, x.property⟩,
    ordConnected_of_pathGraph_connected hC.2.1, hI.2 ▸ card_le_card hIC⟩

end ClusterExpansion

/-!
## Separation around an actual interval in the label path

The complement of an interval and its graph boundary is the union of the allowed label sets to
its left and right. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013.
-/

open Finset SimpleGraph

namespace ClusterExpansion

variable {N : ℕ}

open Classical in
/-- The actual exterior of a connected interval is its two separated sides, excluding the
boundary labels. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem pathGraph_exterior_eq_sides {C : Finset (Fin N)}
    (hC : ((pathGraph N).induce (C : Set (Fin N))).Connected) :
    (C ∪ boundary (pathGraph N) C)ᶜ =
      {j ∈ (univ : Finset (Fin N)) | ∀ c ∈ C, j.val + 1 < c.val} ∪
        {j ∈ (univ : Finset (Fin N)) | ∀ c ∈ C, c.val + 1 < j.val} := by
  classical
  have hord := ordConnected_of_pathGraph_connected hC
  obtain ⟨p⟩ := hC.nonempty
  ext j
  constructor
  · intro hj
    have hjnot : j ∉ C ∧ j ∉ boundary (pathGraph N) C := by
      simpa only [mem_compl, mem_union, not_or] using hj
    have hnadj : ∀ c ∈ C, ¬ (pathGraph N).Adj j c := fun c hc hjc ↦
      hjnot.2 ((mem_boundary (pathGraph N)).mpr ⟨hjnot.1, c, hc, hjc⟩)
    have hne : j ≠ (p : Fin N) := fun heq ↦ hjnot.1 (heq.symm ▸ p.property)
    rcases lt_or_gt_of_ne hne with hjp | hpj
    · apply mem_union_left
      refine mem_filter.mpr ⟨mem_univ _, fun c hc ↦ ?_⟩
      have hlt : j.val < c.val := by
        by_contra hlt
        exact hjnot.1 (hord.out' hc p.property ⟨show c ≤ j by omega, hjp.le⟩)
      have hneq : j.val + 1 ≠ c.val := fun heq ↦ hnadj c hc (pathGraph_adj.mpr (.inl heq))
      omega
    · apply mem_union_right
      refine mem_filter.mpr ⟨mem_univ _, fun c hc ↦ ?_⟩
      have hlt : c.val < j.val := by
        by_contra hlt
        exact hjnot.1 (hord.out' p.property hc ⟨hpj.le, show j ≤ c by omega⟩)
      have hneq : c.val + 1 ≠ j.val := fun heq ↦ hnadj c hc (pathGraph_adj.mpr (.inr heq))
      omega
  · intro hj
    have hside : (∀ c ∈ C, j.val + 1 < c.val) ∨ (∀ c ∈ C, c.val + 1 < j.val) := by
      simpa only [mem_union, mem_filter, mem_univ, true_and] using hj
    have hjC : j ∉ C := by
      intro hjC
      rcases hside with hs | hs <;> have := hs j hjC <;> omega
    refine mem_compl.mpr fun hjbad ↦ (mem_union.mp hjbad).elim hjC ?_
    intro hjB
    obtain ⟨_, c, hc, hjc⟩ := (mem_boundary (pathGraph N)).mp hjB
    have hadj := pathGraph_adj.mp hjc
    rcases hside with hs | hs <;> have := hs c hc <;> omega

/-- The two exterior sides of a nonempty support are disjoint and have no path edge between
them. Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem pathGraph_sides_separated {C : Finset (Fin N)} (hne : C.Nonempty) :
    Disjoint {j ∈ (univ : Finset (Fin N)) | ∀ c ∈ C, j.val + 1 < c.val}
      {j ∈ (univ : Finset (Fin N)) | ∀ c ∈ C, c.val + 1 < j.val} ∧
      ∀ a ∈ {j ∈ (univ : Finset (Fin N)) | ∀ c ∈ C, j.val + 1 < c.val},
        ∀ b ∈ {j ∈ (univ : Finset (Fin N)) | ∀ c ∈ C, c.val + 1 < j.val},
          ¬ (pathGraph N).Adj a b := by
  obtain ⟨p, hp⟩ := hne
  constructor
  · refine Finset.disjoint_left.mpr fun j hjL hjR ↦ ?_
    have hL := (mem_filter.mp hjL).2 p hp
    have hR := (mem_filter.mp hjR).2 p hp
    omega
  · intro a ha b hb hab
    have hL := (mem_filter.mp ha).2 p hp
    have hR := (mem_filter.mp hb).2 p hp
    have hadj := pathGraph_adj.mp hab
    omega

/-- Removing a single label leaves its two strict order sides. Supporting the no-crossing
case in ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem pathGraph_compl_singleton_eq_sides (p : Fin N) :
    ({p} : Finset (Fin N))ᶜ = {j ∈ (univ : Finset (Fin N)) | j.val < p.val} ∪
      {j ∈ (univ : Finset (Fin N)) | p.val < j.val} := by
  ext j
  simp only [mem_compl, mem_singleton, mem_union, mem_filter, mem_univ, true_and,
    Fin.ext_iff]
  omega

/-- The two strict sides of a deleted label are separated in the actual path graph.
Supporting ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem pathGraph_point_sides_separated (p : Fin N) :
    Disjoint {j ∈ (univ : Finset (Fin N)) | j.val < p.val}
      {j ∈ (univ : Finset (Fin N)) | p.val < j.val} ∧
      ∀ a ∈ {j ∈ (univ : Finset (Fin N)) | j.val < p.val},
        ∀ b ∈ {j ∈ (univ : Finset (Fin N)) | p.val < j.val}, ¬ (pathGraph N).Adj a b := by
  constructor
  · refine Finset.disjoint_left.mpr fun j hjL hjR ↦ ?_
    have hL := (mem_filter.mp hjL).2
    have hR := (mem_filter.mp hjR).2
    omega
  · intro a ha b hb hab
    have hL := (mem_filter.mp ha).2
    have hR := (mem_filter.mp hb).2
    have hadj := pathGraph_adj.mp hab
    omega

end ClusterExpansion

/-!
## Weights of unions of interaction-label windows

A union of nonempty families of length-`r` windows is determined by its actual graph components.
Every component is an interval of at least `r` labels. The component map injects these unions into
nonempty families of such intervals, and the total interval weight is bounded using the finite
product expansion and the endpoint count.

This is auxiliary to a corrected interaction-label estimate related to ALVV,
arXiv:1602.08828v2, `thm:cluster-approx`, source lines 1935–1968. No operator factorization or
matrix product representation is needed for this scalar count.
-/

open Finset SimpleGraph

namespace ClusterExpansion

variable {N r : ℕ}

open Classical in
private theorem prod_pow_card_clusters (U : Finset (Fin N)) (b : ℝ) :
    (∏ C ∈ clusters (pathGraph N) U, b ^ C.card) = b ^ U.card := by
  classical
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← Finset.card_biUnion ((pairwise_clusters (pathGraph N) U).mono'
    (fun _ _ h ↦ h.1))]
  exact congrArg Finset.card (biUnion_clusters (pathGraph N) U)

open Classical in
/-- The total weight of unions of nonempty families of length-`r` windows has an exponential
bound. This counts actual components of the label path. Auxiliary to the corrected
interaction-label tail in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem sum_pow_card_unions_pathWindows_le {r : ℕ} (hr : 0 < r)
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    (∑ U ∈ ((pathWindows N r).powerset.filter Finset.Nonempty).image
        (fun F ↦ F.biUnion id), b ^ U.card) ≤
      Real.exp ((N : ℝ) ^ 2 * b ^ r) - 1 := by
  classical
  let S := ((pathWindows N r).powerset.filter Finset.Nonempty).image (fun F ↦ F.biUnion id)
  have hcomponents : ∀ U ∈ S, (clusters (pathGraph N) U).Nonempty ∧
      clusters (pathGraph N) U ⊆ pathIntervals N r := by
    intro U hU
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hU
    have hFsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1
    obtain ⟨I, hIF⟩ := (Finset.mem_filter.mp hF).2
    have hI := mem_pathWindows.mp (hFsub hIF)
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (hI.2.symm ▸ hr)
    obtain ⟨C, hC, _⟩ := exists_isCluster_mem (pathGraph N)
      (show x ∈ F.biUnion id from Finset.mem_biUnion.mpr ⟨I, hIF, hx⟩)
    exact ⟨⟨C, (mem_clusters (pathGraph N)).mpr hC⟩,
      clusters_biUnion_pathWindows_subset hFsub⟩
  have hinj : Function.Injective (clusters (pathGraph N)) := by
    intro U V heq
    exact (biUnion_clusters (pathGraph N) U).symm.trans
      ((congrArg (fun F ↦ F.biUnion id) heq).trans (biUnion_clusters (pathGraph N) V))
  have hsum : (∑ U ∈ S, b ^ U.card) ≤
      ∑ F ∈ (pathIntervals N r).powerset with F.Nonempty, ∏ C ∈ F, b ^ C.card := by
    apply Finset.sum_le_sum_of_injOn (clusters (pathGraph N)) hinj.injOn
    · intro F hF
      obtain ⟨U, hU, rfl⟩ := mem_image.mp hF
      exact mem_filter.mpr ⟨mem_powerset.mpr (hcomponents U hU).2, (hcomponents U hU).1⟩
    · intro U _
      exact (prod_pow_card_clusters U b).symm.le
    · intro F _ _
      exact Finset.prod_nonneg fun C _ ↦ pow_nonneg hb C.card
  have hprod : (∑ F ∈ (pathIntervals N r).powerset with F.Nonempty,
      ∏ C ∈ F, b ^ C.card) + 1 = ∏ C ∈ pathIntervals N r, (1 + b ^ C.card) := by
    rw [Finset.prod_one_add]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := (pathIntervals N r).powerset) (p := Finset.Nonempty)
      (f := fun F ↦ ∏ C ∈ F, b ^ C.card)
    simpa [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq'] using hsplit
  have hweights : (∑ C ∈ pathIntervals N r, b ^ C.card) ≤ (N : ℝ) ^ 2 * b ^ r := by
    calc
      (∑ C ∈ pathIntervals N r, b ^ C.card) ≤ ∑ _C ∈ pathIntervals N r, b ^ r :=
        Finset.sum_le_sum fun C hC ↦ pow_le_pow_of_le_one hb hb1
          (mem_pathIntervals.mp hC).2.2
      _ = (pathIntervals N r).card * b ^ r := by simp
      _ ≤ (N : ℝ) ^ 2 * b ^ r := mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_pathIntervals_le N r) (pow_nonneg hb r)
  have hprodle : (∏ C ∈ pathIntervals N r, (1 + b ^ C.card)) ≤
      Real.exp (∑ C ∈ pathIntervals N r, b ^ C.card) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun C _ ↦ add_nonneg zero_le_one (pow_nonneg hb C.card))
      (fun C _ ↦ by simpa only [add_comm] using Real.add_one_le_exp (b ^ C.card))
  change (∑ U ∈ S, b ^ U.card) ≤ _
  linarith [hprodle.trans (Real.exp_le_exp.mpr hweights)]

end ClusterExpansion

/-!
## Counting the actual crossing intervals of the label path

The left and right distances from the crossing label determine an interval. This gives the
finite count used for the bond estimate in the interaction-label version of ALVV,
arXiv:1602.08828v2, `thm:cluster` and `eq:rho-expansion`, lines 1298–1303 and 1971–2013.
-/

open Finset SimpleGraph

namespace ClusterExpansion

open Classical in
/-- The actual connected label intervals containing `p` and shorter than `r` number at most
`(r - 1)²`. For `r ≤ 1` this family is empty. Supporting the interaction-label version of ALVV,
arXiv:1602.08828v2, `thm:cluster`, lines 1298–1303 and 1971–2013. -/
theorem card_crossing_intervals_le {N : ℕ} (p : Fin N) (r : ℕ) :
    ((univ : Finset (Finset (Fin N))).filter (fun C : Finset (Fin N) ↦
      p ∈ C ∧ ((pathGraph N).induce (C : Set (Fin N))).Connected ∧ C.card < r)).card ≤
        (r - 1) ^ 2 := by
  classical
  let T := (univ : Finset (Finset (Fin N))).filter (fun C : Finset (Fin N) ↦
    p ∈ C ∧ ((pathGraph N).induce (C : Set (Fin N))).Connected ∧ C.card < r)
  change T.card ≤ _
  by_cases hlow : r ≤ 1
  · have hempty : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro C hC
      have hc := (mem_filter.mp hC).2
      have hpos := Finset.card_pos.mpr ⟨p, hc.1⟩
      omega
    rw [hempty]
    exact Nat.zero_le _
  · have hr : 2 ≤ r := by omega
    have hne (C : T) : C.val.Nonempty := ⟨p, (mem_filter.mp C.property).2.1⟩
    have hb (C : T) : p.val - (C.val.min' (hne C)).val < r - 1 ∧
        (C.val.max' (hne C)).val - p.val < r - 1 := by
      have hc := (mem_filter.mp C.property).2
      have hmin : (C.val.min' (hne C)).val ≤ p.val := C.val.min'_le p hc.1
      have hmax : p.val ≤ (C.val.max' (hne C)).val := C.val.le_max' p hc.1
      have hlen : C.val.card = (C.val.max' (hne C)).val + 1 - (C.val.min' (hne C)).val :=
        (congrArg Finset.card (eq_Icc_of_ordConnected
          (ordConnected_of_pathGraph_connected hc.2.1) (hne C))).trans (Fin.card_Icc _ _)
      omega
    let f : T → Fin (r - 1) × Fin (r - 1) := fun C ↦
      (⟨p.val - (C.val.min' (hne C)).val, (hb C).1⟩,
        ⟨(C.val.max' (hne C)).val - p.val, (hb C).2⟩)
    have hinj : Function.Injective f := by
      intro C D hCD
      have hc := (mem_filter.mp C.property).2
      have hd := (mem_filter.mp D.property).2
      have hmin : C.val.min' (hne C) = D.val.min' (hne D) := by
        apply Fin.ext
        have hCmin : (C.val.min' (hne C)).val ≤ p.val := C.val.min'_le p hc.1
        have hDmin : (D.val.min' (hne D)).val ≤ p.val := D.val.min'_le p hd.1
        have hfst : p.val - (C.val.min' (hne C)).val = p.val - (D.val.min' (hne D)).val :=
          congrArg (fun t : Fin (r - 1) × Fin (r - 1) ↦ t.1.val) hCD
        omega
      have hmax : C.val.max' (hne C) = D.val.max' (hne D) := by
        apply Fin.ext
        have hCmax : p.val ≤ (C.val.max' (hne C)).val := C.val.le_max' p hc.1
        have hDmax : p.val ≤ (D.val.max' (hne D)).val := D.val.le_max' p hd.1
        have hsnd : (C.val.max' (hne C)).val - p.val = (D.val.max' (hne D)).val - p.val :=
          congrArg (fun t : Fin (r - 1) × Fin (r - 1) ↦ t.2.val) hCD
        omega
      apply Subtype.ext
      exact (eq_Icc_of_ordConnected (ordConnected_of_pathGraph_connected hc.2.1) (hne C)).trans
        ((congrArg₂ Icc hmin hmax).trans
          (eq_Icc_of_ordConnected (ordConnected_of_pathGraph_connected hd.2.1) (hne D)).symm)
    simpa [pow_two] using Fintype.card_le_of_injective f hinj

end ClusterExpansion

/-!
## The actual path expansion grouped by the crossing component

The two side factors are constructed as retained finite sums on the actual allowed label sets.
Supporting the interaction-label version of ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, source lines 1971–2013. No operator rank or matrix product representation
is assumed here.

**Local fix (interaction-label cutoff):** this decomposition uses components of the actual
label path. It does not identify the resulting truncation with the source's minimal physical-site
support selector; see `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Finset SimpleGraph

namespace ClusterExpansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N r : ℕ}

open Classical in
/-- Exact no-crossing and crossing-component decomposition on the actual label path.
All side factors are actual retained-support sums. The case `r = 1` has no crossing component.
Supporting the interaction-label expansion in ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, source lines 1971–2013. -/
theorem truncatedExp_pathGraph_eq_crossing_components
    (h : Fin N → Matrix ι ι ℂ)
    (hcomm : ∀ j k, ¬ (pathGraph N).Adj j k → Commute (h j) (h k))
    (p : Fin N) (β : ℝ) :
    truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β =
      (∑ A ∈ ({j ∈ (univ : Finset (Fin N)) | j.val < p.val}).powerset
          with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A, clusterOp h A β) *
        (∑ A ∈ ({j ∈ (univ : Finset (Fin N)) | p.val < j.val}).powerset
          with NoLargeCluster (pathGraph N) (fun C ↦ r ≤ C.card) A, clusterOp h A β) +
      ∑ C ∈ (univ : Finset (Finset (Fin N))).filter (fun C : Finset (Fin N) ↦
          p ∈ C ∧ ((pathGraph N).induce (C : Set (Fin N))).Connected ∧ C.card < r),
        clusterOp h C β *
          ((∑ A ∈ ({j ∈ (univ : Finset (Fin N)) |
                ∀ c ∈ C, j.val + 1 < c.val}).powerset
              with NoLargeCluster (pathGraph N) (fun D ↦ r ≤ D.card) A, clusterOp h A β) *
            ∑ A ∈ ({j ∈ (univ : Finset (Fin N)) |
                ∀ c ∈ C, c.val + 1 < j.val}).powerset
              with NoLargeCluster (pathGraph N) (fun D ↦ r ≤ D.card) A, clusterOp h A β) := by
  classical
  let good := NoLargeCluster (pathGraph N) (fun C : Finset (Fin N) ↦ r ≤ C.card)
  have hsplit : (∑ A : Finset (Fin N) with good A, clusterOp h A β) =
      (∑ A : Finset (Fin N) with good A ∧ p ∉ A, clusterOp h A β) +
        ∑ A : Finset (Fin N) with good A ∧ p ∈ A, clusterOp h A β := by
    have hs := Finset.sum_filter_add_sum_filter_not (s := univ.filter good)
      (p := fun A ↦ p ∉ A) (f := fun A ↦ clusterOp h A β)
    simpa only [Finset.filter_filter, not_not] using hs.symm
  have hnoCross : (∑ A : Finset (Fin N) with good A ∧ p ∉ A, clusterOp h A β) =
      ∑ A ∈ (({p} : Finset (Fin N))ᶜ).powerset with good A, clusterOp h A β := by
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext A
    simp only [mem_filter, mem_univ, true_and, mem_powerset, Finset.subset_compl_singleton]
    exact and_comm
  rw [truncatedExp_eq_sum_clusterOp]
  change (∑ A : Finset (Fin N) with good A, clusterOp h A β) = _
  rw [hsplit, hnoCross, sum_retained_clusterOp_containing_eq (pathGraph N)
    (fun C ↦ r ≤ C.card) h hcomm p β]
  simp only [not_le]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [pathGraph_compl_singleton_eq_sides]
    exact sum_retained_clusterOp_union_eq_mul (pathGraph N) (fun C ↦ r ≤ C.card) h hcomm
      (pathGraph_point_sides_separated p).1 (pathGraph_point_sides_separated p).2 β
  · refine Finset.sum_congr rfl fun C hCmem ↦ ?_
    have hc := (mem_filter.mp hCmem).2
    apply congrArg (clusterOp h C β * ·)
    rw [pathGraph_exterior_eq_sides hc.2.1]
    exact sum_retained_clusterOp_union_eq_mul (pathGraph N) (fun D ↦ r ≤ D.card) h hcomm
      (pathGraph_sides_separated ⟨p, hc.1⟩).1 (pathGraph_sides_separated ⟨p, hc.1⟩).2 β

end ClusterExpansion

/-!
## The energy-normalized interaction-label cluster tail on a path

For `H = ∑ i, h i` with Hermitian terms of operator norm at most one and `H ≥ lambda I`, the
existing label-path truncation has energy-normalized error at most
`exp (N² (2 (exp β - 1))^r) - 1`, provided `r > 0`, `β ≥ 0`, and `2 (exp β - 1) ≤ 1`.
The proof groups exact inclusion--exclusion coefficients by their mandatory label union, applies
the normalized mandatory-label norm bound, and sums weights of actual interval components.
No commutation assumption on the terms is needed for this norm estimate.

**Local fix (cutoff and energy normalization):** this is a corrected auxiliary estimate related
to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`, source lines 1270–1291 and 1935–1968.
The cutoff counts interaction labels, the norm is normalized by a supplied lower energy, and the
factor `2` accounts for the grouped inclusion--exclusion coefficients. The printed
physical-support approximation remains false; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`. The spatial cut and matrix product operator
conclusions are separate and are not asserted here.
-/

open Finset SimpleGraph
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ClusterExpansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem sum_bad_clusterOp_grouped (h : κ → Matrix ι ι ℂ)
    (W : Finset (Finset κ)) (β : ℝ) :
    (∑ A : Finset κ with ∃ I ∈ W, I ⊆ A, clusterOp h A β) =
      ∑ U ∈ (W.powerset.filter Finset.Nonempty).image (fun F ↦ F.biUnion id),
        (∑ F ∈ W.powerset with F.Nonempty ∧ F.biUnion id = U,
          (-1 : ℤ) ^ (F.card + 1)) • clusterPart (∑ i, h i) h ∅ U β := by
  classical
  rw [sum_clusterOp_bad_windows_eq]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun F : Finset (Finset κ) ↦ F.biUnion id)
    (t := (W.powerset.filter Finset.Nonempty).image (fun F ↦ F.biUnion id))
    (fun F hF ↦ Finset.mem_image.mpr ⟨F, hF, rfl⟩)]
  refine Finset.sum_congr rfl fun U _ ↦ ?_
  rw [Finset.filter_filter, Finset.sum_smul]
  refine Finset.sum_congr rfl fun F hF ↦ ?_
  rw [(Finset.mem_filter.mp hF).2.2]

private theorem norm_sum_bad_clusterOp_le (h : κ → Matrix ι ι ℂ)
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (W : Finset (Finset κ)) (marker : W → κ)
    (hmarker : ∀ I : W, marker I ∈ (I : Finset κ)) (hinj : Function.Injective marker)
    (lambda β : ℝ) (hlo : (lambda : ℂ) • 1 ≤ ∑ i, h i) (hβ : 0 ≤ β) :
    Real.exp (β * lambda) * ‖∑ A : Finset κ with ∃ I ∈ W, I ⊆ A, clusterOp h A β‖ ≤
      ∑ U ∈ (W.powerset.filter Finset.Nonempty).image (fun F ↦ F.biUnion id),
        (2 * (Real.exp β - 1)) ^ U.card := by
  classical
  rw [sum_bad_clusterOp_grouped]
  let S := (W.powerset.filter Finset.Nonempty).image (fun F ↦ F.biUnion id)
  let c := fun U ↦ ∑ F ∈ W.powerset with F.Nonempty ∧ F.biUnion id = U,
    (-1 : ℤ) ^ (F.card + 1)
  have hH : (∑ i, h i).IsHermitian :=
    (isSelfAdjoint_sum _ fun i _ ↦ (hh i).isSelfAdjoint).isHermitian
  change Real.exp (β * lambda) * ‖∑ U ∈ S, c U • clusterPart (∑ i, h i) h ∅ U β‖ ≤ _
  calc
    _ ≤ Real.exp (β * lambda) * ∑ U ∈ S, ‖c U • clusterPart (∑ i, h i) h ∅ U β‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_pos _).le
    _ = ∑ U ∈ S, ‖c U‖ * (Real.exp (β * lambda) * ‖clusterPart (∑ i, h i) h ∅ U β‖) := by
      simp_rw [norm_zsmul ℝ, Int.norm_cast_real]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun U _ ↦ by ring
    _ ≤ ∑ U ∈ S, (2 : ℝ) ^ U.card * (Real.exp β - 1) ^ U.card := by
      apply Finset.sum_le_sum
      intro U _
      exact mul_le_mul (Finset.norm_sum_powerset_biUnion_sign_le_two_pow W marker hmarker hinj U)
        (norm_clusterPart_empty_boundary_le_of_lower_bound (∑ i, h i) h U hH
          (fun i _ ↦ hh i) (fun i _ ↦ hnorm i) lambda β hlo hβ)
        (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (by positivity)
    _ = _ := by
      simp only [mul_pow]
      rfl

open Classical in
/-- The corrected energy-normalized interaction-label cluster tail on the actual path graph.
For Hermitian norm-one terms and a supplied lower energy `lambda`, the discarded operator has
normalized norm at most `exp (N² (2 (exp β - 1))^r) - 1`. The cutoff counts interaction labels.
This auxiliary correction to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`, source lines
1270–1291 and 1935–1968, does not assert the false printed physical-support estimate or a matrix
product operator representation; see `docs/paper-gaps/alvv16_cluster_approximation.tex`. -/
theorem norm_exp_sub_truncatedExp_pathGraph_le {N r : ℕ} (hr : 0 < r)
    (h : Fin N → Matrix ι ι ℂ) (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (lambda β : ℝ) (hlo : (lambda : ℂ) • 1 ≤ ∑ i, h i) (hβ : 0 ≤ β)
    (hsmall : 2 * (Real.exp β - 1) ≤ 1) :
    Real.exp (β * lambda) *
      ‖NormedSpace.exp (-(β • ∑ i, h i)) -
        truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β‖ ≤
      Real.exp ((N : ℝ) ^ 2 * (2 * (Real.exp β - 1)) ^ r) - 1 := by
  classical
  rw [exp_sub_truncatedExp_eq_sum_clusterPart_windows (pathGraph N)
    (fun C ↦ r ≤ C.card) (pathWindows N r) (fun A ↦ noLargeCluster_pathGraph_iff hr A) h β,
    ← sum_clusterOp_bad_windows_eq]
  obtain ⟨marker, hmarker, hinj⟩ := pathWindows_exists_marker (N := N) hr
  exact (norm_sum_bad_clusterOp_le h hh hnorm (pathWindows N r) marker hmarker hinj
    lambda β hlo hβ).trans (sum_pow_card_unions_pathWindows_le hr
      (mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_exp hβ))) hsmall)

end ClusterExpansion
