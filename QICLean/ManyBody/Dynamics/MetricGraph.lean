/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.Abel
import QICLean.ManyBody.Sites.Lattice.RingBlocks

/-!
# The graph of a metric interaction range

On a pseudometric space of sites, `metricRangeGraph R` joins distinct sites at distance at most
the interaction range `R`. A bound `S` on the number of sites in each ball of radius `R` bounds
the degree of the graph, every ball of radius `R` has graph diameter at most two through its
centre, and physical distance is at most `R` times graph distance. These are the conventions of
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 169–190.

A ball of radius `r` in the coordinate maximum metric on `ℤ^D` lies in a box of side
`2 ⌈r⌉₊ + 1`, so distinct interaction centres have polynomial ball growth. This is the volume
growth of Hastings' local index count, arXiv:cond-mat/0508554v3, lines 1273–1275.

Moved from TNLean, `TNLean/Lattice/MetricInteractionGraph.lean` and
`IntegerLatticeBallCount.lean` at commit `e113e005`, with no change to the statements.

The cyclic distance `min (|i - v|, M - |i - v|)` of the ring of `M` sites is the least absolute
residue of `i - v` in `ZMod M`, so it satisfies the triangle inequality and makes `Fin M` a metric
space. Each of its balls of radius `R` has at most `2 ⌈R⌉₊ + 1` sites.

## Main definitions

* `ManyBody.metricRangeGraph` — the graph of pairs within the interaction range.
* `ManyBody.metricRangeBall` — the metric ball of radius `R`, as a region.
* `ManyBody.cyclicMetricSpace` — the cyclic metric of the ring.

## Main results

* `ManyBody.dist_le_range_mul_graphDist` — physical distance against graph distance.
* `ManyBody.metricRangeGraph_neighbor_card_le` — the degree bound.
* `ManyBody.card_centres_ball_le_polynomial_of_isometry` — polynomial ball growth.
* `ManyBody.card_metricRangeBall_cyclicMetricSpace_le` — the balls of the cyclic metric.
-/

namespace ManyBody


variable {ι : Type*} [PseudoMetricSpace ι]

/-- The graph of pairs within the interaction range.
Hastings, arXiv:cond-mat/0508554v3, lines 180–190. -/
def metricRangeGraph (R : ℝ) : SimpleGraph ι where
  Adj x y := x ≠ y ∧ dist x y ≤ R
  symm := ⟨fun x y h => ⟨h.1.symm, by simpa only [dist_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance (R : ℝ) : DecidableRel (metricRangeGraph (ι := ι) R).Adj :=
  fun _ _ => Classical.propDecidable _

/-- A metric-near pair has graph distance at most one, allowing coincident sites.
Hastings, arXiv:cond-mat/0508554v3, lines 180–190. -/
theorem metricRangeGraph_edist_le_one {R : ℝ} {x y : ι} (hxy : dist x y ≤ R) :
    (metricRangeGraph R).edist x y ≤ 1 := by
  apply SimpleGraph.edist_le_one_iff_adj_or_eq.mpr
  by_cases h : x = y
  · exact Or.inr h
  · exact Or.inl ⟨h, hxy⟩

/-- An interaction support has graph diameter at most two through its centre.
Hastings, arXiv:cond-mat/0508554v3, lines 180–190. -/
theorem metricRangeGraph_edist_le_two {R : ℝ} {a x y : ι}
    (hx : dist x a ≤ R) (hy : dist y a ≤ R) :
    (metricRangeGraph R).edist x y ≤ 2 := by
  exact ((metricRangeGraph R).edist_triangle).trans
    (show (metricRangeGraph R).edist x a + (metricRangeGraph R).edist a y ≤ 2 from
      (add_le_add (metricRangeGraph_edist_le_one hx)
        (metricRangeGraph_edist_le_one (by simpa only [dist_comm] using hy))))

/-- Physical distance is bounded by the length of a walk times the range.
Hastings, arXiv:cond-mat/0508554v3, lines 180–190. -/
theorem dist_le_range_mul_walkLength {R : ℝ} {x y : ι}
    (p : (metricRangeGraph R).Walk x y) : dist x y ≤ R * (p.length : ℝ) := by
  induction p with
  | nil => simp
  | @cons x z y h p ih =>
    calc dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
      _ ≤ R + R * (p.length : ℝ) := add_le_add h.2 ih
      _ = R * ((SimpleGraph.Walk.cons h p).length : ℝ) := by
        simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- Along a connected component the intrinsic graph distance bounds physical distance.
Hastings, arXiv:cond-mat/0508554v3, lines 180–190. -/
theorem dist_le_range_mul_graphDist {R : ℝ} {x y : ι}
    (hxy : (metricRangeGraph R).Reachable x y) :
    dist x y ≤ R * ((metricRangeGraph R).dist x y : ℝ) := by
  obtain ⟨p, hp⟩ := hxy.exists_walk_length_eq_dist
  simpa only [hp] using dist_le_range_mul_walkLength p

/-- Physical separation gives an integer graph-distance threshold by rounding up.
Hastings, arXiv:cond-mat/0508554v3, lines 180–190 and 1469–1505. -/
theorem metricRangeGraph_edist_lower_ceil {R t : ℝ} (hR : 0 < R) {x y : ι}
    (hsep : R * t ≤ dist x y) :
    (Nat.ceil t : ℕ∞) ≤ (metricRangeGraph R).edist x y := by
  by_cases htop : (metricRangeGraph R).edist x y = ⊤
  · rw [htop]; exact le_top
  · have hphys := dist_le_range_mul_graphDist
      (SimpleGraph.edist_ne_top_iff_reachable.mp htop)
    have hm : t ≤ ((metricRangeGraph R).dist x y : ℝ) :=
      le_of_mul_le_mul_left (hsep.trans hphys) hR
    have hnat : Nat.ceil t ≤ (metricRangeGraph R).dist x y := Nat.ceil_le.mpr hm
    exact (show (Nat.ceil t : ℕ∞) ≤ ((metricRangeGraph R).dist x y : ℕ∞) by
      exact_mod_cast hnat).trans SimpleGraph.natCast_dist_le_edist

/-- At range zero, positive physical separation puts sites in different components.
Hastings, arXiv:cond-mat/0508554v3, lines 180–190. -/
theorem metricRangeGraph_zero_edist_eq_top {x y : ι} (hxy : 0 < dist x y) :
    (metricRangeGraph 0).edist x y = ⊤ := by
  by_contra h
  have hphys := dist_le_range_mul_graphDist
    (SimpleGraph.edist_ne_top_iff_reachable.mp h)
  simp only [zero_mul] at hphys
  exact (not_le_of_gt hxy) hphys

section Finite

variable [Fintype ι]

/-- The finite closed metric ball used as an interaction support.
Hastings, arXiv:cond-mat/0508554v3, lines 180–190. -/
noncomputable def metricRangeBall (R : ℝ) (x : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun y => dist x y ≤ R

/-- Membership in the finite closed metric ball. -/
@[simp]
theorem mem_metricRangeBall {R : ℝ} {x y : ι} :
    y ∈ metricRangeBall R x ↔ dist x y ≤ R := by
  classical
  simp only [metricRangeBall, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The finite ball has the usual metric closed ball as its underlying set. -/
@[simp]
theorem coe_metricRangeBall (R : ℝ) (x : ι) :
    (metricRangeBall R x : Set ι) = Metric.closedBall x R := by
  ext y
  simp only [Finset.mem_coe, mem_metricRangeBall, Metric.mem_closedBall, dist_comm]

/-- A centre belongs to its metric interaction ball at every nonnegative range. -/
theorem self_mem_metricRangeBall {R : ℝ} (hR : 0 ≤ R) (x : ι) :
    x ∈ metricRangeBall R x := by
  simpa only [mem_metricRangeBall, dist_self] using hR

/-- The source's bound on metric balls bounds the graph degree directly.
Hastings, arXiv:cond-mat/0508554v3, lines 180–185. -/
theorem metricRangeGraph_neighbor_card_le {R : ℝ} {S : ℕ}
    (hS : ∀ x : ι, (metricRangeBall R x).card ≤ S) (x : ι) :
    ((metricRangeGraph R).neighborFinset x).card ≤ S := by
  refine (Finset.card_le_card ?_).trans (hS x)
  intro y hy
  have hxy : (metricRangeGraph R).Adj x y := by
    simpa only [SimpleGraph.mem_neighborFinset] using hy
  exact mem_metricRangeBall.mpr hxy.2

/-- Full metric interaction balls satisfy the diameter condition for the graph
Lieb--Robinson estimate. Hastings, arXiv:cond-mat/0508554v3, lines 180–190. -/
theorem metricRangeBall_graph_diameter_le_two (R : ℝ) (i : ι) :
    ∀ x ∈ metricRangeBall R i, ∀ y ∈ metricRangeBall R i,
      (metricRangeGraph R).edist x y ≤ 2 := by
  intro x hx y hy
  exact metricRangeGraph_edist_le_two (a := i)
    (by simpa only [dist_comm] using mem_metricRangeBall.mp hx)
    (by simpa only [dist_comm] using mem_metricRangeBall.mp hy)

section NormBudget

variable [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]

omit [DecidableEq ι] in
/-- The source's term-norm and metric-ball bounds give a local norm sum.
Hastings, arXiv:cond-mat/0508554v3, lines 180–185. -/
theorem sum_norm_metricRangeBall_le {R J : ℝ} {S : ℕ}
    (hS : ∀ x : ι, (metricRangeBall R x).card ≤ S) (hJ : 0 ≤ J)
    (h : ι → E) (hbound : ∀ i, ‖h i‖ ≤ J) (x : ι) :
    ∑ i ∈ metricRangeBall R x, ‖h i‖ ≤ (S : ℝ) * J := by
  calc _ ≤ ∑ _i ∈ metricRangeBall R x, J := Finset.sum_le_sum fun i _ => hbound i
    _ = ((metricRangeBall R x).card : ℝ) * J := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hS x) hJ

/-- Enlarging every support to its metric interaction ball supplies the site norm
budget with constant `S J`. Hastings, arXiv:cond-mat/0508554v3, lines 180–185. -/
theorem metricRangeBall_norm_budget_le {R J : ℝ} {S : ℕ}
    (hS : ∀ x : ι, (metricRangeBall R x).card ≤ S) (hJ : 0 ≤ J)
    (h : ι → E) (hbound : ∀ i, ‖h i‖ ≤ J) (x : ι) :
    ∑ i ∈ Finset.univ.filter (fun i => x ∈ metricRangeBall R i), ‖h i‖ ≤
      (S : ℝ) * J := by
  have heq : Finset.univ.filter (fun i => x ∈ metricRangeBall R i) = metricRangeBall R x := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_metricRangeBall, dist_comm]
  rw [heq]
  exact sum_norm_metricRangeBall_le hS hJ h hbound x

end NormBudget

/-- Retaining centres within radius `ℓ-R` keeps their complete interaction supports
within radius `ℓ`. Hastings, arXiv:cond-mat/0508554v3, eq. `odef`, lines 285–320. -/
theorem metricRangeBall_retained_support {R ℓ : ℝ} {i j : ι}
    (hj : j ∈ metricRangeBall (ℓ - R) i) :
    metricRangeBall R j ⊆ metricRangeBall ℓ i := by
  intro x hx
  apply mem_metricRangeBall.mpr
  calc dist i x ≤ dist i j + dist j x := dist_triangle _ _ _
    _ ≤ (ℓ - R) + R := add_le_add (mem_metricRangeBall.mp hj) (mem_metricRangeBall.mp hx)
    _ = ℓ := sub_add_cancel _ _

/-- The original interaction support lies in every admissible truncation ball.
Hastings, arXiv:cond-mat/0508554v3, eq. `odef`, lines 285–320. -/
theorem metricRangeBall_initial_support {R ℓ : ℝ} (hℓ : R ≤ ℓ) (i : ι) :
    metricRangeBall R i ⊆ metricRangeBall ℓ i := by
  intro x hx
  exact mem_metricRangeBall.mpr ((mem_metricRangeBall.mp hx).trans hℓ)

/-- Every omitted centre is beyond an explicit integer interaction-graph radius.
Hastings, arXiv:cond-mat/0508554v3, eq. `odef`, lines 285–320 and 1469–1505. -/
theorem metricRangeGraph_omitted_threshold {R ℓ : ℝ} (hR : 0 < R) {i j : ι}
    (hj : j ∉ metricRangeBall (ℓ - R) i) :
    (Nat.ceil ((ℓ - R) / R) : ℕ∞) ≤ (metricRangeGraph R).edist i j := by
  apply metricRangeGraph_edist_lower_ceil hR
  have hdist : ℓ - R < dist i j := not_le.mp (by
    simpa only [mem_metricRangeBall] using hj)
  calc R * ((ℓ - R) / R) = ℓ - R := by field_simp
    _ ≤ dist i j := hdist.le

end Finite

end ManyBody

namespace ManyBody

/-- Distinct interaction centres in the integer lattice have polynomial ball growth.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_centres_integerLattice_ball_le {κ : Type*} [Fintype κ]
    {D : ℕ} (c : κ → (Fin D → ℤ)) (hc : Function.Injective c)
    (x : Fin D → ℤ) (r : ℝ) :
    (Finset.univ.filter (fun k ↦ dist x (c k) ≤ r)).card ≤ (2 * ⌈r⌉₊ + 1) ^ D := by
  classical
  let m := ⌈r⌉₊
  let B := Fintype.piFinset fun j : Fin D ↦ Finset.Icc (x j - (m : ℤ)) (x j + m)
  have hsub : (Finset.univ.filter (fun k ↦ dist x (c k) ≤ r)).image c ⊆ B := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    have hk' := (Finset.mem_filter.mp hk).2
    apply Fintype.mem_piFinset.mpr
    intro j
    have hjr : |(x j : ℝ) - c k j| ≤ r := by
      simpa only [Int.dist_eq] using (dist_le_pi_dist x (c k) j).trans hk'
    have hj : |(x j : ℝ) - c k j| ≤ (m : ℝ) := hjr.trans (Nat.le_ceil r)
    have hj' : |x j - c k j| ≤ (m : ℤ) := by exact_mod_cast hj
    obtain ⟨hlo, hhi⟩ := abs_le.mp hj'
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hB : B.card = (2 * m + 1) ^ D := by
    dsimp only [B]
    rw [Fintype.card_piFinset]
    have hcoord : ∀ j : Fin D,
        (Finset.Icc (x j - (m : ℤ)) (x j + m)).card = 2 * m + 1 := by
      intro j
      rw [Int.card_Icc]
      omega
    simp only [hcoord, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ = ((Finset.univ.filter (fun k ↦ dist x (c k) ≤ r)).image c).card :=
      (Finset.card_image_of_injective _ hc).symm
    _ ≤ B.card := Finset.card_le_card hsub
    _ = _ := hB

/-- Integer-lattice balls satisfy the form of polynomial growth used in the thermal
index bounds. Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_centres_integerLattice_ball_le_polynomial {κ : Type*}
    [Fintype κ] {D : ℕ}
    (c : κ → (Fin D → ℤ)) (hc : Function.Injective c) (x : Fin D → ℤ) (r : ℝ) :
    (Finset.univ.filter (fun k ↦ dist x (c k) ≤ r)).card ≤
      2 ^ D * (⌈r⌉₊ + 1) ^ D := by
  refine (card_centres_integerLattice_ball_le c hc x r).trans ?_
  rw [← Nat.mul_pow]
  exact Nat.pow_le_pow_left (by omega) D


/-- An injective coordinate map that does not increase distances transfers the integer
box count to the physical metric. In particular, coordinate maximum distance is bounded
by the intrinsic walk distance on an induced integer-lattice domain.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_centres_ball_le_polynomial_of_dist_le {σ κ : Type*}
    [PseudoMetricSpace σ] [Fintype κ] {D : ℕ}
    (e : σ → (Fin D → ℤ)) (he : Function.Injective e)
    (hdist : ∀ a b, dist (e a) (e b) ≤ dist a b)
    (c : κ → σ) (hc : Function.Injective c) (i : σ) (r : ℝ) :
    (Finset.univ.filter (fun k ↦ dist i (c k) ≤ r)).card ≤
      2 ^ D * (⌈r⌉₊ + 1) ^ D := by
  classical
  refine (Finset.card_le_card ?_).trans
    (card_centres_integerLattice_ball_le_polynomial (e ∘ c) (he.comp hc) (e i) r)
  intro k hk
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ k,
    (hdist i (c k)).trans (Finset.mem_filter.mp hk).2⟩

/-- The polynomial ball bound transfers to a finite metric lattice embedded isometrically
in the coordinate maximum metric on the integer lattice, with distinct interaction centres.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1273–1275. -/
theorem card_centres_ball_le_polynomial_of_isometry {σ κ : Type*}
    [MetricSpace σ] [Fintype κ] {D : ℕ}
    (e : σ → (Fin D → ℤ)) (he : Isometry e) (c : κ → σ) (hc : Function.Injective c)
    (i : σ) (r : ℝ) :
    (Finset.univ.filter (fun k ↦ dist i (c k) ≤ r)).card ≤
      2 ^ D * (⌈r⌉₊ + 1) ^ D :=
  card_centres_ball_le_polynomial_of_dist_le e he.injective
    (fun a b ↦ (he.dist_eq a b).le) c hc i r

/-! ### The cyclic metric of the ring -/

private theorem val_finEquiv {M : ℕ} [NeZero M] (i : Fin M) :
    (ZMod.finEquiv M i).val = (i : ℕ) := by
  cases M
  · exact (NeZero.ne 0 rfl).elim
  · rfl

/-- The cyclic distance on `Fin M` is the absolute value of the least absolute residue of the
difference in `ZMod M`. -/
theorem roundedPeriodicDistance_eq_valMinAbs {M : ℕ} [NeZero M] (i v : Fin M) :
    roundedPeriodicDistance i v =
      ((ZMod.finEquiv M i - ZMod.finEquiv M v).valMinAbs).natAbs := by
  rcases le_total (i : ℕ) (v : ℕ) with hiv | hvi
  · have hv : (ZMod.finEquiv M i).val ≤ (ZMod.finEquiv M v).val := by
      simpa only [val_finEquiv] using hiv
    rw [← ZMod.natAbs_valMinAbs_neg, neg_sub, ZMod.valMinAbs_natAbs_eq_min,
      ZMod.val_sub hv, val_finEquiv, val_finEquiv]
    simp only [roundedPeriodicDistance, Nat.dist_eq_sub_of_le hiv]
  · have hv : (ZMod.finEquiv M v).val ≤ (ZMod.finEquiv M i).val := by
      simpa only [val_finEquiv] using hvi
    rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.val_sub hv, val_finEquiv, val_finEquiv]
    simp only [roundedPeriodicDistance, Nat.dist_eq_sub_of_le_right hvi]

/-- The cyclic distance satisfies the triangle inequality. -/
theorem roundedPeriodicDistance_triangle {M : ℕ} [NeZero M] (i v k : Fin M) :
    roundedPeriodicDistance i k ≤ roundedPeriodicDistance i v + roundedPeriodicDistance v k := by
  simp only [roundedPeriodicDistance_eq_valMinAbs]
  have hid : ZMod.finEquiv M i - ZMod.finEquiv M k =
      (ZMod.finEquiv M i - ZMod.finEquiv M v) +
        (ZMod.finEquiv M v - ZMod.finEquiv M k) := by abel
  rw [hid]
  exact (ZMod.natAbs_valMinAbs_add_le _ _).trans (Int.natAbs_add_le _ _)

/-- The metric space structure on `Fin M` given by the cyclic distance of the ring of `M`
sites. It is not an instance, since `Fin M` carries another metric.
Hastings, arXiv:cond-mat/0508554v3, lines 169–190 and 609–743. -/
@[instance_reducible]
noncomputable def cyclicMetricSpace (M : ℕ) [NeZero M] : MetricSpace (Fin M) where
  dist i v := roundedPeriodicDistance i v
  dist_self i := by simp [roundedPeriodicDistance]
  dist_comm i v := by simp only [roundedPeriodicDistance, Nat.dist_comm]
  dist_triangle i v k := by
    exact_mod_cast roundedPeriodicDistance_triangle i v k
  eq_of_dist_eq_zero {i v} hi := by
    have hzero : roundedPeriodicDistance i v = 0 := by exact_mod_cast hi
    rw [roundedPeriodicDistance_eq_valMinAbs, Int.natAbs_eq_zero,
      ZMod.valMinAbs_eq_zero, sub_eq_zero] at hzero
    exact (ZMod.finEquiv M).injective hzero

/-- Every ball of radius `R` of the cyclic metric has at most `2 ⌈R⌉₊ + 1` sites, whatever the
length of the ring. -/
theorem card_metricRangeBall_cyclicMetricSpace_le {M : ℕ} [NeZero M] (R : ℝ) (i : Fin M) :
    letI := cyclicMetricSpace M
    (metricRangeBall R i).card ≤ 2 * Nat.ceil R + 1 := by
  let _ := cyclicMetricSpace M
  let f : Fin M → ℤ := fun v ↦ (ZMod.finEquiv M v - ZMod.finEquiv M i).valMinAbs
  have hf : Set.MapsTo f (↑(metricRangeBall R i) : Set (Fin M))
      (↑(Finset.Icc (-(Nat.ceil R : ℤ)) (Nat.ceil R : ℤ)) : Set ℤ) := by
    intro v hv
    have hvR : (roundedPeriodicDistance i v : ℝ) ≤ R :=
      mem_metricRangeBall.mp hv
    have hvceil : roundedPeriodicDistance i v ≤ Nat.ceil R := by
      exact_mod_cast hvR.trans (Nat.le_ceil R)
    have hd : roundedPeriodicDistance v i = roundedPeriodicDistance i v := by
      simp only [roundedPeriodicDistance, Nat.dist_comm]
    have hnat : (f v).natAbs ≤ Nat.ceil R := by
      simpa only [f, ← roundedPeriodicDistance_eq_valMinAbs, hd] using hvceil
    have hcast : ((f v).natAbs : ℤ) ≤ (Nat.ceil R : ℤ) := by exact_mod_cast hnat
    have hpos : f v ≤ ((f v).natAbs : ℤ) := Int.le_natAbs
    have hneg : -f v ≤ ((f v).natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -f v))
    simp only [Finset.mem_coe, Finset.mem_Icc]
    omega
  have hinj : Function.Injective f := by
    intro a b hab
    have hd := ZMod.injective_valMinAbs hab
    have he : ZMod.finEquiv M a = ZMod.finEquiv M b := by
      simpa using congrArg (fun x ↦ x + ZMod.finEquiv M i) hd
    exact (ZMod.finEquiv M).injective he
  have hc := Finset.card_le_card_of_injOn f hf hinj.injOn
  have hcard : (Finset.Icc (-(Nat.ceil R : ℤ)) (Nat.ceil R : ℤ)).card =
      2 * Nat.ceil R + 1 := by
    rw [Int.card_Icc]
    omega
  exact hc.trans_eq hcard

end ManyBody
