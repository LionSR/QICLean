/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import QICLean.ManyBody.Dynamics.GraphBall

/-!
# Growth of graphs of bounded degree

A graph of degree at most `D` has at most `(D+1)^r` sites in a graph ball `graphBall G x r`,
and a sitewise budget `B` bounds the total weight of the supports meeting a region `K` by
`B |K|`. A bound on the degree therefore bounds an exponential row sum `∑_y e^{-μ d(x,y)}`
uniformly whenever `μ > log (D+1)`, and with a weight budget at each anchor the tail beyond
distance `m` decays at half the excess rate; sites in other components contribute zero.

At most `Δ ^ (2 (n - 1))` connected vertex sets of size `n` contain a given vertex of a graph of
degree at most `Δ`: every such set is the vertex set of a closed walk of length `2 (n - 1)`
from the vertex, built by adding one vertex at a time through a detour out and back along an
edge. This is the count of lattice animals (Klarner, Canad. J. Math. 19 (1967) 851) used by
the cluster expansion of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1227–1254,
eq. `perc2`, in the form `N x ^ n` with `x = max 1 (Δ ^ 2)`.

The degree and tail estimates sum the omitted interactions in Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 169–190 and 1469–1505, without a polynomial
growth hypothesis.

Moved from TNLean, `TNLean/Lattice/GraphDegreeGrowth.lean`, `GraphDegreeTail.lean` and
`ConnectedSetCount.lean` at commit `e113e005`. Changes: the closed ball `graphClosedBall` is
replaced by `ManyBody.graphBall` (the same set), and the lemmas about it are renamed
accordingly.

## Main results

* `ManyBody.card_graphBall_le` — a ball of radius `r` has at most `(D+1)^r` sites.
* `ManyBody.sum_weight_meeting_le_card_mul_budget` — the weight of supports meeting a region.
* `ManyBody.graphBall_separation` — centres outside a ball are far from the supports inside.
* `ManyBody.sum_exp_neg_edist_le_degree`, `ManyBody.sum_weight_exp_neg_edist_tail_le_degree` —
  exponential row sums and their tails.
* `ManyBody.card_connected_induce_le_exponential` — the count of connected sets of size `n`.
-/

namespace ManyBody


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A degree bound gives an exponential bound for closed balls. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 169–190. -/
theorem card_graphBall_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀ x, G.degree x ≤ D) (x : ι) (r : ℕ) :
    (graphBall G x r).card ≤ (D + 1) ^ r := by
  classical
  induction r with
  | zero =>
    have heq : graphBall G x 0 = {x} := by
      ext y
      simp only [mem_graphBall, Nat.cast_zero, nonpos_iff_eq_zero,
        G.edist_eq_zero_iff, Finset.mem_singleton]
      exact eq_comm
    simp [heq]
  | succ r ih =>
    have hsub : graphBall G x (r + 1) ⊆
        (graphBall G x r).biUnion (fun y ↦ insert y (G.neighborFinset y)) := by
      intro z hz
      have hz' : G.edist z x ≤ (r + 1 : ℕ) := by
        simpa only [mem_graphBall, G.edist_comm] using hz
      obtain ⟨p, hp⟩ := G.exists_walk_of_edist_ne_top
        (ne_top_of_le_ne_top (by simp) hz')
      cases p with
      | nil =>
        exact Finset.mem_biUnion.mpr ⟨x, mem_graphBall.mpr (by simp), by simp⟩
      | @cons z y x hzy p =>
        have hlen : p.length + 1 ≤ r + 1 := by
          exact_mod_cast (hp.symm ▸ hz')
        have hy : y ∈ graphBall G x r := by
          rw [mem_graphBall, G.edist_comm]
          exact p.edist_le.trans (by exact_mod_cast (by omega : p.length ≤ r))
        exact Finset.mem_biUnion.mpr ⟨y, hy,
          Finset.mem_insert_of_mem ((G.mem_neighborFinset y z).mpr hzy.symm)⟩
    calc (graphBall G x (r + 1)).card
        ≤ ((graphBall G x r).biUnion
          (fun y ↦ insert y (G.neighborFinset y))).card := Finset.card_le_card hsub
      _ ≤ (graphBall G x r).card * (D + 1) := by
        apply Finset.card_biUnion_le_card_mul
        intro y _
        exact (Finset.card_insert_le _ _).trans (by
          rw [G.card_neighborFinset_eq_degree]
          exact Nat.add_le_add_right (hD y) 1)
      _ ≤ (D + 1) ^ r * (D + 1) := Nat.mul_le_mul_right _ ih
      _ = (D + 1) ^ (r + 1) := (pow_succ _ _).symm


section Anchor

variable {κ : Type*} [Fintype κ]

omit [Fintype ι] in
/-- A local support budget also bounds the weights assigned to any one anchor contained
in those supports. This is the norm-budget reduction in Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu`, lines 1689–1694. -/
theorem sum_weight_anchor_le_of_support_budget (X : κ → Finset ι) (a : κ → ι)
    (ha : ∀ i, a i ∈ X i) (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (B : ℝ)
    (hBudget : ∀ x, ∑ i ∈ Finset.univ.filter (fun i ↦ x ∈ X i), w i ≤ B) (x : ι) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ a i = x), w i ≤ B := by
  classical
  refine le_trans ?_ (hBudget x)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [← hi]; exact ha i) (fun i _ _ ↦ hw i)

end Anchor

/-- Group nonnegative coefficients by their anchors and apply a bound on each fibre. -/
theorem sum_weight_mul_comp_le_budget_mul_sum {κ : Type*} [Fintype κ]
    (a : κ → ι) (w : κ → ℝ) (B : ℝ)
    (hBudget : ∀ y, ∑ k ∈ Finset.univ.filter (fun k ↦ a k = y), w k ≤ B)
    (f : ι → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ∑ k, w k * f (a k) ≤ B * ∑ y, f y := by
  classical
  calc _ = ∑ y, ∑ k ∈ Finset.univ.filter (fun k ↦ a k = y), w k * f (a k) :=
        (Finset.sum_fiberwise_of_maps_to (fun k _ ↦ Finset.mem_univ (a k)) _).symm
    _ = ∑ y, (∑ k ∈ Finset.univ.filter (fun k ↦ a k = y), w k) * f y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k hk ↦ by rw [(Finset.mem_filter.mp hk).2]
    _ ≤ ∑ y, B * f y := Finset.sum_le_sum fun y _ ↦
      mul_le_mul_of_nonneg_right (hBudget y) (hf y)
    _ = B * ∑ y, f y := (Finset.mul_sum _ _ _).symm

omit [Fintype ι] in
/-- A sitewise interaction budget bounds the total weight of terms meeting a region. -/
theorem sum_weight_meeting_le_card_mul_budget {κ : Type*} [Fintype κ]
    (X : κ → Finset ι) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (B : ℝ)
    (hBudget : ∀ x, ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ X k), w k ≤ B)
    (K : Finset ι) (t : Finset κ) (ht : ∀ k ∈ t, ¬Disjoint (X k) K) :
    ∑ k ∈ t, w k ≤ (K.card : ℝ) * B := by
  classical
  calc ∑ k ∈ t, w k
      ≤ ∑ k ∈ t, ∑ x ∈ K, if x ∈ X k then w k else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨x, hxX, hxK⟩ := Finset.not_disjoint_iff.mp (ht k hk)
        have hsingle := Finset.single_le_sum
          (f := fun x ↦ if x ∈ X k then w k else 0)
          (fun x _ ↦ by split_ifs <;> first | exact hw k | exact le_rfl) hxK
        simpa [hxX] using hsingle
    _ ≤ ∑ k, ∑ x ∈ K, if x ∈ X k then w k else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ ↦ Finset.sum_nonneg fun x _ ↦ by
          split_ifs <;> first | exact hw k | exact le_rfl)
    _ = ∑ x ∈ K, ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ X k), w k := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ _x ∈ K, B := Finset.sum_le_sum fun x _ ↦ hBudget x
    _ = (K.card : ℝ) * B := by simp


/-- The weighted shell has an exponential bound derived from a degree bound. -/
theorem sum_weight_meeting_graphBall_le {κ : Type*} [Fintype κ]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ x, G.degree x ≤ D)
    (X : κ → Finset ι) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (B : ℝ) (hB : 0 ≤ B)
    (hBudget : ∀ x, ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ X k), w k ≤ B)
    (x : ι) (l C : ℕ) (K : Finset ι) (hK : K ⊆ graphBall G x (l + C))
    (t : Finset κ) (ht : ∀ k ∈ t, ¬Disjoint (X k) K) :
    ∑ k ∈ t, w k ≤ B * (D + 1 : ℝ) ^ C * Real.exp (Real.log (D + 1) * l) := by
  have hb := sum_weight_meeting_le_card_mul_budget X w hw B hBudget K t ht
  have hc := (Finset.card_le_card hK).trans (card_graphBall_le G D hD x (l + C))
  have heq : Real.exp (Real.log (D + 1) * l) = (D + 1 : ℝ) ^ l := by
    rw [mul_comm (Real.log (D + 1)), Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [heq]
  calc ∑ k ∈ t, w k ≤ (K.card : ℝ) * B := hb
    _ ≤ (D + 1 : ℝ) ^ (l + C) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hB
    _ = B * (D + 1 : ℝ) ^ C * (D + 1 : ℝ) ^ l := by rw [pow_add]; ring


omit [DecidableEq ι] in
/-- A retained term centred in a ball acts inside the ball enlarged by its range. -/
theorem graphBall_subset_of_mem (G : SimpleGraph ι) (x i : ι) (l R : ℕ)
    (hi : i ∈ graphBall G x l) :
    graphBall G i R ⊆ graphBall G x (l + R) := by
  intro y hy
  rw [mem_graphBall] at hi hy ⊢
  exact (G.edist_triangle (u := x) (v := i) (w := y)).trans
    (by simpa only [Nat.cast_add] using add_le_add hi hy)

omit [DecidableEq ι] in
/-- Omitted centres lie far from every site of the original and omitted supports. -/
theorem graphBall_separation (G : SimpleGraph ι) (x k : ι) (l R : ℕ)
    (hk : k ∉ graphBall G x l) {z y : ι}
    (hz : z ∈ graphBall G x R) (hy : y ∈ graphBall G k R) :
    ((l - 2 * R : ℕ) : ℕ∞) ≤ G.edist z y := by
  simp only [mem_graphBall] at hk hz hy
  by_cases hl : 2 * R ≤ l
  · by_contra! hd
    have hbound : G.edist x k ≤ (R : ℕ∞) + (l - 2 * R : ℕ) + R := by
      calc G.edist x k ≤ G.edist x z + G.edist z k := G.edist_triangle
        _ ≤ G.edist x z + (G.edist z y + G.edist y k) :=
          add_le_add le_rfl G.edist_triangle
        _ ≤ (R : ℕ∞) + ((l - 2 * R : ℕ) + R) :=
          add_le_add hz
            (add_le_add hd.le (by simpa only [G.edist_comm] using hy))
        _ = _ := by ac_rfl
    have heq : (R : ℕ∞) + (l - 2 * R : ℕ) + R = (l : ℕ) := by
      rw [← Nat.cast_add, ← Nat.cast_add]
      congr 1
      omega
    exact hk (heq ▸ hbound)
  · simp [Nat.sub_eq_zero_of_le (by omega : l ≤ 2 * R)]


end ManyBody

open scoped Topology

namespace ManyBody

/-- Exponential decay in support separation gives exponential decay in anchor distance,
including infinite distance. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
eq. `blecm`, lines 1548–1601. -/
theorem le_anchorDecay_of_separated_exp {z C A B γ : ℝ} (hγ : 0 < γ) (hC : 2 ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (R : ℕ) (δ : ℕ∞) (htriv : z ≤ 2 * A * B)
    (hsep : ∀ l : ℕ, ((2 * R + l : ℕ) : ℕ∞) < δ →
      z ≤ C * A * B * Real.exp (-(γ * l))) :
    z ≤ C * Real.exp (γ * (2 * R + 1)) * A * B *
      (if δ = ⊤ then 0 else Real.exp (-(γ * (δ.toNat : ℝ)))) := by
  split_ifs with htop
  · rw [mul_zero]
    have hlim : Filter.Tendsto (fun l : ℕ => C * A * B * Real.exp (-(γ * l)))
        Filter.atTop (𝓝 0) := by
      have h1 : Filter.Tendsto (fun l : ℕ => γ * (l : ℝ)) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop hγ tendsto_natCast_atTop_atTop
      simpa [Function.comp_def] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (C * A * B)
    exact ge_of_tendsto' hlim fun l => hsep l (by rw [htop]; exact ENat.natCast_lt_top _)
  · let D := δ.toNat
    have hD : δ = (D : ℕ∞) := (ENat.natCast_toNat htop).symm
    by_cases hfar : 2 * R + 1 < D
    · have hl := hsep (D - (2 * R + 1)) (by rw [hD]; exact_mod_cast (by omega))
      refine hl.trans (le_of_eq ?_)
      have hcast : ((D - (2 * R + 1) : ℕ) : ℝ) = (D : ℝ) - (2 * R + 1) := by
        rw [Nat.cast_sub hfar.le]; push_cast; ring
      rw [hcast, show -(γ * ((D : ℝ) - (2 * R + 1))) = γ * (2 * R + 1) + -(γ * D) by ring,
        Real.exp_add]
      ring
    · push Not at hfar
      have hexp : 1 ≤ Real.exp (γ * (2 * R + 1)) * Real.exp (-(γ * D)) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        have : (D : ℝ) ≤ 2 * R + 1 := by exact_mod_cast hfar
        nlinarith
      have hAB : 0 ≤ A * B := mul_nonneg hA hB
      have hCAB : 0 ≤ C * A * B := by positivity
      calc z ≤ 2 * A * B := htriv
        _ ≤ C * A * B * 1 := by nlinarith [mul_le_mul_of_nonneg_right hC hAB]
        _ ≤ C * A * B * (Real.exp (γ * (2 * R + 1)) * Real.exp (-(γ * D))) :=
          mul_le_mul_of_nonneg_left hexp hCAB
        _ = _ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The sum of an exponential above the degree growth rate is uniformly bounded. -/
theorem sum_exp_neg_edist_le_degree (G : SimpleGraph ι) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀ x, G.degree x ≤ D) (x : ι) {μ : ℝ}
    (hμ : Real.log (D + 1) < μ) :
    ∑ y, (if G.edist x y = ⊤ then 0 else
      Real.exp (-(μ * ((G.edist x y).toNat : ℝ)))) ≤
        1 / (1 - Real.exp (-(μ - Real.log (D + 1)))) := by
  classical
  let S := Finset.univ.filter fun y ↦ G.edist x y ≠ ⊤
  let r : ι → ℕ := fun y ↦ (G.edist x y).toNat
  let q := Real.exp (-(μ - Real.log (D + 1)))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hfib (n : ℕ) : ((S.filter fun y ↦ r y = n).card : ℝ) ≤ (D + 1 : ℝ) ^ n := by
    have hsub : (S.filter fun y ↦ r y = n) ⊆ graphBall G x n := by
      intro y hy
      obtain ⟨hyS, hyn⟩ := Finset.mem_filter.mp hy
      have hyfin := (Finset.mem_filter.mp hyS).2
      rw [mem_graphBall, ← hyn]
      exact (ENat.natCast_toNat hyfin).ge
    exact_mod_cast (Finset.card_le_card hsub).trans (card_graphBall_le G D hD x n)
  have hgeom (n : ℕ) : (D + 1 : ℝ) ^ n * Real.exp (-(μ * n)) = q ^ n := by
    have hpow : (D + 1 : ℝ) ^ n = Real.exp (Real.log (D + 1) * n) := by
      rw [mul_comm (Real.log (D + 1)), Real.exp_nat_mul, Real.exp_log (by positivity)]
    rw [hpow, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  have heq : ∑ y, (if G.edist x y = ⊤ then 0 else Real.exp (-(μ * (r y : ℝ)))) =
      ∑ y ∈ S, Real.exp (-(μ * (r y : ℝ))) := by
    simp only [S, Finset.sum_filter]
    exact Finset.sum_congr rfl fun y _ ↦ by split_ifs <;> simp_all
  rw [heq]
  calc ∑ y ∈ S, Real.exp (-(μ * (r y : ℝ)))
      = ∑ n ∈ S.image r, ∑ y ∈ S.filter (fun y ↦ r y = n),
          Real.exp (-(μ * (r y : ℝ))) :=
        (Finset.sum_fiberwise_of_maps_to (fun y hy ↦ Finset.mem_image_of_mem r hy) _).symm
    _ = ∑ n ∈ S.image r, ((S.filter fun y ↦ r y = n).card : ℝ) *
          Real.exp (-(μ * n)) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.sum_congr rfl (fun y hy ↦ by rw [(Finset.mem_filter.mp hy).2]),
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ S.image r, (D + 1 : ℝ) ^ n * Real.exp (-(μ * n)) :=
      Finset.sum_le_sum fun n _ ↦ mul_le_mul_of_nonneg_right (hfib n) (Real.exp_pos _).le
    _ = ∑ n ∈ S.image r, q ^ n := Finset.sum_congr rfl fun n _ ↦ hgeom n
    _ ≤ ∑' n : ℕ, q ^ n :=
      (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun n _ ↦ pow_nonneg hq0 n)
    _ = _ := by rw [tsum_geometric_of_lt_one hq0 hq1]; simp only [one_div, q]


/-- A degree bound and an anchor budget give an exponentially decaying weighted tail. -/
theorem sum_weight_exp_neg_edist_tail_le_degree {κ : Type*} [Fintype κ]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ x, G.degree x ≤ D)
    (a : κ → ι) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (B : ℝ) (hB : 0 ≤ B)
    (hBudget : ∀ y, ∑ k ∈ Finset.univ.filter (fun k ↦ a k = y), w k ≤ B)
    (x : ι) (t : Finset κ) (m : ℕ)
    (hsep : ∀ k ∈ t, (m : ℕ∞) ≤ G.edist x (a k)) {μ : ℝ}
    (hμ : Real.log (D + 1) < μ) :
    let β := (μ - Real.log (D + 1)) / 2
    ∑ k ∈ t, w k * (if G.edist x (a k) = ⊤ then 0 else
      Real.exp (-(μ * ((G.edist x (a k)).toNat : ℝ)))) ≤
        B * Real.exp (-(β * m)) / (1 - Real.exp (-β)) := by
  classical
  intro β
  have hβ : 0 < β := half_pos (sub_pos.mpr hμ)
  have hη : Real.log (D + 1) < μ - β := by dsimp [β]; linarith
  let f : ℝ → ι → ℝ := fun η y ↦ if G.edist x y = ⊤ then 0 else
    Real.exp (-(η * ((G.edist x y).toNat : ℝ)))
  have hf (η : ℝ) (y : ι) : 0 ≤ f η y := by dsimp [f]; split_ifs <;> positivity
  have hpoint (k : κ) (hk : k ∈ t) : w k * f μ (a k) ≤
      Real.exp (-(β * m)) * (w k * f (μ - β) (a k)) := by
    by_cases htop : G.edist x (a k) = ⊤
    · simp [f, htop]
    have hm : (m : ℝ) ≤ ((G.edist x (a k)).toNat : ℝ) := by
      have hmn : m ≤ (G.edist x (a k)).toNat := by
        exact_mod_cast (show (m : ℕ∞) ≤ ((G.edist x (a k)).toNat : ℕ) by
          simpa only [ENat.natCast_toNat htop] using hsep k hk)
      exact_mod_cast hmn
    have he : Real.exp (-(μ * ((G.edist x (a k)).toNat : ℝ))) ≤
        Real.exp (-(β * m)) * Real.exp (-((μ - β) * ((G.edist x (a k)).toNat : ℝ))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    simp only [f, htop, ↓reduceIte]
    calc _ ≤ w k * (Real.exp (-(β * m)) *
        Real.exp (-((μ - β) * ((G.edist x (a k)).toNat : ℝ)))) :=
          mul_le_mul_of_nonneg_left he (hw k)
      _ = _ := by ring
  have hgroup := sum_weight_mul_comp_le_budget_mul_sum a w B hBudget
    (f (μ - β)) (hf _)
  have hrow := sum_exp_neg_edist_le_degree G D hD x hη
  have hrate : μ - β - Real.log (D + 1) = β := by dsimp [β]; ring
  rw [hrate] at hrow
  calc ∑ k ∈ t, w k * f μ (a k)
      ≤ ∑ k ∈ t, Real.exp (-(β * m)) * (w k * f (μ - β) (a k)) :=
        Finset.sum_le_sum hpoint
    _ = Real.exp (-(β * m)) * ∑ k ∈ t, w k * f (μ - β) (a k) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-(β * m)) * ∑ k, w k * f (μ - β) (a k) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ ↦ mul_nonneg (hw k) (hf _ _))
    _ ≤ Real.exp (-(β * m)) * (B * ∑ y, f (μ - β) y) :=
      mul_le_mul_of_nonneg_left hgroup (Real.exp_pos _).le
    _ ≤ Real.exp (-(β * m)) * (B * (1 / (1 - Real.exp (-β)))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left hrow hB
    _ = _ := by ring

end ManyBody

namespace ManyBody

open Finset SimpleGraph

variable {V : Type*}

/-- Inserting a detour `w → u → w` at a vertex `w` of a closed walk lengthens it by
two and adds exactly the vertex `u` to its vertex set. -/
theorem exists_detour_walk (G : SimpleGraph V) {v w u : V} (p : G.Walk v v)
    (hw : w ∈ p.support) (hwu : G.Adj w u) :
    ∃ q : G.Walk v v, q.length = p.length + 2 ∧
      ∀ x, x ∈ q.support ↔ x ∈ p.support ∨ x = u := by
  classical
  refine ⟨(p.takeUntil w hw).append (.cons hwu (.cons hwu.symm (p.dropUntil w hw))), ?_, ?_⟩
  · have h := congrArg Walk.length (p.take_spec hw)
    rw [Walk.length_append] at h
    simp only [Walk.length_append, Walk.length_cons]
    omega
  · intro x
    conv_rhs => rw [← p.take_spec hw]
    simp only [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons]
    have := (p.dropUntil w hw).start_mem_support
    grind

/-- A finite vertex set `S` containing `v` that induces a connected subgraph is the
vertex set of a closed walk from `v` of length exactly `2 (|S| - 1)`. -/
theorem exists_closedWalk_support_toFinset_eq [DecidableEq V] (G : SimpleGraph V)
    {S : Finset V} {v : V} (hv : v ∈ S) (hS : (G.induce (S : Set V)).Connected) :
    ∃ p : G.Walk v v, p.length = 2 * (#S - 1) ∧ p.support.toFinset = S := by
  suffices h : ∀ k, 1 ≤ k → k ≤ #S → ∃ T ⊆ S, #T = k ∧
      ∃ p : G.Walk v v, p.length = 2 * (k - 1) ∧ p.support.toFinset = T by
    obtain ⟨T, hTS, hT, p, hp, hpT⟩ := h #S (card_pos.2 ⟨v, hv⟩) le_rfl
    exact ⟨p, hp, hpT.trans (eq_of_subset_of_card_le hTS hT.ge)⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun _ => ⟨{v}, by simpa using hv, by simp, .nil, by simp, by simp⟩
  | succ k hk ih =>
    intro hkS
    obtain ⟨T, hTS, hT, p, hp, hpT⟩ := ih (by omega)
    obtain ⟨b, hbS, hbT⟩ : ∃ b ∈ S, b ∉ T := not_subset.1 fun h =>
      by have := card_le_card h; omega
    obtain ⟨W⟩ := hS.preconnected (⟨v, by simpa using hv⟩ : (S : Set V))
      ⟨b, by simp [hbS]⟩
    obtain ⟨d, -, hdT, hdT'⟩ := W.exists_boundary_dart {x | x.1 ∈ T}
      (by simp [← hpT]) (by simpa using hbT)
    have hadj : G.Adj d.fst.1 d.snd.1 := d.adj
    obtain ⟨q, hq, hqsupp⟩ := exists_detour_walk G p (by simpa [← hpT] using hdT) hadj
    refine ⟨insert d.snd.1 T, insert_subset (by simp) hTS,
      by rw [card_insert_of_notMem hdT', hT], q, by rw [hq, hp]; omega, ?_⟩
    ext x
    simp [hqsupp, ← hpT, or_comm]

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a graph of maximum degree at most `Δ`, there are at most `Δ ^ L` walks of length
`L` between two given vertices. -/
theorem card_finsetWalkLength_le_pow {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (L : ℕ)
    (u x : V) : #(G.finsetWalkLength L u x) ≤ Δ ^ L := by
  induction L generalizing u with
  | zero =>
    rw [finsetWalkLength]
    split_ifs with h
    · subst h; simp
    · simp
  | succ L ih =>
    rw [finsetWalkLength]
    refine card_biUnion_le.trans ?_
    calc ∑ w : G.neighborSet u, #((G.finsetWalkLength L w x).map _)
        ≤ ∑ _w : G.neighborSet u, Δ ^ L :=
          Finset.sum_le_sum fun w _ => by rw [card_map]; exact ih w
      _ ≤ Δ ^ (L + 1) := by
        rw [sum_const, card_univ, card_neighborSet_eq_degree, smul_eq_mul, pow_succ,
          mul_comm]
        exact Nat.mul_le_mul_left _ (hΔ u)

/-- **Connected sets through a vertex** (Hastings, arXiv:cond-mat/0508554v3, lines
1227–1254, after Klarner 1967). In a finite graph of maximum degree at most `Δ`, at
most `Δ ^ (2 (n - 1))` vertex sets of size `n` that contain `v` induce a connected
subgraph. -/
theorem card_connected_induce_mem_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (v : V) (n : ℕ) :
    #{S : Finset V | v ∈ S ∧ #S = n ∧ (G.induce (S : Set V)).Connected} ≤
      Δ ^ (2 * (n - 1)) := by
  have key : ∀ S ∈ ({S : Finset V | v ∈ S ∧ #S = n ∧ (G.induce (S : Set V)).Connected} :
      Finset (Finset V)), ∃ p : G.Walk v v,
        p.length = 2 * (n - 1) ∧ p.support.toFinset = S := by
    intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    obtain ⟨hv, rfl, hc⟩ := hS
    exact exists_closedWalk_support_toFinset_eq G hv hc
  choose! f hf using key
  calc _ ≤ #(G.finsetWalkLength (2 * (n - 1)) v v) := by
        refine card_le_card_of_injOn f (fun S hS => ?_) (fun S hS T hT h => ?_)
        · simpa [mem_finsetWalkLength_iff] using (hf S hS).1
        · rw [← (hf S hS).2, h, (hf T hT).2]
    _ ≤ _ := card_finsetWalkLength_le_pow G hΔ _ v v

/-- **Connected sets of a given size** (Hastings, arXiv:cond-mat/0508554v3, lines
1227–1254, after Klarner 1967). In a graph on `N` vertices of maximum degree at most
`Δ`, at most `N Δ ^ (2 (n - 1))` vertex sets of size `n` induce a connected subgraph. -/
theorem card_connected_induce_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (n : ℕ) :
    #{S : Finset V | #S = n ∧ (G.induce (S : Set V)).Connected} ≤
      Fintype.card V * Δ ^ (2 * (n - 1)) := by
  calc _ ≤ #(univ.biUnion fun v : V =>
        ({S : Finset V | v ∈ S ∧ #S = n ∧ (G.induce (S : Set V)).Connected} :
          Finset (Finset V))) := by
        refine card_le_card fun S hS => ?_
        simp only [mem_filter, mem_univ, true_and] at hS
        obtain ⟨⟨v, hv⟩⟩ := hS.2.nonempty
        simp only [mem_biUnion, mem_univ, mem_filter, true_and]
        exact ⟨v, by simpa using hv, hS.1, hS.2⟩
    _ ≤ ∑ v : V, #({S : Finset V | v ∈ S ∧ #S = n ∧ (G.induce (S : Set V)).Connected} :
          Finset (Finset V)) := card_biUnion_le
    _ ≤ ∑ _v : V, Δ ^ (2 * (n - 1)) := Finset.sum_le_sum fun v _ =>
        card_connected_induce_mem_le G hΔ v n
    _ = _ := by simp

/-- The exponential cluster count used in Hastings, arXiv:cond-mat/0508554v3,
lines 1227–1254. The constant `max 1 (Δ ^ 2)` also covers edgeless graphs,
whose connected singleton sets must still be counted. -/
theorem card_connected_induce_le_exponential {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (n : ℕ) :
    #{S : Finset V | #S = n ∧ (G.induce (S : Set V)).Connected} ≤
      Fintype.card V * (max 1 (Δ ^ 2)) ^ n := by
  refine (card_connected_induce_le G hΔ n).trans (Nat.mul_le_mul_left _ ?_)
  rw [pow_mul]
  exact (pow_le_pow_left' (le_max_right 1 (Δ ^ 2)) (n - 1)).trans
    (pow_le_pow_right' (le_max_left 1 (Δ ^ 2)) (Nat.sub_le n 1))


end ManyBody
