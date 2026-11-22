/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import QICLean.Algebra.Combinatorics.ConnectedSetCount
import QICLean.Analysis.ClusterExpansion.Truncation

/-!
# Hastings' percolation bound

The error `e^{-βH} - ρ(β, l)` of the truncated expansion is bounded by a sum over families of
large connected sets of terms, each set weighted by `y^{n_C}`. Counting connected sets of size
`n` in a graph of degree at most `Δ` by `N x^n`, `x = max 1 (Δ²)`, the sum is at most
`exp(N (xy)^{l} / (1 - xy)) - 1` once `xy ≤ 1/2`. For terms acting on supports of diameter at
most `2R` in a pseudometric space, a cluster of diameter larger than `l_proj` has more than
`l_proj / 2R` terms, which gives eq. `perc2` with decay length `2R / ln(1/(xy))` (Hastings,
`proj3new.tex`, lines 1227–1254).

Moved from TNLean (`e113e005`): `TNLean/Lattice/ClusterExpansion/Percolation.lean` (namespace
`TNLean.Lattice`) and `PercolationSource.lean`, both in the namespace `ClusterExpansion`. The
connected-set count is `SimpleGraph.card_connected_induce_le_exponential` of
`QICLean/Algebra/Combinatorics/ConnectedSetCount.lean`.
-/

/-!
## The percolation sum of Hastings' high-temperature cluster expansion

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1196–1254), bounds the difference between the
thermal operator `ρ(β)` and its truncation `ρ(β, l_proj)` by an inclusion–exclusion sum over
families of clusters of diameter larger than `l_proj`. A family of `m` clusters `C₁, …, C_m`
contributes at most `∏ y^{n_{C_i}}`, where `n_C` is the number of sites of `C` and
`y = (e^{Jβ} − 1) e^{SJβ}`. Summing over families, the source obtains

`∑_{m ≥ 1} (1/m!) (∑_C y^{n_C})^m ≤ exp[N ∑_{n > l_proj} (xy)^n] − 1`
`≤ exp[N e^{−l_proj/ξ_perc}] − 1`

when there are at most `N xⁿ` clusters of `n` sites (lines 1227–1250).

This file proves that estimate with abstract weights. A weight `a_C` with `0 ≤ a_C ≤ y^{n_C}` stands
for the contribution of the cluster `C`. Families of clusters are finite subsets `U` of the
family `T` of large clusters, and contribute `∏_{C ∈ U} a_C`. Every cluster of `T` is assumed to
have at least `l + 1` sites, for a size threshold `l` that is a parameter of the statements.

**Local fix (size threshold):** the source starts the sum over cluster sizes at
`n = l_proj + 1` (line 1240), which holds for nearest-neighbour bonds only. With terms of range
`R`, a cluster of `n` sites spans a distance of at most `2Rn`, so diameter larger than `l_proj`
gives only `n ≥ ⌊l_proj/(2R)⌋ + 1`; the cluster `{0, 2R}` of a chain has two sites and spans
`4R`. The statements here take the size threshold `l` as a hypothesis, and the application takes
`l = ⌊l_proj/(2R)⌋`. Documented in `docs/paper-gaps/hastings05_percolation_cluster_size.tex`.

The decay is explicit in the size threshold. For `0 < xy ≤ 1/2`, the tail `∑_{n > l} (xy)^n` is
at most `(xy)^l = e^{−l/ξ}` with `ξ = 1 / ln(1/(xy))`, a decay length in units of cluster size.
With `l = ⌊l_proj/(2R)⌋` this is at most `(xy)^{−1} e^{−l_proj/ξ_perc}` with
`ξ_perc = 2R / ln(1/(xy))` in units of distance, which is the source's "`ξ_perc` of order the
interaction range" (line 1250).

### Main results

* `ClusterExpansion.sum_powersetCard_prod_le`: the families of `m` clusters contribute at most
  `(∑_C a_C)^m / m!` (the bound on `ρ_m`, line 1210).
* `ClusterExpansion.sum_nonempty_powerset_prod_eq`,
  `ClusterExpansion.sum_nonempty_powerset_prod_le_exp`: all nonempty families together contribute
  `∏_C (1 + a_C) − 1 ≤ exp(∑_C a_C) − 1`.
* `ClusterExpansion.sum_pow_le_of_card_le`: `∑_C y^{n_C} ≤ N (xy)^{l+1} / (1 − xy)` from the count
  of clusters by size.
* `ClusterExpansion.sum_nonempty_powerset_prod_le_percolation`: the percolation bound
  `exp(N e^{−l/ξ}) − 1`, eq. `perc2` (lines 1227–1254) without the trace, in terms of the size
  threshold `l`.
* `ClusterExpansion.sum_nonempty_powerset_prod_le_percolation_connected`: the same for families of
  connected vertex sets of a graph of maximum degree `Δ`, with `N` the number of vertices and
  `x = max(1, Δ²)`.
* `ClusterExpansion.exists_percolation_temperature`: some `β₀ > 0` gives `xy ≤ 1/2` for every
  `0 ≤ β ≤ β₀` (line 1244).
-/

open Finset Real

namespace ClusterExpansion

variable {ι : Type*}

section Families

/-- `s^{m+1} + (m + 1) a s^m ≤ (s + a)^{m+1}` for `s, a ≥ 0`: the first two terms of the binomial
expansion. -/
private theorem pow_succ_add_mul_le {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (m : ℕ) :
    s ^ (m + 1) + (m + 1) * a * s ^ m ≤ (s + a) ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 0 ≤ s ^ m := pow_nonneg hs m
    have h2 : 0 ≤ a * a * s ^ m := by positivity
    calc s ^ (m + 1 + 1) + ((m + 1 : ℕ) + 1 : ℝ) * a * s ^ (m + 1)
        ≤ (s + a) * (s ^ (m + 1) + (m + 1) * a * s ^ m) := by
          push_cast
          rw [pow_succ s (m + 1), pow_succ s m]
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) h2]
      _ ≤ (s + a) * (s + a) ^ (m + 1) := by gcongr
      _ = (s + a) ^ (m + 1 + 1) := by ring

/-- **Families of `m` clusters.** For nonnegative weights `a` on a finite set `T`, the sum over
the `m`-element subsets `U ⊆ T` of `∏_{i ∈ U} a_i` is at most `(∑_{i ∈ T} a_i)^m / m!`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, line 1210, the bound on `ρ_m`. -/
theorem sum_powersetCard_prod_le {T : Finset ι} {a : ι → ℝ} (ha : ∀ i ∈ T, 0 ≤ a i)
    (m : ℕ) :
    ∑ U ∈ T.powersetCard m, ∏ i ∈ U, a i ≤ (∑ i ∈ T, a i) ^ m / m.factorial := by
  classical
  induction T using Finset.induction_on generalizing m with
  | empty =>
    cases m with
    | zero => simp
    | succ m => simp [powersetCard_eq_empty.2 (by simp : #(∅ : Finset ι) < m + 1)]
  | insert b T hb ih =>
    have haT : ∀ i ∈ T, 0 ≤ a i := fun i hi ↦ ha i (mem_insert_of_mem hi)
    have hab : 0 ≤ a b := ha b (mem_insert_self b T)
    have hs : 0 ≤ ∑ i ∈ T, a i := sum_nonneg haT
    rw [sum_insert hb]
    cases m with
    | zero => simp
    | succ m =>
      have hdisj : Disjoint (T.powersetCard (m + 1)) ((T.powersetCard m).image (insert b)) := by
        rw [disjoint_left]
        intro U hU hU'
        obtain ⟨V, -, rfl⟩ := mem_image.1 hU'
        exact hb ((mem_powersetCard.1 hU).1 (mem_insert_self b V))
      have hinj : ∀ U ∈ T.powersetCard m, ∀ V ∈ T.powersetCard m, insert b U = insert b V →
          U = V := fun U hU V hV h ↦ by
        have hbU : b ∉ U := fun h' ↦ hb ((mem_powersetCard.1 hU).1 h')
        have hbV : b ∉ V := fun h' ↦ hb ((mem_powersetCard.1 hV).1 h')
        simpa [erase_insert hbU, erase_insert hbV] using congrArg (·.erase b) h
      rw [powersetCard_succ_insert hb, sum_union hdisj,
        sum_image fun U hU V hV h ↦ hinj U (mem_coe.1 hU) V (mem_coe.1 hV) h]
      have hins : ∀ U ∈ T.powersetCard m, ∏ i ∈ insert b U, a i = a b * ∏ i ∈ U, a i :=
        fun U hU ↦ prod_insert fun h ↦ hb ((mem_powersetCard.1 hU).1 h)
      rw [sum_congr rfl hins, ← mul_sum]
      have h1 := ih haT (m + 1)
      have h2 := ih haT m
      have hbin := pow_succ_add_mul_le hs hab m
      rw [add_comm (∑ i ∈ T, a i)] at hbin
      calc ∑ U ∈ T.powersetCard (m + 1), ∏ i ∈ U, a i + a b * ∑ U ∈ T.powersetCard m, ∏ i ∈ U, a i
          ≤ (∑ i ∈ T, a i) ^ (m + 1) / (m + 1).factorial +
              a b * ((∑ i ∈ T, a i) ^ m / m.factorial) :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h2 hab)
        _ = ((∑ i ∈ T, a i) ^ (m + 1) + (m + 1) * a b * (∑ i ∈ T, a i) ^ m) /
              (m + 1).factorial := by
            rw [Nat.factorial_succ]; push_cast; field_simp
        _ ≤ (a b + ∑ i ∈ T, a i) ^ (m + 1) / (m + 1).factorial := by gcongr

variable [DecidableEq ι]

/-- The sum over the nonempty subsets `U ⊆ T` of `∏_{i ∈ U} a_i` is `∏_{i ∈ T} (1 + a_i) − 1`. -/
theorem sum_nonempty_powerset_prod_eq (T : Finset ι) (a : ι → ℝ) :
    ∑ U ∈ T.powerset.erase ∅, ∏ i ∈ U, a i = ∏ i ∈ T, (1 + a i) - 1 := by
  rw [sum_erase_eq_sub (empty_mem_powerset T), ← prod_one_add, prod_empty]

/-- **All nonempty families of clusters.** For nonnegative weights `a` on a finite set `T`, the sum
over the nonempty subsets `U ⊆ T` of `∏_{i ∈ U} a_i` equals `∏_{i ∈ T} (1 + a_i) − 1`, and is at
most `exp(∑_{i ∈ T} a_i) − 1`. This is the inclusion–exclusion sum `∑_{m ≥ 1} ρ_m` of Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1196–1225, estimated as at lines 1238–1241. -/
theorem sum_nonempty_powerset_prod_le_exp {T : Finset ι} {a : ι → ℝ} (ha : ∀ i ∈ T, 0 ≤ a i) :
    ∑ U ∈ T.powerset.erase ∅, ∏ i ∈ U, a i ≤ exp (∑ i ∈ T, a i) - 1 := by
  rw [sum_nonempty_powerset_prod_eq, exp_sum]
  have := prod_le_prod₀ (s := T) (f := fun i ↦ 1 + a i) (g := fun i ↦ exp (a i))
    (fun i hi ↦ by linarith [ha i hi]) fun i _ ↦ by linarith [add_one_le_exp (a i)]
  linarith

end Families

section Count

/-- A finite sum of `r^k` over exponents `k ≥ l + 1` is at most `r^{l+1} / (1 − r)` for
`0 ≤ r < 1`. -/
theorem sum_pow_le_of_forall_lt {K : Finset ℕ} {l : ℕ} (hK : ∀ k ∈ K, l + 1 ≤ k) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) : ∑ k ∈ K, r ^ k ≤ r ^ (l + 1) / (1 - r) := by
  have hsub : K ⊆ Ico (l + 1) (K.sup id + l + 2) := fun k hk ↦
    mem_Ico.2 ⟨hK k hk, by have := le_sup (f := id) hk; simp only [id] at this; omega⟩
  refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ pow_nonneg hr0 _).trans ?_
  rw [geom_sum_Ico' hr1.ne (by omega)]
  gcongr
  all_goals linarith [pow_nonneg hr0 (K.sup id + l + 2)]

/-- **The sum over large clusters.** Let `T` be a finite family of clusters, where the cluster `i`
has `n i ≥ l + 1` sites and there are at most `N x^k` clusters of `k` sites. For `0 ≤ y` with
`x y < 1`, `∑_{i ∈ T} y^{n i} ≤ N (xy)^{l+1} / (1 − xy)`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1236–1241. -/
theorem sum_pow_le_of_card_le {T : Finset ι} {n : ι → ℕ} {l : ℕ} (hn : ∀ i ∈ T, l + 1 ≤ n i)
    {N x y : ℝ} (hcount : ∀ k, (#{i ∈ T | n i = k} : ℝ) ≤ N * x ^ k) (hN : 0 ≤ N) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hxy : x * y < 1) :
    ∑ i ∈ T, y ^ n i ≤ N * ((x * y) ^ (l + 1) / (1 - x * y)) := by
  rw [← sum_fiberwise_of_maps_to (g := n) (t := T.image n) fun i hi ↦ mem_image_of_mem n hi]
  calc ∑ k ∈ T.image n, ∑ i ∈ T with n i = k, y ^ n i
      = ∑ k ∈ T.image n, (#{i ∈ T | n i = k} : ℝ) * y ^ k := by
        refine sum_congr rfl fun k _ ↦ ?_
        rw [sum_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2], sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ T.image n, N * (x * y) ^ k := by
        refine sum_le_sum fun k _ ↦ ?_
        rw [mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hcount k) (pow_nonneg hy k)
    _ = N * ∑ k ∈ T.image n, (x * y) ^ k := by rw [mul_sum]
    _ ≤ N * ((x * y) ^ (l + 1) / (1 - x * y)) := by
        gcongr
        refine sum_pow_le_of_forall_lt (fun k hk ↦ ?_) (mul_nonneg hx hy) hxy
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hk
        exact hn i hi

end Count

section Percolation

/-- For `0 ≤ r ≤ 1/2`, the geometric tail `r^{l+1} / (1 − r)` is at most `r^l`. -/
theorem pow_succ_div_one_sub_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (l : ℕ) :
    r ^ (l + 1) / (1 - r) ≤ r ^ l := by
  rw [div_le_iff₀ (by linarith), pow_succ]
  have := pow_nonneg hr0 l
  nlinarith

/-- For `0 < r`, `r^l = e^{−l/ξ}` with `ξ = 1 / ln(1/r)`. -/
theorem pow_eq_exp_neg_div (r : ℝ) (hr : 0 < r) (l : ℕ) :
    r ^ l = exp (-(l / (log r⁻¹)⁻¹)) := by
  rw [div_inv_eq_mul, log_inv, mul_neg, neg_neg, ← log_pow, exp_log (pow_pos hr l)]

variable [DecidableEq ι]

/-- **The percolation bound (eq. `perc2` without the trace).** Let `T` be a finite family of
clusters, where the cluster `i` has `n i ≥ l + 1` sites and there are at most `N x^k` clusters
of `k` sites, and let the weights satisfy `0 ≤ a i ≤ y^{n i}` with `0 < x y ≤ 1/2`. Then the sum
over nonempty subfamilies `U ⊆ T` of `∏_{i ∈ U} a i` is at most `exp(N e^{−l/ξ}) − 1`, with
the decay length `ξ = 1 / ln(1/(xy))` in units of cluster size. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1227–1254, with the families of clusters of
lines 1196–1225 and the size threshold of the section docstring. -/
theorem sum_nonempty_powerset_prod_le_percolation {T : Finset ι} {n : ι → ℕ} {l : ℕ}
    (hn : ∀ i ∈ T, l + 1 ≤ n i) {N x y : ℝ}
    (hcount : ∀ k, (#{i ∈ T | n i = k} : ℝ) ≤ N * x ^ k) (hN : 0 ≤ N) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hxy0 : 0 < x * y) (hxy : x * y ≤ 1 / 2) {a : ι → ℝ}
    (ha0 : ∀ i ∈ T, 0 ≤ a i) (ha : ∀ i ∈ T, a i ≤ y ^ n i) :
    ∑ U ∈ T.powerset.erase ∅, ∏ i ∈ U, a i ≤
      exp (N * exp (-(l / (log (x * y)⁻¹)⁻¹))) - 1 := by
  refine (sum_nonempty_powerset_prod_le_exp ha0).trans ?_
  gcongr
  calc ∑ i ∈ T, a i ≤ ∑ i ∈ T, y ^ n i := sum_le_sum ha
    _ ≤ N * ((x * y) ^ (l + 1) / (1 - x * y)) :=
        sum_pow_le_of_card_le hn hcount hN hx hy (by linarith)
    _ ≤ N * (x * y) ^ l := by
        gcongr
        exact pow_succ_div_one_sub_le hxy0.le hxy l
    _ = N * exp (-(l / (log (x * y)⁻¹)⁻¹)) := by rw [pow_eq_exp_neg_div _ hxy0]

/-- **The percolation bound for connected clusters.** Let `G` be a graph on `N` vertices with
maximum degree at most `Δ`, and put `x = max(1, Δ²)`. Let `T` be a finite family of connected
vertex sets of `G`, each with at least `l + 1` vertices, with weights `0 ≤ a C ≤ y^{#C}`, and let
`0 < x y ≤ 1/2`. Then the sum over nonempty subfamilies `U ⊆ T` of `∏_{C ∈ U} a C` is at most
`exp(N e^{−l/ξ}) − 1` with `ξ = 1 / ln(1/(xy))`. The count of clusters by size is
`SimpleGraph.card_connected_induce_le_exponential`, the lattice-animal bound cited by Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1234–1236. -/
theorem sum_nonempty_powerset_prod_le_percolation_connected {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {T : Finset (Finset V)}
    (hT : ∀ C ∈ T, (G.induce (C : Set V)).Connected) {l : ℕ} (hl : ∀ C ∈ T, l + 1 ≤ #C)
    {y : ℝ} (hy : 0 ≤ y) (hxy0 : 0 < (max 1 (Δ ^ 2) : ℕ) * y)
    (hxy : (max 1 (Δ ^ 2) : ℕ) * y ≤ 1 / 2) {a : Finset V → ℝ} (ha0 : ∀ C ∈ T, 0 ≤ a C)
    (ha : ∀ C ∈ T, a C ≤ y ^ #C) :
    ∑ U ∈ T.powerset.erase ∅, ∏ C ∈ U, a C ≤
      exp (Fintype.card V * exp (-(l / (log ((max 1 (Δ ^ 2) : ℕ) * y)⁻¹)⁻¹))) - 1 := by
  refine sum_nonempty_powerset_prod_le_percolation hl (fun k ↦ ?_) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hy hxy0 hxy ha0 ha
  have hsub : ({C ∈ T | #C = k} : Finset (Finset V)) ⊆
      ({S : Finset V | #S = k ∧ (G.induce (S : Set V)).Connected} : Finset (Finset V)) :=
      fun C hC ↦ by
    obtain ⟨hCT, hCk⟩ := mem_filter.1 hC
    exact mem_filter.2 ⟨mem_univ _, hCk, hT C hCT⟩
  exact_mod_cast (card_le_card hsub).trans (SimpleGraph.card_connected_induce_le_exponential G hΔ k)

/-- **A percolation temperature.** For real `J`, `S` and `x` there is `β₀ > 0` such that
`x (e^{Jβ} − 1) e^{SJβ} ≤ 1/2` for every `0 ≤ β ≤ β₀`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1242–1245 ("for sufficiently small `β`"). -/
theorem exists_percolation_temperature (J S x : ℝ) :
    ∃ β₀ > 0, ∀ β, 0 ≤ β → β ≤ β₀ → x * ((exp (J * β) - 1) * exp (S * J * β)) ≤ 1 / 2 := by
  have hc : Continuous fun β : ℝ ↦ x * ((exp (J * β) - 1) * exp (S * J * β)) := by fun_prop
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hc.continuousAt (1 / 2) (by norm_num)
  refine ⟨δ / 2, by linarith, fun β hβ0 hβ ↦ ?_⟩
  have hd : dist β 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hβ0]; linarith
  have := h hd
  simp only [mul_zero, exp_zero, sub_self, zero_mul, mul_zero, Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

end Percolation

end ClusterExpansion

/-!
## Hastings' percolation bound for clusters of large diameter

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1090–1114), defines the truncation
`ρ(β, l_proj)` of `e^{-βH}` by keeping the terms of its power series in which no cluster contains
two sites at distance larger than `l_proj`. With the size-threshold correction below, its
equation `perc2` (lines 1227–1254) gives the metric estimate

`Z⁻¹ |Tr (O ρ(β)) - Tr (O ρ(β, l_proj))| ≤ {exp[N (xy)⁻¹ exp(-l_proj/ξ_perc)] - 1} ‖O‖`.

This file states and proves that bound in the source's terms. The terms `h_k` of
`H = ∑_k h_k` act on supports `acts k` in a pseudometric space of sites, each support of diameter
at most `2R` (a term acting on the sites within `R` of its centre), and a set `C` of terms is
large when the support of `H_C` contains two sites at distance larger than `l_proj`
(`IsLargeDiam`). The overlap graph of the supports has maximum degree `Δ`.

* A connected set of `n` terms has support of diameter at most `2Rn`, so a large connected set
  has at least `⌊l_proj/(2R)⌋ + 1` terms.
* There are at most `N x^n` connected sets of `n` terms, with `N` the number of terms (the source
  indexes the terms by sites, so this is its number of sites) and
  `x = max(1, Δ²)` (the lattice-animal count, lines 1227–1229).
* A set `C` of terms and its boundary together have at most `(Δ + 1) n_C` terms.

With `y = (e^{βJ} - 1) e^{(Δ+1)Jβ}` and `0 < xy ≤ 1/2`, the error is at most
`‖O‖ (exp(N e^{-l/ξ}) - 1) Z` with `l = ⌊l_proj/(2R)⌋` and `ξ = 1/ln(1/(xy))`, and hence at most
`‖O‖ (exp(N (xy)^{-1} e^{-l_proj/ξ_perc}) - 1) Z` with `ξ_perc = 2R/ln(1/(xy))`, of order the
interaction range as the source states (line 1247).

**Local fix (size threshold):** the source starts the sum over cluster sizes at
`n = l_proj + 1` (line 1235), which presumes that a cluster of diameter larger than `l_proj` has
more than `l_proj` sites. With terms of range `R` only `n ≥ ⌊l_proj/(2R)⌋ + 1` holds, which is the
threshold used here; in units of distance this changes the constant `N` to `N (xy)^{-1}`.
Documented in `docs/paper-gaps/hastings05_percolation_cluster_size.tex`.

**Local fix (cluster boundary):** the boundary of a cluster is the set of terms whose support
meets the support of the cluster, the neighbours in the overlap graph, and the count
`n_C + n_B ≤ S n_C` of equation `percb2` holds with `S = Δ + 1`, which counts a term and its
overlap neighbours. Documented in `docs/paper-gaps/hastings05_cluster_boundary.tex`.

### Main results

* `ClusterExpansion.IsLargeDiam`: a set of terms whose support has diameter larger
  than `l_proj` (lines 1104–1107).
* `ClusterExpansion.dist_le_of_mem_biUnion_of_connected`: a connected set of `n`
  terms has support of diameter at most `2Rn`.
* `ClusterExpansion.card_ge_of_isLargeDiam`: a large connected set has at least
  `⌊l_proj/(2R)⌋ + 1` terms.
* `ClusterExpansion.card_add_card_boundary_le`: `n_C + n_{∂C} ≤ (Δ + 1) n_C`.
* `ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam`: equation
  `perc2` with the decay length `ξ = 1/ln(1/(xy))` in units of cluster size.
* `ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam_dist`:
  equation `perc2` with the decay length `ξ_perc = 2R/ln(1/(xy))` in units of distance.

### References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, lines 1090–1114 and 1227–1254.
-/

open Finset Matrix SimpleGraph
open scoped Matrix.Norms.L2Operator

namespace ClusterExpansion

variable {κ σ : Type*} [PseudoMetricSpace σ] [DecidableEq σ]

section Diameter

/-- A set `C` of terms is *large* when the support `⋃_{k ∈ C} acts k` of `H_C` contains two sites
at distance larger than `l_proj`. The truncation `ρ(β, l_proj)` keeps the terms of the power
series with no large cluster. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1104–1107. -/
def IsLargeDiam (acts : κ → Finset σ) (lproj : ℝ) (C : Finset κ) : Prop :=
  ∃ a ∈ C.biUnion acts, ∃ b ∈ C.biUnion acts, lproj < dist a b

variable {acts : κ → Finset σ} {R : ℝ}

/-- Along a walk of length `m` in the overlap graph induced on `C`, the supports of the endpoints
contain sites at distance at most `2R(m + 1)` when every support has diameter at most `2R`:
consecutive supports share a site. -/
theorem dist_le_of_walk (hR : ∀ k, ∀ a ∈ acts k, ∀ b ∈ acts k, dist a b ≤ 2 * R)
    {C : Finset κ} {u v : (C : Set κ)}
    (p : ((overlapGraph acts).induce (C : Set κ)).Walk u v) {a b : σ} (ha : a ∈ acts u)
    (hb : b ∈ acts v) : dist a b ≤ 2 * R * (p.length + 1) := by
  induction p generalizing a with
  | nil => simpa using hR _ a ha b hb
  | @cons u w v hadj p ih =>
    obtain ⟨-, c, hc⟩ := SimpleGraph.comap_adj.mp hadj
    rw [mem_inter] at hc
    calc dist a b ≤ dist a c + dist c b := dist_triangle _ _ _
      _ ≤ 2 * R + 2 * R * (p.length + 1) := add_le_add (hR _ a ha c hc.1) (ih hc.2 hb)
      _ = 2 * R * ((SimpleGraph.Walk.cons hadj p).length + 1) := by
          rw [SimpleGraph.Walk.length_cons]; push_cast; ring

/-- **The diameter of a connected set of terms.** If every support has diameter at most `2R` and
the terms of `C` are connected in the overlap graph, the support of `H_C` has diameter at most
`2R n_C`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1097–1100 (active bonds have
length at most `2R`). -/
theorem dist_le_of_mem_biUnion_of_connected (hR0 : 0 ≤ R)
    (hR : ∀ k, ∀ a ∈ acts k, ∀ b ∈ acts k, dist a b ≤ 2 * R) {C : Finset κ}
    (hC : ((overlapGraph acts).induce (C : Set κ)).Connected) {a b : σ}
    (ha : a ∈ C.biUnion acts) (hb : b ∈ C.biUnion acts) : dist a b ≤ 2 * R * #C := by
  classical
  obtain ⟨i, hi, hai⟩ := mem_biUnion.1 ha
  obtain ⟨j, hj, hbj⟩ := mem_biUnion.1 hb
  obtain ⟨p⟩ := hC.preconnected ⟨i, hi⟩ ⟨j, hj⟩
  have hlen : (p.toPath : _).1.length < #C := by
    simpa using (p.toPath : _).2.length_lt
  refine (dist_le_of_walk hR (p.toPath : _).1 hai hbj).trans ?_
  have : ((p.toPath : _).1.length : ℝ) + 1 ≤ #C := by exact_mod_cast hlen
  gcongr

variable [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- **The size threshold.** If every support has diameter at most `2R` with `R > 0`, a large
connected set of terms has at least `⌊l_proj/(2R)⌋ + 1` terms. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, line 1235, starts the sum at `l_proj + 1` instead; see
the section docstring. -/
theorem card_ge_of_isLargeDiam (hR0 : 0 < R)
    (hR : ∀ k, ∀ a ∈ acts k, ∀ b ∈ acts k, dist a b ≤ 2 * R) {lproj : ℝ} {C : Finset κ}
    (hC : C ∈ largeConnected (overlapGraph acts) (IsLargeDiam acts lproj)) :
    ⌊lproj / (2 * R)⌋₊ + 1 ≤ #C := by
  obtain ⟨hconn, a, ha, b, hb, hab⟩ := (mem_largeConnected _).1 hC
  have hd := dist_le_of_mem_biUnion_of_connected hR0.le hR hconn ha hb
  obtain ⟨i, hi, -⟩ := mem_biUnion.1 ha
  have hne : #C ≠ 0 := (card_pos.2 ⟨i, hi⟩).ne'
  rw [Nat.add_one_le_iff, Nat.floor_lt' hne, div_lt_iff₀ (by positivity)]
  linarith [mul_comm (2 * R) (#C : ℝ)]

end Diameter

section Boundary

variable [Fintype κ] [DecidableEq κ]

/-- **The boundary count.** In a graph of maximum degree `Δ`, a set `C` and its boundary have
together at most `(Δ + 1) n_C` elements. For the overlap graph this is the count
`n_C + n_B ≤ S n_C` of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, line 1186, with
`S = Δ + 1`. -/
theorem card_add_card_boundary_le (G : SimpleGraph κ) [DecidableRel G.Adj] {Δ : ℕ}
    (hΔ : ∀ k, G.degree k ≤ Δ) (C : Finset κ) : #C + #(boundary G C) ≤ (Δ + 1) * #C :=
  card_add_card_clusterBoundary_le _ C (fun i ↦ insert i (G.neighborFinset i))
    (fun i _ ↦ mem_insert_self i _)
    (fun j i _ hij ↦ mem_insert_of_mem ((G.mem_neighborFinset i j).2
      ((G.mem_neighborFinset j i).1 hij).symm))
    fun i _ ↦ (card_insert_le _ _).trans (by
      have := hΔ i; rw [G.card_neighborFinset_eq_degree]; omega)

end Boundary

section Percolation

variable [Fintype κ] [DecidableEq κ] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {acts : κ → Finset σ} {R : ℝ}

open Classical in
/-- **Equation `perc2`, in units of cluster size.** Let the terms `h_k` of the Hermitian
`H = ∑_k h_k` be Hermitian with `‖h_k‖ ≤ J`, act on supports of diameter at most `2R` with
`R > 0`, and overlap at most `Δ` other terms each. Let `β ≥ 0`, `x = max(1, Δ²)`,
`y = (e^{βJ} - 1) e^{(Δ+1)Jβ}` and `0 < xy ≤ 1/2`. Then the truncation `ρ(β, l_proj)`, which
keeps the terms of the power series with no cluster of diameter larger than `l_proj`, satisfies
`|Tr (O (e^{-βH} - ρ(β, l_proj)))| ≤ ‖O‖ (exp(N e^{-l/ξ}) - 1) Tr e^{-βH}`, with `N` the number
of terms, `l = ⌊l_proj/(2R)⌋` and `ξ = 1/ln(1/(xy))`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1227–1254, with the size threshold of the section docstring. The hypothesis
`0 < xy` only excludes `β J = 0`, where the truncation is exact and `ξ` is undefined. -/
theorem norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam (hR0 : 0 < R)
    (hR : ∀ k, ∀ a ∈ acts k, ∀ b ∈ acts k, dist a b ≤ 2 * R) {Δ : ℕ}
    (hΔ : ∀ k, (overlapGraph acts).degree k ≤ Δ) (lproj : ℝ) {H : Matrix ι ι ℂ}
    (hHerm : H.IsHermitian) {h : κ → Matrix ι ι ℂ} (hH : H = ∑ k, h k)
    (hh : ∀ k, (h k).IsHermitian) {J : ℝ} (hJ : ∀ k, ‖h k‖ ≤ J) (O : Matrix ι ι ℂ) {β : ℝ}
    (hβ : 0 ≤ β)
    (hxy0 : 0 < ((max 1 (Δ ^ 2) : ℕ) : ℝ) *
      ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)))
    (hxy : ((max 1 (Δ ^ 2) : ℕ) : ℝ) *
      ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)) ≤ 1 / 2) :
    ‖(O * (NormedSpace.exp (-(β • H)) -
        truncatedExp (overlapGraph acts) (IsLargeDiam acts lproj) h β)).trace‖ ≤
      ‖O‖ * (Real.exp (Fintype.card κ * Real.exp (-(⌊lproj / (2 * R)⌋₊ /
          (Real.log (((max 1 (Δ ^ 2) : ℕ) : ℝ) *
            ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)))⁻¹)⁻¹))) - 1) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  set G := overlapGraph acts
  set T := largeConnected G (IsLargeDiam acts lproj)
  set y := (Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)
  have hS : ∀ C ∈ T, ((#C : ℝ) + #(boundary G C)) ≤ ((Δ : ℝ) + 1) * #C := fun C _ ↦ by
    exact_mod_cast card_add_card_boundary_le G hΔ C
  refine (norm_trace_mul_exp_sub_truncatedExp_le G _ hHerm hH hh hJ O hβ hS).trans ?_
  have hZ := (hHerm.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_nonneg
  have hy : 0 ≤ y := (pos_of_mul_pos_right hxy0 (Nat.cast_nonneg _)).le
  rw [← sum_mul, ← mul_sum]
  gcongr
  calc ∑ U ∈ T.powerset with IsAdmissible G U ∧ U.Nonempty, ∏ C ∈ U, y ^ #C
      ≤ ∑ U ∈ T.powerset.erase ∅, ∏ C ∈ U, y ^ #C :=
        sum_le_sum_of_subset_of_nonneg (fun U hU ↦ by
          obtain ⟨hUT, -, hne⟩ := mem_filter.1 hU
          exact mem_erase.2 ⟨hne.ne_empty, hUT⟩)
          fun _ _ _ ↦ prod_nonneg fun _ _ ↦ pow_nonneg hy _
    _ ≤ _ := sum_nonempty_powerset_prod_le_percolation_connected G hΔ
        (fun C hC ↦ ((mem_largeConnected G).1 hC).1)
        (fun C hC ↦ card_ge_of_isLargeDiam hR0 hR hC) hy hxy0 hxy
        (fun _ _ ↦ pow_nonneg hy _) fun _ _ ↦ le_rfl

/-- `e^{-l/ξ} ≤ r^{-1} e^{-l_proj/ξ_perc}` for `l = ⌊l_proj/(2R)⌋`, `ξ = 1/ln(1/r)` and
`ξ_perc = 2R/ln(1/r)`, when `0 < r < 1` and `R > 0`: the passage from cluster size to distance,
using `l ≥ l_proj/(2R) - 1`. -/
theorem exp_neg_floor_div_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hR0 : 0 < R) (lproj : ℝ) :
    Real.exp (-(⌊lproj / (2 * R)⌋₊ / (Real.log r⁻¹)⁻¹)) ≤
      r⁻¹ * Real.exp (-(lproj / (2 * R / Real.log r⁻¹))) := by
  have hE : r⁻¹ = Real.exp (Real.log r⁻¹) := (Real.exp_log (inv_pos.2 hr0)).symm
  set L := Real.log r⁻¹ with hL
  have hL0 : 0 < L := Real.log_pos ((one_lt_inv₀ hr0).2 hr1)
  have hfl := Nat.sub_one_lt_floor (lproj / (2 * R))
  calc Real.exp (-(⌊lproj / (2 * R)⌋₊ / L⁻¹)) ≤ Real.exp (L + -(lproj / (2 * R / L))) := by
        refine Real.exp_le_exp.2 ?_
        rw [div_inv_eq_mul, show lproj / (2 * R / L) = L * (lproj / (2 * R)) by
          field_simp]
        nlinarith [mul_le_mul_of_nonneg_left hfl.le hL0.le]
    _ = r⁻¹ * Real.exp (-(lproj / (2 * R / L))) := by rw [Real.exp_add, ← hE]

open Classical in
/-- **Equation `perc2`, in units of distance.** Under the hypotheses of
`norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam`,
`|Tr (O (e^{-βH} - ρ(β, l_proj)))| ≤ ‖O‖ (exp(N (xy)^{-1} e^{-l_proj/ξ_perc}) - 1) Tr e^{-βH}`
with `ξ_perc = 2R/ln(1/(xy))`, of order the interaction range. After division by
`Z = Tr e^{-βH}` this is the source's `{exp[N exp(-l_proj/ξ_perc)] - 1} ‖O‖` with the constant
`N (xy)^{-1}` in place of `N` (see the section docstring). Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1246–1254. -/
theorem norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam_dist (hR0 : 0 < R)
    (hR : ∀ k, ∀ a ∈ acts k, ∀ b ∈ acts k, dist a b ≤ 2 * R) {Δ : ℕ}
    (hΔ : ∀ k, (overlapGraph acts).degree k ≤ Δ) (lproj : ℝ) {H : Matrix ι ι ℂ}
    (hHerm : H.IsHermitian) {h : κ → Matrix ι ι ℂ} (hH : H = ∑ k, h k)
    (hh : ∀ k, (h k).IsHermitian) {J : ℝ} (hJ : ∀ k, ‖h k‖ ≤ J) (O : Matrix ι ι ℂ) {β : ℝ}
    (hβ : 0 ≤ β)
    (hxy0 : 0 < ((max 1 (Δ ^ 2) : ℕ) : ℝ) *
      ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)))
    (hxy : ((max 1 (Δ ^ 2) : ℕ) : ℝ) *
      ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)) ≤ 1 / 2) :
    ‖(O * (NormedSpace.exp (-(β • H)) -
        truncatedExp (overlapGraph acts) (IsLargeDiam acts lproj) h β)).trace‖ ≤
      ‖O‖ * (Real.exp (Fintype.card κ *
          ((((max 1 (Δ ^ 2) : ℕ) : ℝ) *
            ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)))⁻¹ *
          Real.exp (-(lproj / (2 * R / Real.log (((max 1 (Δ ^ 2) : ℕ) : ℝ) *
            ((Real.exp (β * J) - 1) * Real.exp (((Δ : ℝ) + 1) * J * β)))⁻¹))))) - 1) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  refine (norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam hR0 hR hΔ lproj hHerm hH hh hJ O
    hβ hxy0 hxy).trans ?_
  have hZ := (hHerm.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_nonneg
  have key := exp_neg_floor_div_le hxy0 (by linarith) hR0 lproj
  gcongr

end Percolation

end ClusterExpansion
