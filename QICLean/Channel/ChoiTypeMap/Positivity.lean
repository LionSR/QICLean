/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.DeterminantTraceBound
import QICLean.Channel.ChoiTypeMap

/-!
# Positivity of the first Choi-type map

This module proves the case \(n=1\) of the positivity assertion in Wolf
Chapter 3, Example 3.1, equation (3.20), local source lines 357–365.  The proof
establishes the boundary-inclusive cyclic reciprocal inequality
\[
  \sum_i \frac{x_i}{(d-1)x_i+x_{i-1}} \le 1
\]
for every nonnegative family on `ZMod d`, applies it to the diagonal weights of
the rank-one formula `Matrix.choiTypeMap_vecMulVec`, and then uses spectral
decomposition to pass from rank-one projectors to all positive semidefinite
matrices.

The middle range \(2\le n\le d-3\) and indecomposability are not proved here.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Example 3.1, equation (3.20)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder InnerProductSpace
open Finset

namespace Matrix

variable {d : ℕ} [NeZero d]

/-! ## The bottom of Wolf's range: `n = 1`

For `n = 1` the Choi rank-one diagonal weight collapses to
\(a_i = (d-1)x_i + x_{i-1}\) with \(x_i = |v_i|^2\), and the cyclic
reciprocal estimate \(\sum_i x_i/((d-1)x_i + x_{i-1}) \le 1\) holds for
every \(d \ge 2\).  In the interior (all \(x_i > 0\)), writing the
summand as \(1/(y_i + (d-1))\) with \(y_i = x_{i-1}/x_i\) gives
\(\prod_i y_i = 1\).  After clearing denominators and multiplying the
resulting difference by \(d-1\), its expansion in the elementary symmetric
polynomials \(e_k\) of the \(y\)'s is
\(\sum_k (k-1)(d-1)^{d-k} e_k \ge 0\).  That estimate follows from
the AM–GM bound \(e_k \ge \binom{d}{k}\) (the product of all
\(k\)-subset monomials is \((\prod_i y_i)^{\binom{d-1}{k-1}} = 1\)) and
the binomial identity \(\sum_k (k-1)(d-1)^{d-k}\binom{d}{k} = 0\).  If
some coordinate vanishes, at most \(d-1\) summands are nonzero and each is at
most \(1/(d-1)\), which proves the boundary case directly.

This is the case \(n = 1\) of the positivity assertion of Wolf Chapter 3,
Example 3.1, equation (3.20) (ch03 lines 357–365); that case is classical
(Tanahashi–Tomiyama, *Indecomposable positive maps in matrix algebras*,
Canad. Math. Bull. 31 (1988), 308–317).  The proof here is the
elementary-symmetric expansion sketched above, not the variational argument
of Yamagami needed for the middle of the range. -/

/-- Each variable appears in the same number of `k`-subsets of the index
type, so the product of all `k`-subset monomials of a product-one family is
one: it is a power of the total product.  This is the geometric-mean
computation behind the AM–GM bound on the elementary symmetric sums. -/
private theorem prod_powersetCard_prod_eq_one {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (hprod : ∏ i, y i = 1) {k : ℕ} :
    ∏ t ∈ Finset.powersetCard k Finset.univ, ∏ j ∈ t, y j = 1 := by
  classical
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [Finset.powersetCard_zero]
  have hmem : ∀ t ∈ Finset.powersetCard k (Finset.univ : Finset ι),
      ∏ j ∈ t, y j = ∏ j ∈ Finset.univ, if j ∈ t then y j else 1 := by
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    have h2 : ∏ j ∈ t, (if j ∈ t then y j else 1) =
        ∏ j ∈ Finset.univ, if j ∈ t then y j else 1 :=
      Finset.prod_subset ht.1 fun j _ hj => by simp [hj]
    rw [← h2]
    exact Finset.prod_congr rfl fun j hj => by simp [hj]
  rw [Finset.prod_congr rfl hmem, Finset.prod_comm]
  -- The fiber of `k`-subsets containing `j` is in bijection with the
  -- `(k - 1)`-subsets of the remaining indices, via erasing `j`.
  have hfiber : ∀ j : ι, ∏ t ∈ Finset.powersetCard k Finset.univ,
        (if j ∈ t then y j else 1) =
      y j ^ ((Fintype.card ι - 1).choose (k - 1)) := by
    intro j
    rw [← Finset.prod_filter, Finset.prod_const]
    congr 1
    have hbij : ((Finset.powersetCard k Finset.univ).filter fun t => j ∈ t).card =
        (Finset.powersetCard (k - 1) (Finset.univ.erase j)).card := by
      refine Finset.card_bij (fun t _ => t.erase j) ?_ ?_ ?_
      · intro t ht
        rw [Finset.mem_filter, Finset.mem_powersetCard] at ht
        obtain ⟨⟨htsub, htc⟩, hjt⟩ := ht
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.erase_subset_erase j htsub,
          by rw [Finset.card_erase_of_mem hjt, htc]⟩
      · intro t₁ ht₁ t₂ ht₂ h
        rw [Finset.mem_filter] at ht₁ ht₂
        have h₁ := Finset.insert_erase ht₁.2
        have h₂ := Finset.insert_erase ht₂.2
        rw [← h₁, h]
        exact h₂
      · intro u hu
        rw [Finset.mem_powersetCard] at hu
        obtain ⟨husub, huc⟩ := hu
        have hju : j ∉ u := fun h => (Finset.mem_erase.1 (husub h)).1 rfl
        refine ⟨insert j u, ?_, Finset.erase_insert hju⟩
        rw [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self j u⟩
        · exact Finset.insert_subset (Finset.mem_univ j) (Finset.subset_univ u)
        · rw [Finset.card_insert_of_notMem hju, huc]
          omega
    rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ]
  rw [Finset.prod_congr rfl fun j _ => hfiber j, Finset.prod_pow, hprod, one_pow]

/-- **AM–GM bound on the elementary symmetric sums.**  For a positive
product-one family, each elementary symmetric sum is bounded below by the
corresponding binomial coefficient: the `k`-subset monomials have geometric
mean `1` by `prod_powersetCard_prod_eq_one`, and there are
`Nat.choose d k` of them. -/
private theorem card_choose_le_sum_powersetCard_prod {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (hy : ∀ i, 0 < y i) (hprod : ∏ i, y i = 1) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    (Nat.choose (Fintype.card ι) k : ℝ) ≤
      ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ j ∈ t, y j := by
  classical
  set s := Finset.powersetCard k (Finset.univ : Finset ι) with hs_def
  have hcard : s.card = Nat.choose (Fintype.card ι) k := by
    rw [hs_def, Finset.card_powersetCard, Finset.card_univ]
  have hmpos : 0 < s.card := hcard.symm ▸ Nat.choose_pos hk
  have hnonneg : ∀ t : ↥s, 0 ≤ ∏ j ∈ t.1, y j :=
    fun t => Finset.prod_nonneg fun j _ => (hy j).le
  have hamgm := pow_card_mul_prod_le_sum_pow' (fun t : ↥s => ∏ j ∈ t.1, y j) hnonneg
  simp only [Fintype.card_coe, Finset.univ_eq_attach] at hamgm
  rw [Finset.prod_attach s (fun t => ∏ j ∈ t, y j),
    Finset.sum_attach s (fun t => ∏ j ∈ t, y j),
    prod_powersetCard_prod_eq_one y hprod, mul_one] at hamgm
  have heR : (0 : ℝ) ≤ ∑ t ∈ s, ∏ j ∈ t, y j :=
    Finset.sum_nonneg fun t _ => Finset.prod_nonneg fun j _ => (hy j).le
  have hle : ((s.card : ℝ)) ≤ ∑ t ∈ s, ∏ j ∈ t, y j :=
    (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) heR hmpos.ne').mp hamgm
  rwa [hcard] at hle

/-- **Master expansion.**  With `s = d - 1` (as a real) and `d` the
cardinality of the index type, the difference of the full product and the sum
of the erased products, scaled by `s`, expands as the signed subset sum
`∑ t, (|t| - 1) s ^ (d - |t|) y^t`: the scaled `t`-coefficient satisfies
`s * (s ^ (d - |t|) - (d - |t|) * s ^ (d - 1 - |t|)) =
  (|t| - 1) * s ^ (d - |t|)`, using `s = d - 1`. -/
private theorem mul_prod_add_sub_sum_prod_erase {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) :
    ((Fintype.card ι : ℝ) - 1) *
        (∏ i, (y i + ((Fintype.card ι : ℝ) - 1)) -
          ∑ i, ∏ j ∈ Finset.univ.erase i, (y j + ((Fintype.card ι : ℝ) - 1))) =
      ∑ t ∈ Finset.univ.powerset,
        ((t.card : ℝ) - 1) * ((Fintype.card ι : ℝ) - 1) ^ (Fintype.card ι - t.card) *
          ∏ j ∈ t, y j := by
  classical
  set d : ℕ := Fintype.card ι with hd
  set s : ℝ := (d : ℝ) - 1 with hs
  -- Expansion of the full product over the powerset.
  have hP : ∏ i, (y i + s) =
      ∑ t ∈ Finset.univ.powerset, (∏ j ∈ t, y j) * s ^ (d - t.card) := by
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_powerset] at ht
    rw [Finset.prod_const, Finset.card_sdiff_of_subset ht, Finset.card_univ, ← hd]
  -- Expansion of one erased product over the powerset of the erased index set.
  have hQ : ∀ i : ι, ∏ j ∈ Finset.univ.erase i, (y j + s) =
      ∑ t ∈ (Finset.univ.erase i).powerset, (∏ j ∈ t, y j) * s ^ (d - 1 - t.card) := by
    intro i
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_powerset] at ht
    rw [Finset.prod_const, Finset.card_sdiff_of_subset ht, Finset.card_erase_of_mem
      (Finset.mem_univ i), Finset.card_univ, ← hd]
  -- The erased powersets are the fibers of the full powerset.
  have hps : ∀ i : ι, (Finset.univ.erase i : Finset ι).powerset =
      Finset.univ.powerset.filter fun t => i ∉ t := by
    intro i
    ext t
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨Subset.trans h (Finset.erase_subset _ _), (Finset.subset_erase.1 h).2⟩
    · intro h
      exact Finset.subset_erase.2 ⟨Finset.subset_univ t, h.2⟩
  -- Summing the erased expansions over `i` double-counts each subset by its
  -- complement cardinality.
  have hsum : ∑ i, ∏ j ∈ Finset.univ.erase i, (y j + s) =
      ∑ t ∈ Finset.univ.powerset,
        (((d - t.card : ℕ) : ℝ)) * ((∏ j ∈ t, y j) * s ^ (d - 1 - t.card)) := by
    have step : ∀ i : ι, ∑ t ∈ (Finset.univ.erase i).powerset,
          (∏ j ∈ t, y j) * s ^ (d - 1 - t.card) =
        ∑ t ∈ Finset.univ.powerset,
          (if i ∉ t then (∏ j ∈ t, y j) * s ^ (d - 1 - t.card) else 0) := by
      intro i
      rw [hps i, Finset.sum_filter]
    rw [Finset.sum_congr rfl (fun i _ => hQ i),
      Finset.sum_congr rfl (fun i _ => step i), Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_filter]
    have hfilter : Finset.univ.filter (fun i => i ∉ t) = Finset.univ \ t := by
      ext i
      simp
    rw [hfilter, Finset.sum_const, nsmul_eq_mul,
      Finset.card_sdiff_of_subset (Finset.subset_univ t), Finset.card_univ, ← hd]
  -- Combine and compare subset by subset.
  rw [hP, hsum, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_powerset] at ht
  have htc : t.card ≤ d := by
    have h1 := Finset.card_le_card ht
    rwa [Finset.card_univ, ← hd] at h1
  rcases Nat.eq_or_lt_of_le htc with hteq | htlt
  · have htuniv : t = Finset.univ := by
      have h1 : t.card = (Finset.univ : Finset ι).card := by
        rwa [Finset.card_univ, ← hd]
      exact Finset.eq_univ_of_card t h1
    subst htuniv
    simp [hs, hd]
  · have hexp : d - t.card = (d - 1 - t.card) + 1 := by omega
    have hpow : s ^ (d - t.card) = s ^ (d - 1 - t.card) * s := by
      rw [hexp, pow_succ]
    have hcast : (((d - t.card : ℕ)) : ℝ) = (d : ℝ) - t.card := by
      rw [Nat.cast_sub (le_of_lt htlt)]
    rw [hpow, hcast, hs]
    ring

/-- The powerset sum of the signed monomial terms groups by subset
cardinality into the elementary symmetric sums. -/
private theorem sum_powerset_signed_monomial_eq_sum_range {ι : Type*} [Fintype ι]
    (y : ι → ℝ) :
    ∑ t ∈ Finset.univ.powerset,
        ((t.card : ℝ) - 1) * ((Fintype.card ι : ℝ) - 1) ^ (Fintype.card ι - t.card) *
          ∏ j ∈ t, y j =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        ((k : ℝ) - 1) * ((Fintype.card ι : ℝ) - 1) ^ (Fintype.card ι - k) *
          ∑ t ∈ Finset.univ.powersetCard k, ∏ j ∈ t, y j := by
  classical
  set d : ℕ := Fintype.card ι with hd
  set s : ℝ := (d : ℝ) - 1 with hs
  have hmaps : ∀ t ∈ (Finset.univ : Finset ι).powerset, t.card ∈ Finset.range (d + 1) := by
    intro t ht
    rw [Finset.mem_range]
    have h1 := Finset.card_le_card (Finset.mem_powerset.1 ht)
    rw [Finset.card_univ, ← hd] at h1
    omega
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset ι).powerset)
    (t := Finset.range (d + 1)) (g := fun t : Finset ι => t.card) hmaps]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Finset.powersetCard_eq_filter]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht2 : t.card = k := (Finset.mem_powersetCard.1 ht).2
  rw [ht2]

/-- **Polynomial form of the product-one reciprocal bound** (interior of the
Tanahashi–Tomiyama slice).  For `d ≥ 2` and strictly positive `y` with
product one, the sum of the erased products is at most the full product:
scaled by `s = d - 1`, the difference expands as
`∑_k (k-1) s ^ (d-k) e_k`, which is `≥ -s ^ d + ∑_k (k-1) s ^ (d-k)
Nat.choose d k = 0` by the AM–GM bound
`card_choose_le_sum_powersetCard_prod` and the binomial identity obtained by
evaluating the same expansion at `y ≡ 1`. -/
private theorem sum_prod_erase_le_prod_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hd2 : 2 ≤ Fintype.card ι) (y : ι → ℝ) (hy : ∀ i, 0 < y i) (hprod : ∏ i, y i = 1) :
    ∑ i, ∏ j ∈ Finset.univ.erase i, (y j + ((Fintype.card ι : ℝ) - 1)) ≤
      ∏ i, (y i + ((Fintype.card ι : ℝ) - 1)) := by
  classical
  set d : ℕ := Fintype.card ι with hd
  set s : ℝ := (d : ℝ) - 1 with hs
  have hs_pos : 0 < s := by
    rw [hs]
    have h2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    linarith
  have hsplit : ∀ (g : ℕ → ℝ), ∑ k ∈ Finset.range (d + 1), g k =
      (∑ k ∈ Finset.range 2, g k) + ∑ k ∈ Finset.Ico 2 (d + 1), g k := by
    intro g
    exact (Finset.sum_range_add_sum_Ico g (by omega : (2 : ℕ) ≤ d + 1)).symm
  have hpair : ∀ (g : ℕ → ℝ), ∑ k ∈ Finset.range 2, g k = g 0 + g 1 := by
    intro g
    rw [show Finset.range 2 = {0, 1} from by ext k; simp; omega,
      Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  -- The binomial-coefficient identity, from the master expansion at `y ≡ 1`.
  have hD : ∑ k ∈ Finset.range (d + 1),
      ((k : ℝ) - 1) * s ^ (d - k) * (Nat.choose d k : ℝ) = 0 := by
    have hB := mul_prod_add_sub_sum_prod_erase (fun _ : ι => (1 : ℝ))
    have hC := sum_powerset_signed_monomial_eq_sum_range (fun _ : ι => (1 : ℝ))
    have hBC : s * (∏ _i, ((1 : ℝ) + s) - ∑ i, ∏ _j ∈ Finset.univ.erase i, ((1 : ℝ) + s)) =
        ∑ k ∈ Finset.range (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
          ∑ t ∈ (Finset.univ : Finset ι).powersetCard k, ∏ _j ∈ t, (1 : ℝ) :=
      hB.trans hC
    have he1 : ∀ k : ℕ,
        (∑ t ∈ (Finset.univ : Finset ι).powersetCard k, ∏ _j ∈ t, (1 : ℝ)) =
        (Nat.choose d k : ℝ) := by
      intro k
      simp only [Finset.prod_const_one, Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.card_powersetCard, Finset.card_univ, ← hd]
    have hP1 : ∏ _i : ι, ((1 : ℝ) + s) = (1 + s) ^ d := by
      rw [Finset.prod_const, Finset.card_univ, ← hd]
    have hQ1 : ∀ i : ι, ∏ _j ∈ Finset.univ.erase i, ((1 : ℝ) + s) = (1 + s) ^ (d - 1) := by
      intro i
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, ← hd]
    rw [hP1, Finset.sum_congr rfl (fun i _ => hQ1 i), Finset.sum_const, Finset.card_univ,
      ← hd, nsmul_eq_mul] at hBC
    have hzero : (1 + s) ^ d - (d : ℝ) * (1 + s) ^ (d - 1) = 0 := by
      have h1s : (1 : ℝ) + s = d := by rw [hs]; ring
      have hpow : (1 + s) ^ d = (1 + s) ^ (d - 1) * (1 + s) := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpow, h1s]
      ring
    rw [hzero, mul_zero] at hBC
    simp only [he1] at hBC
    exact hBC.symm
  -- The master expansion, grouped, with the `k = 0, 1` slices peeled off.
  have hBy := mul_prod_add_sub_sum_prod_erase y
  have hCy := sum_powerset_signed_monomial_eq_sum_range y
  have hBC : s * (∏ i, (y i + s) - ∑ i, ∏ j ∈ Finset.univ.erase i, (y j + s)) =
      ∑ k ∈ Finset.range (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        ∑ t ∈ Finset.univ.powersetCard k, ∏ j ∈ t, y j :=
    hBy.trans hCy
  have hrange : (∑ k ∈ Finset.range (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (∑ t ∈ Finset.univ.powersetCard k, ∏ j ∈ t, y j)) =
      -s ^ d + ∑ k ∈ Finset.Ico 2 (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (∑ t ∈ Finset.univ.powersetCard k, ∏ j ∈ t, y j) := by
    rw [hsplit, hpair]
    have h0 : (((0 : ℕ) : ℝ) - 1) * s ^ (d - 0) *
        (∑ t ∈ Finset.univ.powersetCard 0, ∏ j ∈ t, y j) = -s ^ d := by
      simp
    have h1 : (((1 : ℕ) : ℝ) - 1) * s ^ (d - 1) *
        (∑ t ∈ Finset.univ.powersetCard 1, ∏ j ∈ t, y j) = 0 := by
      simp
    rw [h0, h1, add_zero]
  have hrangeC : (∑ k ∈ Finset.range (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (Nat.choose d k : ℝ)) =
      -s ^ d + ∑ k ∈ Finset.Ico 2 (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (Nat.choose d k : ℝ) := by
    rw [hsplit, hpair]
    have h0 : (((0 : ℕ) : ℝ) - 1) * s ^ (d - 0) * (Nat.choose d 0 : ℝ) = -s ^ d := by
      simp
    have h1 : (((1 : ℕ) : ℝ) - 1) * s ^ (d - 1) * (Nat.choose d 1 : ℝ) = 0 := by
      simp
    rw [h0, h1, add_zero]
  have hXC : (∑ k ∈ Finset.Ico 2 (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (Nat.choose d k : ℝ)) = s ^ d := by
    linarith [hD, hrangeC]
  have hAmgm : (∑ k ∈ Finset.Ico 2 (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (Nat.choose d k : ℝ)) ≤
      ∑ k ∈ Finset.Ico 2 (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (∑ t ∈ Finset.univ.powersetCard k, ∏ j ∈ t, y j) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk2 : 2 ≤ k := (Finset.mem_Ico.1 hk).1
    have hkd : k ≤ d := by
      have h2 := (Finset.mem_Ico.1 hk).2
      omega
    have hcoeff : (0 : ℝ) ≤ ((k : ℝ) - 1) * s ^ (d - k) := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      exact mul_nonneg (by linarith) (pow_nonneg hs_pos.le _)
    exact mul_le_mul_of_nonneg_left
      (card_choose_le_sum_powersetCard_prod y hy hprod (hd ▸ hkd)) hcoeff
  have key : 0 ≤ s * (∏ i, (y i + s) - ∑ i, ∏ j ∈ Finset.univ.erase i, (y j + s)) := by
    rw [hBC, hrange]
    linarith [hXC ▸ hAmgm]
  have hmain : 0 ≤ ∏ i, (y i + s) - ∑ i, ∏ j ∈ Finset.univ.erase i, (y j + s) :=
    nonneg_of_mul_nonneg_left (by rwa [mul_comm] at key) hs_pos
  exact sub_nonneg.mp hmain

/-- **Reciprocal sum bound for product-one families** (interior of the
Tanahashi–Tomiyama slice, reciprocal form).  For `d ≥ 2` and strictly
positive `y` with `∏ y_i = 1`, `∑ i, 1 / (y_i + (d - 1)) ≤ 1`. -/
private theorem sum_inv_add_card_sub_one_le_one {ι : Type*} [Fintype ι]
    (hd2 : 2 ≤ Fintype.card ι) (y : ι → ℝ) (hy : ∀ i, 0 < y i) (hprod : ∏ i, y i = 1) :
    ∑ i, 1 / (y i + ((Fintype.card ι : ℝ) - 1)) ≤ 1 := by
  classical
  set d : ℕ := Fintype.card ι with hd
  set s : ℝ := (d : ℝ) - 1 with hs
  have hs_pos : 0 < s := by
    rw [hs]
    have h2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    linarith
  have hD : ∀ i : ι, 0 < y i + s := fun i => add_pos (hy i) hs_pos
  have hP : 0 < ∏ i, (y i + s) := Finset.prod_pos (fun i _ => hD i)
  have hEpoly := sum_prod_erase_le_prod_add hd2 y hy hprod
  have hdiv : ∀ i : ι, 1 / (y i + s) =
      (∏ j ∈ Finset.univ.erase i, (y j + s)) / ∏ j, (y j + s) := by
    intro i
    have h1 : y i + s ≠ 0 := (hD i).ne'
    have h2 : (∏ j ∈ Finset.univ.erase i, (y j + s)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => (hD j).ne'
    rw [← Finset.mul_prod_erase Finset.univ (fun j => y j + s) (Finset.mem_univ i)]
    field_simp
  rw [Finset.sum_congr rfl fun i _ => hdiv i, ← Finset.sum_div]
  exact (div_le_one hP).2 hEpoly

/-- Interior of the first cyclic reciprocal estimate: for `d ≥ 2` and
strictly positive `x` on `ZMod d`,
`∑ i, x i / ((d - 1) * x i + x (i - 1)) ≤ 1`.  With `y_i = x_{i-1} / x_i`
the product of the `y`'s telescopes to `1` by cyclic shift invariance, and
the summand becomes `1 / (y_i + (d - 1))`, so the claim reduces to the
product-one reciprocal bound. -/
theorem choiType_cyclic_reciprocal_one_of_pos (hd : 2 ≤ d) (x : ZMod d → ℝ)
    (hx : ∀ i, 0 < x i) :
    ∑ i, x i / (((d : ℝ) - 1) * x i + x (i - 1)) ≤ 1 := by
  classical
  set y : ZMod d → ℝ := fun i => x (i - 1) / x i with hy_def
  have hy : ∀ i, 0 < y i := fun i => div_pos (hx _) (hx _)
  have hprod : ∏ i, y i = 1 := by
    have hshift : ∏ i, x (i - 1) = ∏ i, x i :=
      Equiv.prod_comp (Equiv.subRight (1 : ZMod d)) x
    rw [hy_def, Finset.prod_div_distrib, hshift,
      div_self (Finset.prod_pos (fun i _ => hx i)).ne']
  have hcard : Fintype.card (ZMod d) = d := ZMod.card d
  have hrecip := sum_inv_add_card_sub_one_le_one (ι := ZMod d) (by rwa [hcard]) y hy hprod
  rw [hcard] at hrecip
  refine le_trans (Finset.sum_le_sum fun i _ => le_of_eq ?_) hrecip
  have hxi : x i ≠ 0 := (hx i).ne'
  have hyi : y i = x (i - 1) / x i := rfl
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have h2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hDpos : (((d : ℝ) - 1) * x i + x (i - 1)) ≠ 0 :=
    (add_pos (mul_pos hd1 (hx i)) (hx _)).ne'
  have hEpos : (x (i - 1) / x i + ((d : ℝ) - 1)) ≠ 0 :=
    (add_pos (div_pos (hx _) (hx _)) hd1).ne'
  rw [hyi]
  field_simp
  ring

/-- **The first cyclic reciprocal estimate, including boundary points.**  For
`d ≥ 2` and nonnegative `x` on `ZMod d`,
`∑ i, x i / ((d - 1) * x i + x (i - 1)) ≤ 1`.

In the interior this is `choiType_cyclic_reciprocal_one_of_pos`.  If some
coordinate vanishes, only at most `d - 1` summands are nonzero, and each is at
most `1 / (d - 1)`.

This is the scalar inequality for the case `n = 1` of Wolf Chapter 3,
Example 3.1, equation (3.20) (ch03 lines 357–365).

**Scope restriction:** See
`docs/paper-gaps/wolf_ex3_1_choi_positivity_subcase_scope.tex`.  The theorem
covers the full bottom slice `n = 1`, not the middle range `2 ≤ n ≤ d - 3`. -/
theorem choiType_cyclic_reciprocal_one_of_nonneg (hd : 2 ≤ d) (x : ZMod d → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i / (((d : ℝ) - 1) * x i + x (i - 1)) ≤ 1 := by
  classical
  by_cases hpos : ∀ i, 0 < x i
  · exact choiType_cyclic_reciprocal_one_of_pos hd x hpos
  · push Not at hpos
    obtain ⟨i₀, hi₀⟩ := hpos
    have hxi₀ : x i₀ = 0 := le_antisymm hi₀ (hx i₀)
    let s : Finset (ZMod d) := Finset.univ.filter fun i => x i ≠ 0
    have hslt : s.card < d := by
      calc
        s.card < (Finset.univ : Finset (ZMod d)).card :=
          Finset.card_lt_card
            (Finset.filter_ssubset.2 ⟨i₀, Finset.mem_univ _, fun h => h hxi₀⟩)
        _ = d := ZMod.card d
    have hscard : s.card ≤ d - 1 := by omega
    have hd1pos : (0 : ℝ) < (d : ℝ) - 1 := by
      have h2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have hterm : ∀ i ∈ s,
        x i / (((d : ℝ) - 1) * x i + x (i - 1)) ≤ 1 / ((d : ℝ) - 1) := by
      intro i hi
      have hxi : 0 < x i := lt_of_le_of_ne (hx i) (Finset.mem_filter.1 hi).2.symm
      have hden : 0 < ((d : ℝ) - 1) * x i + x (i - 1) :=
        add_pos_of_pos_of_nonneg (mul_pos hd1pos hxi) (hx _)
      rw [div_le_div_iff₀ hden hd1pos]
      nlinarith [hx (i - 1)]
    calc
      ∑ i, x i / (((d : ℝ) - 1) * x i + x (i - 1)) =
          ∑ i ∈ s, x i / (((d : ℝ) - 1) * x i + x (i - 1)) := by
            rw [Finset.sum_subset (Finset.subset_univ s)]
            intro i _ hi
            simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            have hzero : x i = 0 := not_ne_iff.mp hi
            simp [hzero]
      _ ≤ ∑ _i ∈ s, 1 / ((d : ℝ) - 1) := Finset.sum_le_sum hterm
      _ = (s.card : ℝ) / ((d : ℝ) - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ((d : ℝ) - 1) / ((d : ℝ) - 1) := by
        rw [div_le_div_iff_of_pos_right hd1pos]
        have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
          norm_num [Nat.cast_sub (by omega : 1 ≤ d)]
        rw [← hcast]
        exact_mod_cast hscard
      _ = 1 := div_self hd1pos.ne'

/-- **Wolf Chapter 3, Example 3.1, equation (3.20), case `n = 1`.**  The
rank-one diagonal weight is
\(a_i=(d-1)|v_i|^2+|v_{i-1}|^2\). -/
theorem choiTypeRankOneWeight_one (v : ZMod d → ℂ) (i : ZMod d) :
    choiTypeRankOneWeight d 1 v i =
      ((d : ℝ) - 1) * ‖v i‖ ^ 2 + ‖v (i - 1)‖ ^ 2 := by
  simp [choiTypeRankOneWeight]

/-- The reciprocal sum of the rank-one diagonal weights is at most one for
the bottom slice `n = 1` of Wolf's range. -/
theorem choiTypeRankOneWeight_reciprocal_sum_one (hd : 2 ≤ d) (v : ZMod d → ℂ) :
    ∑ i, ‖v i‖ ^ 2 / choiTypeRankOneWeight d 1 v i ≤ 1 := by
  simp_rw [choiTypeRankOneWeight_one]
  exact choiType_cyclic_reciprocal_one_of_nonneg hd (fun i => ‖v i‖ ^ 2)
    fun i => sq_nonneg _

/-- Rank-one positivity for the Choi-type map at the bottom of Wolf's range:
for `3 ≤ d`, the image \(T_C(|v\rangle\langle v|)\) with `n = 1` is
positive semidefinite (Wolf Chapter 3, Example 3.1, equation (3.20), ch03
lines 357–365). -/
theorem choiTypeMap_vecMulVec_posSemidef_one (hd : 3 ≤ d) (v : ZMod d → ℂ) :
    (choiTypeMap d 1 (vecMulVec v (star v))).PosSemidef := by
  refine choiTypeMap_vecMulVec_posSemidef_of_weight_sum_le_one 1 v (by omega) ?_
  exact choiTypeRankOneWeight_reciprocal_sum_one (by omega) v

/-- **Wolf Chapter 3, Example 3.1, equation (3.20), case `n = 1`.**  For
`3 ≤ d`, the first Choi-type map sends every positive semidefinite matrix to a
positive semidefinite matrix.

**Scope restriction:** See
`docs/paper-gaps/wolf_ex3_1_choi_positivity_subcase_scope.tex`.  This proves
the complete bottom slice `n = 1` of Wolf's positivity assertion, including
boundary vectors.  The middle range `2 ≤ n ≤ d - 3` remains open. -/
theorem choiTypeMap_isPositiveMap_one (hd : 3 ≤ d) :
    IsPositiveMap (choiTypeMap d 1) :=
  isPositiveMap_of_forall_vecMulVec_posSemidef _ fun v =>
    choiTypeMap_vecMulVec_posSemidef_one hd v

end Matrix
