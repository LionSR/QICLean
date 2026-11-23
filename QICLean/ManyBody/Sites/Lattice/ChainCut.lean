/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Cut
import QICLean.ManyBody.Sites.Lattice.Chain

/-!
# Supports of range `R` crossing a cut of the chain

An interval `[a, b)` of the chain of `L` sites is cut at two positions at most, and a support of
range `R` split by the interval lies in one of the two windows of `2R` sites around the cut
positions. Hence at most `N_R = 2 · 2^{2R}` supports are split by any interval, their dimensions
are at most `q^{R + 1}` for local dimension `q`, and the cut budget of an interval is at most
`B_R = 1 + N_R log² (e q^{R + 1})`. For an arbitrary region `A`, a split support lies in a window
of `2R` sites about one of the boundary edges of `A`, so at most `2^{2R} |∂A|` supports are split.

The same counting gives the other bounds of this file: at most `2^{2R+1}` supports contain a
site, at most `(R + 1) 2^{2R+1}` meet a given support, at most two nearest-neighbour bonds
contain a site, and there are at most `2L` supports of range one.

The shells `[l - jR, r + jR)` of an interval are split by disjoint sets of supports of range
`R`: a support split by one shell lies in every later shell and misses every earlier one.

## Main definitions

* `ManyBody.chainCrossConst R` — the count `N_R = 2 · 2^{2R}`.
* `ManyBody.chainBudgetConst q R` — the budget `B_R = 1 + N_R log² (e q^{R + 1})`.

## Main results

* `ManyBody.card_crossingTerms_interval_le` — at most `N_R` supports are split by an interval.
* `ManyBody.card_crossingTerms_le_mul_card_boundaryEdges` — at most `2^{2R} |∂A|` supports are
  split by a region `A`.
* `ManyBody.cutLogBudget_interval_le` — the cut budget of an interval is at most `B_R`.
* `ManyBody.single_splitting_shells`, `ManyBody.not_splits_two_shells` — shells `R` apart are
  split by disjoint sets of supports.
* `ManyBody.ChainSupport.card_filter_mem_le`, `ManyBody.ChainSupport.card_filter_not_disjoint_le`
  — the supports containing a site and meeting a support.
* `ManyBody.exists_interval_subset_boundaryEdges_sdiff_ssubset` — a nonempty proper region
  contains an interval whose removal shrinks its boundary.
* `ManyBody.card_chainSupport_range_one_le` — at most `2L` supports of range one.

## References

* M. B. Hastings, *An area law for one-dimensional quantum systems*, arXiv:0705.2024v4,
  `law16.tex`, lines 82–91 (finite range).
* Two-dimensional area-law manuscript (September 24, 2026), Lemma 3.1 (`lem:tail`),
  `02-initial.tex`, lines 47–55 (the cut budget).
* I. Arad, Z. Landau, U. Vazirani and T. Vidick, arXiv:1602.08828v2,
  `def:hard-trunc`, lines 873–886 (the internal bonds of a region).
-/

namespace ManyBody

variable {L q R : ℕ}

/-! ### Supports inside a set of sites -/

namespace ChainSupport

/-- At most `2^{|W|}` supports lie in a set of sites `W`. -/
theorem card_filter_subset_le (W : Finset (Fin L)) :
    (Finset.univ.filter fun X : ChainSupport L R ↦ X.1 ⊆ W).card ≤ 2 ^ W.card := by
  rw [← Finset.card_powerset]
  exact Finset.card_le_card_of_injOn (fun X ↦ X.1)
    (fun X hX ↦ Finset.mem_powerset.mpr (Finset.mem_filter.mp hX).2)
    (fun X _ Y _ h ↦ Subtype.ext h)

/-- At most `2^n` supports lie in a set of at most `n` sites. -/
theorem card_filter_subset_le_pow_of_card_le {W : Finset (Fin L)} {n : ℕ}
    (hW : W.card ≤ n) :
    (Finset.univ.filter fun X : ChainSupport L R ↦ X.1 ⊆ W).card ≤ 2 ^ n :=
  (card_filter_subset_le W).trans (Nat.pow_le_pow_right (by norm_num) hW)

/-- At most `2^{2R+1}` supports of range `R` contain a given site.
Hastings, arXiv:0705.2024v4, `law16.tex`, lines 88–91 (finite range). -/
theorem card_filter_mem_le (x : Fin L) :
    (Finset.univ.filter fun X : ChainSupport L R ↦ x ∈ X.1).card ≤ 2 ^ (2 * R + 1) := by
  classical
  let W := interval L (x.val - R) (x.val + R + 1)
  have hcover : (Finset.univ.filter fun X : ChainSupport L R ↦ x ∈ X.1) ⊆
      Finset.univ.filter (fun X : ChainSupport L R ↦ X.1 ⊆ W) := by
    intro X hX
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy ↦ ?_⟩
    have hx := (Finset.mem_filter.mp hX).2
    have hxy := X.2.2 x hx y hy
    have hyx := X.2.2 y hy x hx
    rw [mem_interval]
    omega
  exact (Finset.card_le_card hcover).trans
    (card_filter_subset_le_pow_of_card_le ((card_interval_le _ _).trans (by omega)))

/-- At most `(R + 1) 2^{2R+1}` supports of range `R` meet a given support: each of its at most
`R + 1` sites lies in at most `2^{2R+1}` supports. -/
theorem card_filter_not_disjoint_le (S : Finset (ChainSupport L R)) (X : ChainSupport L R) :
    (S.filter fun Y ↦ ¬Disjoint Y.1 X.1).card ≤ (R + 1) * 2 ^ (2 * R + 1) := by
  classical
  have hcover : S.filter (fun Y ↦ ¬Disjoint Y.1 X.1) ⊆
      X.1.biUnion fun x ↦ Finset.univ.filter fun Y : ChainSupport L R ↦ x ∈ Y.1 := by
    intro Y hY
    obtain ⟨x, hxY, hxX⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hY).2
    exact Finset.mem_biUnion.mpr ⟨x, hxX, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxY⟩⟩
  calc (S.filter fun Y ↦ ¬Disjoint Y.1 X.1).card
      ≤ ∑ x ∈ X.1, (Finset.univ.filter fun Y : ChainSupport L R ↦ x ∈ Y.1).card :=
        (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ ≤ X.1.card * 2 ^ (2 * R + 1) := by
        simpa using Finset.sum_le_card_nsmul X.1 _ _ fun x _ ↦ card_filter_mem_le x
    _ ≤ (R + 1) * 2 ^ (2 * R + 1) := Nat.mul_le_mul_right _ X.2.card_le

/-- The dimension of a support of range `R` is at most `q^{R + 1}`. -/
theorem supportDim_le (hq : 1 ≤ q) (X : ChainSupport L R) :
    Entropy.supportDim (fun _ : Fin L ↦ q) X.1 ≤ q ^ (R + 1) := by
  rw [Entropy.supportDim, Finset.prod_const]
  exact Nat.pow_le_pow_right hq X.2.card_le

/-- The logarithmic size `log² (e d_X)` of a support of range `R` is at most
`log² (e q^{R + 1})`. -/
theorem log_sq_supportDim_le (hq : 1 ≤ q) (X : ChainSupport L R) :
    Real.log (Real.exp 1 * (Entropy.supportDim (fun _ : Fin L ↦ q) X.1 : ℝ)) ^ 2 ≤
      Real.log (Real.exp 1 * (q : ℝ) ^ (R + 1)) ^ 2 := by
  have h1 : (1 : ℝ) ≤ Entropy.supportDim (fun _ : Fin L ↦ q) X.1 := by
    exact_mod_cast one_le_supportDim_const hq X.1
  have h2 : (Entropy.supportDim (fun _ : Fin L ↦ q) X.1 : ℝ) ≤ (q : ℝ) ^ (R + 1) := by
    exact_mod_cast supportDim_le hq X
  have := Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le)
  have h0 : 0 ≤ Real.log (Real.exp 1 * (Entropy.supportDim (fun _ : Fin L ↦ q) X.1 : ℝ)) :=
    Real.log_nonneg (by nlinarith [Real.add_one_le_exp (1 : ℝ)])
  exact pow_le_pow_left₀ h0 this 2

end ChainSupport

open ChainSupport

/-! ### Supports split by an interval -/

/-- The number of supports of range `R` split by an interval: `N_R = 2 · 2^{2R}`, the subsets of
the two windows of `2R` sites around the cut positions. -/
def chainCrossConst (R : ℕ) : ℕ := 2 * 2 ^ (2 * R)

/-- **Split supports of an interval.** At most `N_R` supports of range `R` are split by any
interval of the chain. -/
theorem card_crossingTerms_interval_le (a b : ℕ) :
    (crossingTerms (fun X : ChainSupport L R ↦ X.1) (interval L a b)).card ≤
      chainCrossConst R := by
  classical
  have hcover : crossingTerms (fun X : ChainSupport L R ↦ X.1) (interval L a b) ⊆
      (Finset.univ.filter fun X : ChainSupport L R ↦ X.1 ⊆ interval L (a - R) (a + R)) ∪
        Finset.univ.filter fun X : ChainSupport L R ↦ X.1 ⊆ interval L (b - R) (b + R) := by
    intro X hX
    simp only [crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hX
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact X.2.subset_window_of_splits hX
  have hW : ∀ c : ℕ, (interval L (c - R) (c + R)).card ≤ 2 * R := fun c ↦
    (card_interval_le _ _).trans (by omega)
  calc _ ≤ _ := Finset.card_le_card hcover
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 ^ (2 * R) + 2 ^ (2 * R) :=
        Nat.add_le_add (card_filter_subset_le_pow_of_card_le (hW a))
          (card_filter_subset_le_pow_of_card_le (hW b))
    _ = chainCrossConst R := by rw [chainCrossConst]; ring

/-- The cut budget of an interval: `B_R = 1 + N_R log² (e q^{R + 1})`. -/
noncomputable def chainBudgetConst (q R : ℕ) : ℝ :=
  1 + (chainCrossConst R : ℝ) * Real.log (Real.exp 1 * (q : ℝ) ^ (R + 1)) ^ 2

/-- The cut budget constant is at least one. -/
theorem one_le_chainBudgetConst (q R : ℕ) : 1 ≤ chainBudgetConst q R :=
  le_add_of_nonneg_right (by positivity)

/-- For local dimension at least two, the interval cut budget is at most a coefficient
depending on the range times the square of the logarithm of the local dimension. -/
theorem chainBudgetConst_le_mul_log_sq (hq : 2 ≤ q) :
    chainBudgetConst q R ≤
      (chainBudgetConst 2 R / Real.log 2 ^ 2) * Real.log (q : ℝ) ^ 2 := by
  have ht : Real.log 2 ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hq)
  have hlog (d : ℝ) (hd : 0 < d) :
      Real.log (Real.exp 1 * d ^ (R + 1)) = 1 + (R + 1 : ℕ) * Real.log d := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (pow_ne_zero _ hd.ne'),
      Real.log_exp, Real.log_pow]
  simp only [chainBudgetConst, Nat.cast_ofNat,
    hlog (q : ℝ) (by exact_mod_cast (by omega : 0 < q)), hlog 2 (by norm_num)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos (Real.log_pos (by norm_num)))]
  have hcross : Real.log 2 * (1 + (R + 1 : ℕ) * Real.log (q : ℝ)) ≤
      Real.log (q : ℝ) * (1 + (R + 1 : ℕ) * Real.log 2) := by
    nlinarith only [ht]
  have hc : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ht0 : 0 ≤ Real.log (q : ℝ) := hc.trans ht
  have hs := pow_le_pow_left₀ (by positivity :
    0 ≤ Real.log 2 * (1 + (R + 1 : ℕ) * Real.log (q : ℝ))) hcross 2
  calc
    _ = Real.log 2 ^ 2 + (chainCrossConst R : ℝ) *
        (Real.log 2 * (1 + (R + 1 : ℕ) * Real.log (q : ℝ))) ^ 2 := by ring
    _ ≤ Real.log (q : ℝ) ^ 2 + (chainCrossConst R : ℝ) *
        (Real.log (q : ℝ) * (1 + (R + 1 : ℕ) * Real.log 2)) ^ 2 :=
      add_le_add (pow_le_pow_left₀ hc ht 2)
        (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
    _ = _ := by ring

/-- **The cut budget of an interval is bounded by a constant.** The cut budget
`ℬ = 1 + ∑_{i ∈ I×} log² (e d_i)` at an interval is at most `B_R`. -/
theorem cutLogBudget_interval_le (hq : 1 ≤ q) (a b : ℕ) :
    cutLogBudget (fun X : ChainSupport L R ↦ X.1) (fun _ ↦ q) (interval L a b) ≤
      chainBudgetConst q R := by
  refine (cutLogBudget_const_le hq fun X _ ↦ X.2.card_le).trans ?_
  have hcard : ((crossingTerms (fun X : ChainSupport L R ↦ X.1) (interval L a b)).card : ℝ) ≤
      chainCrossConst R := by
    exact_mod_cast card_crossingTerms_interval_le a b
  rw [chainBudgetConst]
  gcongr

/-! ### Shells of an interval -/

/-- **Single splitting of shells.** If a set of diameter at most `R` is split by the interval
`[l - jR, r + jR)`, every later interval of this form contains it, every earlier one is disjoint
from it, and no other one splits it. Radius zero and arbitrary endpoints are allowed. -/
theorem single_splitting_shells {Y : Finset (Fin L)}
    (hY : ∀ x ∈ Y, ∀ y ∈ Y, y.val ≤ x.val + R) {l r j : ℕ}
    (hsplit : (∃ v ∈ Y, v ∈ interval L (l - j * R) (r + j * R)) ∧
      ∃ v ∈ Y, v ∉ interval L (l - j * R) (r + j * R)) :
    (∀ i : ℕ, j < i → Y ⊆ interval L (l - i * R) (r + i * R)) ∧
      (∀ i : ℕ, i < j → Disjoint Y (interval L (l - i * R) (r + i * R))) ∧
      (∀ i : ℕ,
        ((∃ v ∈ Y, v ∈ interval L (l - i * R) (r + i * R)) ∧
          ∃ v ∈ Y, v ∉ interval L (l - i * R) (r + i * R)) → i = j) := by
  have hclose {d e : ℕ} (hde : d + R ≤ e) {x : Fin L}
      (hxY : x ∈ Y) (hx : x ∈ interval L (l - d) (r + d)) :
      Y ⊆ interval L (l - e) (r + e) := by
    intro y hy
    have hdist := And.intro (hY x hxY y hy) (hY y hy x hxY)
    rw [mem_interval] at hx ⊢
    omega
  have hlater : ∀ i : ℕ, j < i → Y ⊆ interval L (l - i * R) (r + i * R) := by
    intro i hji
    obtain ⟨x, hxY, hx⟩ := hsplit.1
    apply hclose ?_ hxY hx
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right R (Nat.succ_le_of_lt hji)
  have hearlier : ∀ i : ℕ, i < j →
      Disjoint Y (interval L (l - i * R) (r + i * R)) := by
    intro i hij
    refine Finset.disjoint_left.mpr (fun x hxY hx ↦ ?_)
    obtain ⟨y, hyY, hy⟩ := hsplit.2
    apply hy (hclose ?_ hxY hx hyY)
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right R (Nat.succ_le_of_lt hij)
  refine ⟨hlater, hearlier, ?_⟩
  intro i hi
  rcases lt_trichotomy i j with hij | hij | hji
  · obtain ⟨x, hxY, hx⟩ := hi.1
    exact False.elim (Finset.disjoint_left.mp (hearlier i hij) hxY hx)
  · exact hij
  · obtain ⟨x, hxY, hx⟩ := hi.2
    exact False.elim (hx (hlater i hji hxY))

/-- **Shells `R` apart are split by disjoint sets of supports.** No support of range `R` is split
by both the shell `[l - (j + 1) R, r + (j + 1) R)` and the shell
`[l - (j' + 1) R, r + (j' + 1) R)` with `j < j'`. -/
theorem not_splits_two_shells {X : Finset (Fin L)} (hX : IsChainSupport L R X) {l r j j' : ℕ}
    (hjj : j < j')
    (h₁ : (∃ v ∈ X, v ∈ interval L (l - (j + 1) * R) (r + (j + 1) * R)) ∧
      ∃ v ∈ X, v ∉ interval L (l - (j + 1) * R) (r + (j + 1) * R))
    (h₂ : (∃ v ∈ X, v ∈ interval L (l - (j' + 1) * R) (r + (j' + 1) * R)) ∧
      ∃ v ∈ X, v ∉ interval L (l - (j' + 1) * R) (r + (j' + 1) * R)) : False := by
  have heq := (single_splitting_shells hX.2 h₁).2.2 (j' + 1) h₂
  omega

/-! ### Supports split by an arbitrary region -/

/-- A prefix of the chain has at most one boundary edge, including the empty and whole-chain
cases. -/
theorem card_boundaryEdges_prefix_le (L k : ℕ) :
    (boundaryEdges L (interval L 0 k)).card ≤ 1 := by
  classical
  have hmem (u : ℕ) (hu : u < L) :
      (∃ i ∈ interval L 0 k, i.val = u) ↔ u < k := by
    constructor
    · rintro ⟨i, hi, hiu⟩
      have := (mem_interval.mp hi).2
      omega
    · intro huk
      exact ⟨⟨u, hu⟩, mem_interval.mpr ⟨Nat.zero_le _, huk⟩, rfl⟩
  have hcut (p : ℕ) (hp : p ∈ boundaryEdges L (interval L 0 k)) : p + 1 = k := by
    obtain ⟨hpL, hp⟩ := mem_boundaryEdges.mp hp
    rw [hmem p (by omega), hmem (p + 1) hpL] at hp
    omega
  apply Finset.card_le_one.mpr
  intro p hp r hr
  have hp' := hcut p hp
  have hr' := hcut r hr
  omega

/-- A nonempty proper region `A` of the chain contains a nonempty interval `I` (its leftmost
maximal run) such that the boundary of `A \ I` is a proper subset of the boundary of `A`: the
boundary edges of `A \ I` are boundary edges of `A`, and the edge leaving the right end of the
run (or the edge entering its left end, when the run reaches the end of the chain) is a
boundary edge of `A` alone. -/
theorem exists_interval_subset_boundaryEdges_sdiff_ssubset {A : Finset (Fin L)}
    (hne : A.Nonempty) (hA : A ≠ Finset.univ) :
    ∃ a b : ℕ, interval L a b ⊆ A ∧ (interval L a b).Nonempty ∧
      boundaryEdges L (A \ interval L a b) ⊂ boundaryEdges L A := by
  classical
  -- `l` is the least position of a site of `A`.
  obtain ⟨l, hlmem, hlmin⟩ : ∃ l ∈ A.image Fin.val, ∀ v ∈ A, l ≤ v.val :=
    ⟨_, Finset.min'_mem _ (hne.image _),
      fun v hv ↦ Finset.min'_le _ _ (Finset.mem_image_of_mem _ hv)⟩
  obtain ⟨a₀, ha₀A, ha₀⟩ := Finset.mem_image.mp hlmem
  have ha₀L := a₀.2
  -- `g` is the least position `≥ l` that is not the position of a site of `A`.
  have hex : ∃ p, l ≤ p ∧ ¬ ∃ v ∈ A, v.val = p :=
    ⟨L, by omega, fun ⟨v, _, hv⟩ ↦ by have := v.2; omega⟩
  obtain ⟨g, ⟨hlg, hgA⟩, hgL, hgmin⟩ : ∃ g, (l ≤ g ∧ ¬ ∃ v ∈ A, v.val = g) ∧ g ≤ L ∧
      ∀ p, l ≤ p → p < g → ∃ v ∈ A, v.val = p :=
    ⟨Nat.find hex, Nat.find_spec hex,
      Nat.find_min' hex ⟨by omega, fun ⟨v, _, hv⟩ ↦ by have := v.2; omega⟩,
      fun p hlp hpg ↦ by
        by_contra h
        exact Nat.find_min hex hpg ⟨hlp, h⟩⟩
  have hlg' : l < g := lt_of_le_of_ne hlg fun h ↦ hgA ⟨a₀, ha₀A, by omega⟩
  -- The run `I` is the interval `[l, g)`.
  have hIA : interval L l g ⊆ A := by
    intro v hv
    rw [mem_interval] at hv
    obtain ⟨w, hwA, hw⟩ := hgmin v.val hv.1 hv.2
    exact Fin.ext hw ▸ hwA
  have hIne : (interval L l g).Nonempty := ⟨a₀, by rw [mem_interval]; omega⟩
  -- Sites of `A` outside the run sit strictly beyond the gap position `g`.
  have hA' : ∀ v ∈ A \ interval L l g, g + 1 ≤ v.val := by
    intro v hv
    rw [Finset.mem_sdiff, mem_interval] at hv
    have h1 := hlmin v hv.1
    have h2 : v.val ≠ g := fun h ↦ hgA ⟨v, hv.1, h⟩
    omega
  have hnot : ∀ p, p ≤ g → ¬ ∃ i ∈ A \ interval L l g, i.val = p := by
    rintro p hp ⟨i, hi, rfl⟩
    have := hA' i hi
    omega
  refine ⟨l, g, hIA, hIne, ?_⟩
  rw [Finset.ssubset_iff_of_subset]
  · -- A boundary edge of `A` that is not a boundary edge of `A \ I`.
    by_cases hgL' : g < L
    · obtain ⟨b, hbA, hb⟩ := hgmin (g - 1) (by omega) (by omega)
      refine ⟨g - 1, ?_, ?_⟩
      · rw [mem_boundaryEdges]
        refine ⟨by omega, fun h ↦ hgA ?_⟩
        obtain ⟨i, hi, hi'⟩ := h.mp ⟨b, hbA, hb⟩
        exact ⟨i, hi, hi'.trans (Nat.sub_add_cancel (Nat.zero_lt_of_lt hlg'))⟩
      · rw [mem_boundaryEdges]
        rintro ⟨-, h⟩
        exact h (iff_of_false (hnot _ (by omega)) (hnot _ (by omega)))
    · -- The run reaches the end of the chain, so it does not start at position `0`.
      have hl0 : 0 < l := by
        by_contra hl0
        apply hA
        rw [Finset.eq_univ_iff_forall]
        intro v
        exact hIA (mem_interval.mpr ⟨by omega, by have := v.2; omega⟩)
      refine ⟨l - 1, ?_, ?_⟩
      · rw [mem_boundaryEdges]
        refine ⟨by omega, fun h ↦ ?_⟩
        obtain ⟨i, hi, hil⟩ := h.mpr ⟨a₀, ha₀A, by omega⟩
        have := hlmin i hi
        omega
      · rw [mem_boundaryEdges]
        rintro ⟨-, h⟩
        exact h (iff_of_false (hnot _ (by omega)) (hnot _ (by omega)))
  · -- Every boundary edge of `A \ I` is a boundary edge of `A`.
    have key : ∀ r, g ≤ r → ((∃ i ∈ A \ interval L l g, i.val = r) ↔ ∃ i ∈ A, i.val = r) := by
      intro r hr
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, (Finset.mem_sdiff.mp hi).1, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        refine ⟨i, Finset.mem_sdiff.mpr ⟨hi, fun hI ↦ ?_⟩, rfl⟩
        rw [mem_interval] at hI
        omega
    intro p hp
    rw [mem_boundaryEdges] at hp ⊢
    obtain ⟨hpL, hp⟩ := hp
    refine ⟨hpL, fun h ↦ hp ?_⟩
    by_cases hgp : g ≤ p
    · rw [key p hgp, key (p + 1) (by omega)]
      exact h
    · refine iff_of_false (hnot p (by omega)) ?_
      rintro ⟨i, hi, hi'⟩
      have := hA' i hi
      omega

/-- The number of supports of range `R` crossing a region is at most `2^{2R}` times the number
of its boundary edges. The region need not be an interval. -/
theorem card_crossingTerms_le_mul_card_boundaryEdges (L R : ℕ) (D : Finset (Fin L)) :
    (crossingTerms (fun X : ChainSupport L R ↦ X.1) D).card ≤
      2 ^ (2 * R) * (boundaryEdges L D).card := by
  classical
  let W (p : ℕ) := interval L (p + 1 - R) (p + 1 + R)
  let F (p : ℕ) := Finset.univ.filter (fun X : ChainSupport L R ↦ X.1 ⊆ W p)
  have hcover : crossingTerms (fun X : ChainSupport L R ↦ X.1) D ⊆
      (boundaryEdges L D).biUnion F := by
    intro X hX
    simp only [crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hX
    obtain ⟨p, hp, hsub⟩ := X.2.exists_boundary_window_of_split hX
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub⟩⟩
  have hcard (p : ℕ) : (F p).card ≤ 2 ^ (2 * R) :=
    card_filter_subset_le_pow_of_card_le
      ((card_interval_le _ _).trans (by omega))
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_biUnion_le_card_mul (boundaryEdges L D) F (2 ^ (2 * R))
      (fun p _ ↦ hcard p)).trans_eq (Nat.mul_comm _ _))

/-! ### Nearest-neighbour bonds -/

/-- An internal nearest-neighbour bond `[i, i + 2)` with `lo ≤ i` and `i + 1 < hi` lies in the
interval `[lo, hi)`. Arad–Landau–Vazirani–Vidick, arXiv:1602.08828v2, `def:hard-trunc`,
lines 873–886. -/
theorem internal_bond_support_subset {lo hi : ℕ} {i : Fin (L - 1)}
    (hmem : i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun j ↦ lo ≤ j.val ∧ j.val + 1 < hi)) :
    interval L i.val (i.val + 2) ⊆ interval L lo hi := by
  have hiRange := (Finset.mem_filter.mp hmem).2
  intro v hv
  simp only [mem_interval] at hv ⊢
  omega

/-- At most `hi - lo - 1` nearest-neighbour bonds are internal to the interval `[lo, hi)`;
empty and out-of-range intervals are included. -/
theorem card_internal_bonds_le (L lo hi : ℕ) :
    ((Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ lo ≤ i.val ∧ i.val + 1 < hi)).card ≤ hi - lo - 1 := by
  let I := (Finset.univ : Finset (Fin (L - 1))).filter
    (fun i ↦ lo ≤ i.val ∧ i.val + 1 < hi)
  have hmap : Set.MapsTo Fin.val (I : Set (Fin (L - 1)))
      (Finset.Ico lo (hi - 1) : Set ℕ) := by
    intro i hiI
    have hiRange := (Finset.mem_filter.mp hiI).2
    apply Finset.mem_Ico.mpr
    constructor
    · exact hiRange.1
    · omega
  have hcard : I.card ≤ (Finset.Ico lo (hi - 1)).card :=
    Finset.card_le_card_of_injOn Fin.val hmap (by
      intro i _ j _ hij
      exact Fin.ext hij)
  rw [Nat.card_Ico] at hcard
  change I.card ≤ hi - lo - 1
  omega

/-- Every site of the chain lies in at most two of the nearest-neighbour bonds of a set. -/
theorem card_filter_mem_bond_le_two (s : Finset (Fin (L - 1))) (x : Fin L) :
    (s.filter fun i ↦ x ∈ interval L i.val (i.val + 2)).card ≤ 2 := by
  classical
  apply (Finset.card_le_card_of_injOn (fun i : Fin (L - 1) ↦ i.val)
    (t := {x.val - 1, x.val}) ?_ Fin.val_injective.injOn).trans Finset.card_le_two
  intro i hi
  have hx := mem_interval.mp (Finset.mem_filter.mp hi).2
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  omega

/-! ### Supports of range one -/

/-- A range-one support is the interval starting at its least site, with length equal to its
cardinality, which is one or two. -/
private theorem chainSupport_range_one_eq_interval (X : ChainSupport L 1) :
    X.1 = interval L (X.1.min' X.2.1).val ((X.1.min' X.2.1).val + X.1.card) := by
  classical
  by_cases hone : X.1.card = 1
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
    simp only [hx, Finset.min'_singleton, Finset.card_singleton]
    ext i
    simp only [Finset.mem_singleton, mem_interval]
    constructor
    · rintro rfl
      omega
    · intro hi
      exact Fin.ext (by omega)
  · have htwo : X.1.card = 2 := by
      have := X.2.card_le
      have := X.2.1.card_pos
      omega
    obtain ⟨a, ha, hXa⟩ := X.2.exists_eq_interval_of_card_eq htwo
    have haX : (⟨a, by omega⟩ : Fin L) ∈ X.1 := by
      rw [hXa]
      simp only [mem_interval]
      omega
    have hmX := X.1.min'_mem X.2.1
    have hmval : (X.1.min' X.2.1).val = a := by
      have hlow := (mem_interval.mp ((Finset.ext_iff.mp hXa _).mp hmX)).1
      have hupp := Finset.min'_le X.1 _ haX
      change (X.1.min' X.2.1).val ≤ a at hupp
      omega
    simpa only [hmval, htwo, Nat.add_assoc] using hXa

/-- A chain of `L` sites has at most `2L` nonempty supports of diameter at most one. -/
theorem card_chainSupport_range_one_le (L : ℕ) : Fintype.card (ChainSupport L 1) ≤ 2 * L := by
  classical
  let f : ChainSupport L 1 → Fin L × Fin 2 := fun X ↦
    (X.1.min' X.2.1, ⟨X.1.card - 1, by have := X.2.card_le; omega⟩)
  have hf : Function.Injective f := by
    intro X Y h
    have hm := congrArg Prod.fst h
    have hc := congrArg (fun p ↦ p.2.val) h
    change X.1.min' X.2.1 = Y.1.min' Y.2.1 at hm
    change X.1.card - 1 = Y.1.card - 1 at hc
    have hcard : X.1.card = Y.1.card := by
      have := X.2.1.card_pos
      have := Y.2.1.card_pos
      omega
    apply Subtype.ext
    rw [chainSupport_range_one_eq_interval X, chainSupport_range_one_eq_interval Y, hm, hcard]
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective f hf

end ManyBody
