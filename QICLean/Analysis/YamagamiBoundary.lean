/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Yamagami's singular-boundary estimate

This file isolates the omitted simultaneous-singularity step in Shigeru
Yamagami's proof of the cyclic inequalities.  We retain Yamagami's forward
cyclic indexing.  Thus
\[
  f_{N,m,s}(x)=\sum_j
    \frac{x_j}{(s-m)x_j+x_{j+1}+\cdots+x_{j+m}}.
\]

For the case called `l = 1` in the paper, a singular denominator gives a run
of at least `m + 1` zero coordinates.  Starting at the first positive
coordinate after this run, the preceding `m` summands tend to zero along
strictly positive approximants.  Every other summand is at most
`1 / (s - m)`.  The resulting single global count is
`(N - m) / (s - m) ≤ N / s`; no decomposition into maximal zero blocks is
used.

The last theorem is deliberately conditional on the strictly positive
inequality.  It only transfers such an inequality to Lean's totalized
nonnegative value, where `0 / 0 = 0`; it does not establish the strictly
positive theorem or the regular-boundary induction.

## Source

* S. Yamagami, *Cyclic inequalities*, Proc. Amer. Math. Soc. 118 (1993),
  521--527, especially the singular-boundary paragraph on pp. 524--525.
-/

open scoped BigOperators Topology
open Filter Finset

namespace Yamagami

section FiniteEstimate

variable {α ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite limsup estimate separating the terms that tend to zero from the
uniformly bounded terms.  This is the analytic form of Yamagami's global
count at a singular boundary point. -/
theorem limsup_sum_le_card_mul_of_tendsto_zero_on
    {l : Filter α} [NeBot l] (u : α → ι → ℝ) (V : Finset ι) (c : ℝ)
    (hzero : ∀ i ∈ V, Tendsto (fun t ↦ u t i) l (𝓝 0))
    (hnonneg : ∀ᶠ t in l, ∀ i, 0 ≤ u t i)
    (hle : ∀ᶠ t in l, ∀ i ∉ V, u t i ≤ c) :
    limsup (fun t ↦ ∑ i, u t i) l ≤ (((Finset.univ \ V).card : ℕ) : ℝ) * c := by
  have hzeroSum : Tendsto (fun t ↦ ∑ i ∈ V, u t i) l (𝓝 0) := by
    simpa using tendsto_finsetSum V hzero
  have hcomplement : ∀ᶠ t in l,
      (∑ i ∈ Finset.univ \ V, u t i) ≤ (((Finset.univ \ V).card : ℕ) : ℝ) * c := by
    filter_upwards [hle] with t ht
    simpa [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul (Finset.univ \ V) (u t) c fun i hi ↦
        ht i (Finset.mem_sdiff.mp hi).2)
  have hsplit : ∀ t,
      (∑ i, u t i) = (∑ i ∈ V, u t i) + ∑ i ∈ Finset.univ \ V, u t i := by
    intro t
    rw [← Finset.sum_sdiff V.subset_univ, add_comm]
  have hbelow : IsCoboundedUnder (· ≤ ·) l (fun t ↦ ∑ i, u t i) :=
    isCoboundedUnder_le_of_eventually_le l
      (hnonneg.mono fun t ht ↦ Finset.sum_nonneg fun i _ ↦ ht i)
  have habove : IsBoundedUnder (· ≤ ·) l (fun t ↦ ∑ i, u t i) := by
    refine isBoundedUnder_of_eventually_le
      (a := 1 + (((Finset.univ \ V).card : ℕ) : ℝ) * c) ?_
    filter_upwards [(tendsto_order.1 hzeroSum).2 1 zero_lt_one, hcomplement]
      with t hsmall hrest
    rw [hsplit]
    linarith
  rw [limsup_le_iff hbelow habove]
  intro y hy
  filter_upwards [
      (tendsto_order.1 hzeroSum).2
        (y - (((Finset.univ \ V).card : ℕ) : ℝ) * c) (sub_pos.mpr hy),
      hcomplement] with t hsmall hrest
  rw [hsplit]
  linarith

end FiniteEstimate

section OneStepCyclicFunction

variable {N : ℕ} [NeZero N]

/-- The denominator of Yamagami's `f_{N,m,s}` for the case `l = 1`, with
the forward cyclic window used in the paper. -/
def fnmsDenominator (m : ℕ) (s : ℝ) (x : ZMod N → ℝ) (i : ZMod N) : ℝ :=
  (s - (m : ℝ)) * x i + ∑ k ∈ Finset.Icc 1 m, x (i + (k : ZMod N))

/-- One summand of Yamagami's `f_{N,m,s}`. -/
noncomputable def fnmsTerm (m : ℕ) (s : ℝ) (x : ZMod N → ℝ) (i : ZMod N) : ℝ :=
  x i / fnmsDenominator m s x i

/-- Yamagami's `f_{N,m,s}` for the case `l = 1`.  Division is Lean's
totalized real division, so a boundary term `0 / 0` has value zero. -/
noncomputable def fnms (m : ℕ) (s : ℝ) (x : ZMod N → ℝ) : ℝ :=
  ∑ i, fnmsTerm m s x i

/-- The `m` terms immediately preceding the first positive coordinate after
the zero run singled out in Yamagami's singular-boundary argument. -/
def precedingIndices (m : ℕ) (j : ZMod N) : Finset (ZMod N) :=
  (Finset.Icc 1 m).image fun k : ℕ ↦ j - (k : ZMod N)

/-- The exact zero-run witness noted in Yamagami's omitted
multiple-singularity sentence: `a_j > 0` and
`a_{j-m-1} = ... = a_{j-1} = 0`. -/
def HasSingularRun (m : ℕ) (a : ZMod N → ℝ) (j : ZMod N) : Prop :=
  0 < a j ∧ ∀ k ∈ Finset.Icc 1 (m + 1), a (j - (k : ZMod N)) = 0

/-- Starting from a zero forward window, choose the first positive coordinate
encountered after that window.  The preceding `m + 1` coordinates are zero.
This is the finite cyclic first-positive step used in Yamagami's
singular-boundary paragraph; it does not choose or decompose maximal zero
blocks. -/
theorem exists_hasSingularRun_of_zero_window
    (m : ℕ) (a : ZMod N → ℝ) (i : ZMod N)
    (ha : ∀ q, 0 ≤ a q) (hpos : ∃ q, 0 < a q)
    (hwindow : ∀ k ∈ Finset.Icc 0 m, a (i + (k : ZMod N)) = 0) :
    ∃ j, HasSingularRun m a j := by
  have hex : ∃ r : ℕ, 0 < a (i + ((m + 1 + r : ℕ) : ZMod N)) := by
    obtain ⟨q, hq⟩ := hpos
    let b : ZMod N := i + ((m + 1 : ℕ) : ZMod N)
    refine ⟨(q - b).val, ?_⟩
    convert hq using 1
    dsimp [b]
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
    abel_nf
  let r := Nat.find hex
  have hrpos : 0 < a (i + ((m + 1 + r : ℕ) : ZMod N)) := Nat.find_spec hex
  have hrmin : ∀ q < r, ¬ 0 < a (i + ((m + 1 + q : ℕ) : ZMod N)) := by
    intro q hqr hqpos
    exact (not_le_of_gt hqr) (Nat.find_min' hex hqpos)
  refine ⟨i + ((m + 1 + r : ℕ) : ZMod N), hrpos, ?_⟩
  intro k hk
  rw [Finset.mem_Icc] at hk
  by_cases hkr : k ≤ r
  · have hindex :
        i + ((m + 1 + r : ℕ) : ZMod N) - (k : ZMod N) =
          i + ((m + 1 + (r - k) : ℕ) : ZMod N) := by
      have hnat : m + 1 + r = (m + 1 + (r - k)) + k := by omega
      rw [hnat, Nat.cast_add]
      abel_nf
    rw [hindex]
    apply le_antisymm
    · exact le_of_not_gt (hrmin (r - k) (by omega))
    · exact ha _
  · have hindex :
        i + ((m + 1 + r : ℕ) : ZMod N) - (k : ZMod N) =
          i + (((m + 1 + r) - k : ℕ) : ZMod N) := by
      have hnat : m + 1 + r = (m + 1 + r - k) + k := by omega
      conv_lhs => rw [hnat, Nat.cast_add]
      abel_nf
    rw [hindex]
    apply hwindow
    rw [Finset.mem_Icc]
    omega

omit [NeZero N] in
/-- Before the cyclic indices wrap, the preceding set has exactly `m`
members.  This is the combinatorial count in the `l = 1` proof. -/
theorem card_precedingIndices (m : ℕ) (j : ZMod N) (hmN : m < N) :
    (precedingIndices m j).card = m := by
  unfold precedingIndices
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb hab
    have hcast : (a : ZMod N) = (b : ZMod N) := sub_right_inj.mp hab
    have haN : a < N := lt_of_le_of_lt (Finset.mem_Icc.mp ha).2 hmN
    have hbN : b < N := lt_of_le_of_lt (Finset.mem_Icc.mp hb).2 hmN
    have hval := congrArg ZMod.val hcast
    simpa [ZMod.val_natCast_of_lt haN, ZMod.val_natCast_of_lt hbN] using hval

omit [NeZero N] in
/-- Every one of the `m` preceding indices has zero boundary numerator, and
its forward denominator window contains the positive coordinate `j`. -/
theorem precedingIndices_zero_and_reaches
    (m : ℕ) (a : ZMod N → ℝ) (j i : ZMod N) (hrun : HasSingularRun m a j)
    (hi : i ∈ precedingIndices m j) :
    a i = 0 ∧ ∃ k ∈ Finset.Icc 1 m, i + (k : ZMod N) = j := by
  rw [precedingIndices, Finset.mem_image] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  constructor
  · apply hrun.2 k
    rw [Finset.mem_Icc] at hk ⊢
    omega
  · exact ⟨k, hk, by abel_nf⟩

omit [NeZero N] in
/-- At each of the `m` preceding indices, the limiting denominator is
strictly positive because its forward window contains `a_j > 0`. -/
theorem fnmsDenominator_pos_of_mem_preceding
    (m : ℕ) (s : ℝ) (a : ZMod N → ℝ) (j i : ZMod N)
    (ha : ∀ q, 0 ≤ a q) (hrun : HasSingularRun m a j)
    (hi : i ∈ precedingIndices m j) :
    0 < fnmsDenominator m s a i := by
  obtain ⟨hizero, k, hk, hik⟩ := precedingIndices_zero_and_reaches m a j i hrun hi
  rw [fnmsDenominator, hizero, mul_zero, zero_add]
  have hsingle : a j ≤ ∑ q ∈ Finset.Icc 1 m, a (i + (q : ZMod N)) := by
    rw [← hik]
    exact Finset.single_le_sum (s := Finset.Icc 1 m)
      (f := fun q : ℕ ↦ a (i + (q : ZMod N)))
      (fun q _ ↦ ha (i + (q : ZMod N))) hk
  exact hrun.1.trans_le hsingle

omit [NeZero N] in
/-- The cyclic denominator is continuous under coordinatewise convergence. -/
theorem tendsto_fnmsDenominator
    {α : Type*} {l : Filter α} (m : ℕ) (s : ℝ)
    (x : α → ZMod N → ℝ) (a : ZMod N → ℝ)
    (hx : Tendsto x l (𝓝 a)) (i : ZMod N) :
    Tendsto (fun t ↦ fnmsDenominator m s (x t) i) l
      (𝓝 (fnmsDenominator m s a i)) := by
  unfold fnmsDenominator
  exact (tendsto_const_nhds.mul ((tendsto_pi_nhds.1 hx) i)).add
    (tendsto_finsetSum (Finset.Icc 1 m) fun k _ ↦
      (tendsto_pi_nhds.1 hx) (i + (k : ZMod N)))

omit [NeZero N] in
/-- A nonsingular cyclic summand is continuous under coordinatewise
convergence. -/
theorem tendsto_fnmsTerm_of_denominator_ne
    {α : Type*} {l : Filter α} (m : ℕ) (s : ℝ)
    (x : α → ZMod N → ℝ) (a : ZMod N → ℝ)
    (hx : Tendsto x l (𝓝 a)) (i : ZMod N)
    (hi : fnmsDenominator m s a i ≠ 0) :
    Tendsto (fun t ↦ fnmsTerm m s (x t) i) l (𝓝 (fnmsTerm m s a i)) := by
  have hquot :=
    (tendsto_pi_nhds.1 hx i).div (tendsto_fnmsDenominator m s x a hx i) hi
  refine Tendsto.congr' ?_ hquot
  exact Eventually.of_forall fun _ ↦ rfl

omit [NeZero N] in
/-- The `m` source-designated summands tend to zero along any approximating
filter.  Their numerators tend to zero and their limiting denominators contain
the fixed positive coordinate `a_j`. -/
theorem tendsto_fnmsTerm_zero_of_mem_preceding
    {α : Type*} {l : Filter α} (m : ℕ) (s : ℝ)
    (x : α → ZMod N → ℝ) (a : ZMod N → ℝ) (j i : ZMod N)
    (hx : Tendsto x l (𝓝 a)) (ha : ∀ q, 0 ≤ a q)
    (hrun : HasSingularRun m a j) (hi : i ∈ precedingIndices m j) :
    Tendsto (fun t ↦ fnmsTerm m s (x t) i) l (𝓝 0) := by
  have hizero := (precedingIndices_zero_and_reaches m a j i hrun hi).1
  have hdenom := fnmsDenominator_pos_of_mem_preceding m s a j i ha hrun hi
  have hquot :=
    (tendsto_pi_nhds.1 hx i).div (tendsto_fnmsDenominator m s x a hx i) hdenom.ne'
  have hquotZero : Tendsto
      ((fun t ↦ x t i) / fun t ↦ fnmsDenominator m s (x t) i) l (𝓝 0) := by
    simpa [hizero] using hquot
  refine Tendsto.congr' ?_ hquotZero
  exact Eventually.of_forall fun _ ↦ rfl

omit [NeZero N] in
/-- On the strictly positive cone, every summand is nonnegative and is at
most the common source coefficient `1 / (s - m)`. -/
theorem fnmsTerm_nonneg_and_le
    (m : ℕ) (s : ℝ) (x : ZMod N → ℝ) (hs : (m : ℝ) < s)
    (hx : ∀ q, 0 < x q) (i : ZMod N) :
    0 ≤ fnmsTerm m s x i ∧ fnmsTerm m s x i ≤ 1 / (s - (m : ℝ)) := by
  have hc : 0 < s - (m : ℝ) := sub_pos.mpr hs
  have hsum : 0 ≤ ∑ k ∈ Finset.Icc 1 m, x (i + (k : ZMod N)) :=
    Finset.sum_nonneg fun k _ ↦ (hx (i + (k : ZMod N))).le
  have hdenom : 0 < fnmsDenominator m s x i := by
    unfold fnmsDenominator
    exact add_pos_of_pos_of_nonneg (mul_pos hc (hx i)) hsum
  constructor
  · exact div_nonneg (hx i).le hdenom.le
  · have hbase : (s - (m : ℝ)) * x i ≤ fnmsDenominator m s x i := by
      unfold fnmsDenominator
      exact le_add_of_nonneg_right hsum
    calc
      fnmsTerm m s x i = x i / fnmsDenominator m s x i := rfl
      _ ≤ x i / ((s - (m : ℝ)) * x i) :=
        div_le_div_of_nonneg_left (hx i).le (mul_pos hc (hx i)) hbase
      _ = 1 / (s - (m : ℝ)) := by
        field_simp [hc.ne', (hx i).ne']

omit [NeZero N] in
/-- With nonnegative coordinates and `s > m`, a zero cyclic denominator has
zero numerator.  Hence its totalized boundary summand is `0 / 0 = 0`. -/
theorem eq_zero_of_fnmsDenominator_eq_zero
    (m : ℕ) (s : ℝ) (x : ZMod N → ℝ) (hs : (m : ℝ) < s)
    (hx : ∀ q, 0 ≤ x q) (i : ZMod N)
    (hi : fnmsDenominator m s x i = 0) : x i = 0 := by
  by_contra hxi
  have hxipos : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hxi)
  have hsum : 0 ≤ ∑ k ∈ Finset.Icc 1 m, x (i + (k : ZMod N)) :=
    Finset.sum_nonneg fun k _ ↦ hx (i + (k : ZMod N))
  have hdenom : 0 < fnmsDenominator m s x i := by
    unfold fnmsDenominator
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hs) hxipos) hsum
  exact hdenom.ne' hi

omit [NeZero N] in
/-- A singular denominator is exactly a zero numerator followed by `m` zero
coordinates.  This records the `m + 1` consecutive zeros from which
Yamagami begins the singular-boundary count. -/
theorem fnmsDenominator_eq_zero_iff
    (m : ℕ) (s : ℝ) (x : ZMod N → ℝ) (hs : (m : ℝ) < s)
    (hx : ∀ q, 0 ≤ x q) (i : ZMod N) :
    fnmsDenominator m s x i = 0 ↔
      x i = 0 ∧ ∀ k ∈ Finset.Icc 1 m, x (i + (k : ZMod N)) = 0 := by
  constructor
  · intro hi
    have hxi := eq_zero_of_fnmsDenominator_eq_zero m s x hs hx i hi
    refine ⟨hxi, ?_⟩
    have hsum : (∑ k ∈ Finset.Icc 1 m, x (i + (k : ZMod N))) = 0 := by
      simpa [fnmsDenominator, hxi] using hi
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.Icc 1 m) (f := fun k : ℕ ↦ x (i + (k : ZMod N)))
      (fun k _ ↦ hx (i + (k : ZMod N)))).mp hsum
  · rintro ⟨hxi, hwindow⟩
    rw [fnmsDenominator, hxi, mul_zero, zero_add]
    exact Finset.sum_eq_zero hwindow

/-- A singular denominator in a nonzero nonnegative vector supplies the
zero run singled out in Yamagami's simultaneous-singularity sentence.  The
positive endpoint is the first positive coordinate encountered after the
denominator's zero forward window. -/
theorem exists_hasSingularRun_of_fnmsDenominator_eq_zero
    (m : ℕ) (s : ℝ) (a : ZMod N → ℝ) (i : ZMod N)
    (hs : (m : ℝ) < s) (ha : ∀ q, 0 ≤ a q) (hne : a ≠ 0)
    (hi : fnmsDenominator m s a i = 0) :
    ∃ j, HasSingularRun m a j := by
  apply exists_hasSingularRun_of_zero_window m a i ha
  · by_contra hpos
    apply hne
    funext q
    apply le_antisymm
    · exact not_lt.mp (fun hq ↦ hpos ⟨q, hq⟩)
    · exact ha q
  · obtain ⟨hai, hforward⟩ :=
      (fnmsDenominator_eq_zero_iff m s a hs ha i).mp hi
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_cases hk0 : k = 0
    · simpa [hk0] using hai
    · exact hforward k (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hk0, hk.2⟩)

/-- Yamagami's omitted simultaneous-singularity estimate for `l = 1`.
The one source-designated zero run supplies all `m` vanishing summands at
once, and the complement has `N - m` terms. -/
theorem limsup_fnms_le_sub_ratio_of_singularRun
    {α : Type*} {l : Filter α} [NeBot l]
    (m : ℕ) (s : ℝ) (x : α → ZMod N → ℝ) (a : ZMod N → ℝ) (j : ZMod N)
    (hmN : m < N) (hs : (m : ℝ) < s)
    (hx : Tendsto x l (𝓝 a)) (hxpos : ∀ᶠ t in l, ∀ i, 0 < x t i)
    (ha : ∀ i, 0 ≤ a i) (hrun : HasSingularRun m a j) :
    limsup (fun t ↦ fnms m s (x t)) l ≤
      ((N - m : ℕ) : ℝ) / (s - (m : ℝ)) := by
  have hcard : (Finset.univ \ precedingIndices m j).card = N - m := by
    rw [Finset.card_sdiff_of_subset (precedingIndices m j).subset_univ, Finset.card_univ,
      ZMod.card, card_precedingIndices m j hmN]
  have hlim := limsup_sum_le_card_mul_of_tendsto_zero_on
    (u := fun t i ↦ fnmsTerm m s (x t) i) (V := precedingIndices m j)
    (c := 1 / (s - (m : ℝ)))
    (fun i hi ↦ tendsto_fnmsTerm_zero_of_mem_preceding m s x a j i hx ha hrun hi)
    (hxpos.mono fun t ht i ↦ (fnmsTerm_nonneg_and_le m s (x t) hs ht i).1)
    (hxpos.mono fun t ht i _ ↦ (fnmsTerm_nonneg_and_le m s (x t) hs ht i).2)
  simpa [fnms, hcard, div_eq_mul_inv] using hlim

/-- Yamagami's singular-boundary estimate stated from the boundary condition
itself: at least one denominator vanishes in a nonzero nonnegative vector.
The first-positive lemma constructs the source-designated zero run, after
which the global `N - m` count applies. -/
theorem limsup_fnms_le_sub_ratio_of_singularDenominator
    {α : Type*} {l : Filter α} [NeBot l]
    (m : ℕ) (s : ℝ) (x : α → ZMod N → ℝ) (a : ZMod N → ℝ)
    (hmN : m < N) (hs : (m : ℝ) < s)
    (hx : Tendsto x l (𝓝 a)) (hxpos : ∀ᶠ t in l, ∀ i, 0 < x t i)
    (ha : ∀ i, 0 ≤ a i) (hne : a ≠ 0)
    (hsingular : ∃ i, fnmsDenominator m s a i = 0) :
    limsup (fun t ↦ fnms m s (x t)) l ≤
      ((N - m : ℕ) : ℝ) / (s - (m : ℝ)) := by
  obtain ⟨i, hi⟩ := hsingular
  obtain ⟨j, hrun⟩ :=
    exists_hasSingularRun_of_fnmsDenominator_eq_zero m s a i hs ha hne hi
  exact limsup_fnms_le_sub_ratio_of_singularRun m s x a j hmN hs hx hxpos ha hrun

omit [NeZero N] in
/-- The elementary comparison displayed by Yamagami:
`(N - m) / (s - m) ≤ N / s` when `N ≤ s`. -/
theorem sub_ratio_le_card_ratio
    (m N : ℕ) (s : ℝ) (hmN : m < N) (hs : (m : ℝ) < s)
    (hNs : (N : ℝ) ≤ s) :
    ((N - m : ℕ) : ℝ) / (s - (m : ℝ)) ≤ (N : ℝ) / s := by
  have hc : 0 < s - (m : ℝ) := sub_pos.mpr hs
  have hspos : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg m) hs
  rw [div_le_div_iff₀ hc hspos, Nat.cast_sub (Nat.le_of_lt hmN)]
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

/-- The singular-boundary limsup is at most the interior value `N / s`.
This is equation (5) of Yamagami's proof, with the suppressed simultaneous
`0 / 0` case supplied by `limsup_fnms_le_sub_ratio_of_singularRun`. -/
theorem limsup_fnms_le_card_ratio_of_singularRun
    {α : Type*} {l : Filter α} [NeBot l]
    (m : ℕ) (s : ℝ) (x : α → ZMod N → ℝ) (a : ZMod N → ℝ) (j : ZMod N)
    (hmN : m < N) (hs : (m : ℝ) < s) (hNs : (N : ℝ) ≤ s)
    (hx : Tendsto x l (𝓝 a)) (hxpos : ∀ᶠ t in l, ∀ i, 0 < x t i)
    (ha : ∀ i, 0 ≤ a i) (hrun : HasSingularRun m a j) :
    limsup (fun t ↦ fnms m s (x t)) l ≤ (N : ℝ) / s :=
  (limsup_fnms_le_sub_ratio_of_singularRun m s x a j hmN hs hx hxpos ha hrun).trans
    (sub_ratio_le_card_ratio m N s hmN hs hNs)

/-- Equation (5) in Yamagami's singular-boundary case, including the
suppressed possibility of several vanishing denominators.  No zero-block
decomposition is used: one singular denominator and the first positive
coordinate after its window provide all `m` vanishing summands. -/
theorem limsup_fnms_le_card_ratio_of_singularDenominator
    {α : Type*} {l : Filter α} [NeBot l]
    (m : ℕ) (s : ℝ) (x : α → ZMod N → ℝ) (a : ZMod N → ℝ)
    (hmN : m < N) (hs : (m : ℝ) < s) (hNs : (N : ℝ) ≤ s)
    (hx : Tendsto x l (𝓝 a)) (hxpos : ∀ᶠ t in l, ∀ i, 0 < x t i)
    (ha : ∀ i, 0 ≤ a i) (hne : a ≠ 0)
    (hsingular : ∃ i, fnmsDenominator m s a i = 0) :
    limsup (fun t ↦ fnms m s (x t)) l ≤ (N : ℝ) / s :=
  (limsup_fnms_le_sub_ratio_of_singularDenominator
    m s x a hmN hs hx hxpos ha hne hsingular).trans
      (sub_ratio_le_card_ratio m N s hmN hs hNs)

/-- Conditional passage from an already established strictly positive
inequality to the repository's direct nonnegative value.  The proof uses the
uniform perturbation `x_i + 1 / (n + 1)`.  Nonsingular summands converge to
their boundary values, while the omitted singular summands are nonnegative;
Lean's totalized value of each omitted `0 / 0` term is zero.

This theorem does not prove the strictly positive inequality supplied as
`hpositive`. -/
theorem fnms_le_of_strictlyPositive
    (m : ℕ) (s B : ℝ) (x : ZMod N → ℝ) (hs : (m : ℝ) < s)
    (hx : ∀ i, 0 ≤ x i)
    (hpositive : ∀ y : ZMod N → ℝ, (∀ i, 0 < y i) → fnms m s y ≤ B) :
    fnms m s x ≤ B := by
  classical
  let R : Finset (ZMod N) :=
    Finset.univ.filter fun i ↦ fnmsDenominator m s x i ≠ 0
  have hregular : fnms m s x = ∑ i ∈ R, fnmsTerm m s x i := by
    rw [fnms, Finset.sum_subset (Finset.subset_univ R)]
    intro i _ hi
    have hdenom : fnmsDenominator m s x i = 0 := by
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact not_ne_iff.mp hi
    have hxi := eq_zero_of_fnmsDenominator_eq_zero m s x hs hx i hdenom
    simp [fnmsTerm, hxi, hdenom]
  let y : ℕ → ZMod N → ℝ := fun n i ↦ x i + 1 / ((n : ℝ) + 1)
  have hypos : ∀ n i, 0 < y n i := by
    intro n i
    exact add_pos_of_nonneg_of_pos (hx i) (one_div_pos.mpr (by positivity))
  have hytend : Tendsto y atTop (𝓝 x) := by
    apply tendsto_pi_nhds.2
    intro i
    simpa [y] using
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hregularTend :
      Tendsto (fun n ↦ ∑ i ∈ R, fnmsTerm m s (y n) i) atTop (𝓝 (fnms m s x)) := by
    rw [hregular]
    exact tendsto_finsetSum R fun i hi ↦
      tendsto_fnmsTerm_of_denominator_ne m s y x hytend i (Finset.mem_filter.mp hi).2
  have hregular_le : ∀ n, (∑ i ∈ R, fnmsTerm m s (y n) i) ≤ B := by
    intro n
    have hsubset : (∑ i ∈ R, fnmsTerm m s (y n) i) ≤ fnms m s (y n) := by
      rw [fnms]
      exact Finset.sum_le_sum_of_subset_of_nonneg R.subset_univ fun i _ _ ↦
        (fnmsTerm_nonneg_and_le m s (y n) hs (hypos n) i).1
    exact hsubset.trans (hpositive (y n) (hypos n))
  exact le_of_tendsto' hregularTend hregular_le

/-- The direct `0 / 0 = 0` nonnegative cyclic inequality, conditional only
on the corresponding strictly positive inequality. -/
theorem fnms_le_card_ratio_of_strictlyPositive
    (m : ℕ) (s : ℝ) (x : ZMod N → ℝ) (hs : (m : ℝ) < s)
    (hx : ∀ i, 0 ≤ x i)
    (hpositive : ∀ y : ZMod N → ℝ, (∀ i, 0 < y i) →
      fnms m s y ≤ (N : ℝ) / s) :
    fnms m s x ≤ (N : ℝ) / s :=
  fnms_le_of_strictlyPositive m s ((N : ℝ) / s) x hs hx hpositive

end OneStepCyclicFunction

end Yamagami
