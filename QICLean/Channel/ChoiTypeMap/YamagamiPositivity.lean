/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.YamagamiBoundary
import QICLean.Analysis.YamagamiCyclicMatrix
import QICLean.Analysis.YamagamiRegularBoundary
import QICLean.Channel.ChoiTypeMap.Positivity
import Mathlib.Topology.Sequences

/-!
# Yamagami's cyclic inequality at the cardinal parameter

This file proves the scalar cyclic inequality used in the middle range of
Wolf's Choi-type maps.  The argument follows Yamagami's variational route:
strong induction handles regular boundary points, the simultaneous-singularity
estimate excludes singular points from a compact superlevel closure, and the
Fourier--Hessian package together with the finite-coordinate Nowosad theorem
identifies the remaining positive maximizer.

## References

* S. Yamagami, *Cyclic inequalities*, Proc. Amer. Math. Soc. 118 (1993),
  521--527.
-/

open scoped BigOperators Matrix Topology
open Filter Finset Nowosad

namespace Yamagami

private theorem forwardDenominator_comp_add
    (N m : ℕ) [NeZero N] (s : ℝ) (x : ZMod N → ℝ) (a i : ZMod N) :
    forwardDenominator N m s (fun j ↦ x (j + a)) i =
      forwardDenominator N m s x (i + a) := by
  unfold forwardDenominator
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  abel_nf

private theorem functional_comp_add
    (N m : ℕ) [NeZero N] (s : ℝ) (x : ZMod N → ℝ) (a : ZMod N) :
    functional N m s (fun i ↦ x (i + a)) = functional N m s x := by
  unfold functional
  simp_rw [forwardDenominator_comp_add]
  exact Equiv.sum_comp (Equiv.addRight a)
    (fun i : ZMod N ↦ x i / forwardDenominator N m s x i)

private theorem tendsto_functional_of_denominators_ne
    {A : Type*} {l : Filter A} (N m : ℕ) [NeZero N] (s : ℝ)
    (x : A → ZMod N → ℝ) (a : ZMod N → ℝ)
    (hx : Tendsto x l (𝓝 a))
    (hden : ∀ i, forwardDenominator N m s a i ≠ 0) :
    Tendsto (fun t ↦ functional N m s (x t)) l
      (𝓝 (functional N m s a)) := by
  unfold functional
  exact tendsto_finsetSum Finset.univ fun i _ ↦
    tendsto_summand_of_denominator_ne m s x a hx i (hden i)

private theorem forwardDenominator_pos_of_positive
    (N m : ℕ) [NeZero N] (hmN : m < N) (x : ZMod N → ℝ)
    (hx : ∀ i, 0 < x i) (i : ZMod N) :
    0 < forwardDenominator N m (N : ℝ) x i := by
  have hcoeff : 0 < (N : ℝ) - (m : ℝ) := by
    have hmNR : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    linarith
  unfold forwardDenominator
  exact add_pos_of_pos_of_nonneg (mul_pos hcoeff (hx i))
    (Finset.sum_nonneg fun k _ ↦ (hx _).le)

private theorem continuousAt_functional_of_positive
    (N m : ℕ) [NeZero N] (hmN : m < N) (x : ZMod N → ℝ)
    (hx : ∀ i, 0 < x i) :
    ContinuousAt (functional N m (N : ℝ)) x := by
  exact tendsto_functional_of_denominators_ne N m (N : ℝ)
    id x tendsto_id fun i ↦ (forwardDenominator_pos_of_positive N m hmN x hx i).ne'

private theorem functional_le_uniformBound_of_positive
    (N m : ℕ) [NeZero N] (hmN : m < N) (x : ZMod N → ℝ)
    (hx : ∀ i, 0 < x i) :
    functional N m (N : ℝ) x ≤
      (N : ℝ) * (1 / ((N : ℝ) - (m : ℝ))) := by
  have hmNR : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
  unfold functional
  calc
    (∑ i : ZMod N, x i / forwardDenominator N m (N : ℝ) x i) ≤
        ∑ _i : ZMod N, 1 / ((N : ℝ) - (m : ℝ)) := by
      exact Finset.sum_le_sum fun i _ ↦
        (summand_nonneg_and_le m (N : ℝ) x hmNR hx i).2
    _ = (N : ℝ) * (1 / ((N : ℝ) - (m : ℝ))) := by
      simp [ZMod.card]

private theorem functional_card_le_one_one
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (x : ZMod N → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    functional N 1 (N : ℝ) x ≤ 1 := by
  let y : ZMod N → ℝ := fun i ↦ x (-i)
  have hy : ∀ i, 0 ≤ y i := fun i ↦ hx (-i)
  have horientation := functional_comp_neg N 1 (N : ℝ) y
  have hbound := Matrix.choiType_cyclic_reciprocal_one_of_nonneg hN y hy
  rw [show (fun i ↦ y (-i)) = x by
    funext i
    simp [y]] at horientation
  rw [horientation]
  simpa using hbound

private theorem functional_eq_one_of_isScalarVector
    (N m : ℕ) [NeZero N] (x : ZMod N → ℝ)
    (hx : ∀ i, 0 < x i) (hscalar : IsScalarVector x) :
    functional N m (N : ℝ) x = 1 := by
  obtain ⟨c, rfl⟩ := hscalar
  have hc : c ≠ 0 := by
    have hcpos := hx 0
    simpa using hcpos.ne'
  calc
    functional N m (N : ℝ) (c • (1 : ZMod N → ℝ)) =
        functional N m (N : ℝ) (fun i ↦ c * (1 : ZMod N → ℝ) i) := by
      rfl
    _ = functional N m (N : ℝ) (1 : ZMod N → ℝ) :=
      functional_mul N m (N : ℝ) c (1 : ZMod N → ℝ) hc
    _ = 1 := by
      change functional N m (N : ℝ) (fun _ ↦ 1) = 1
      rw [functional_one]
      exact div_self (Nat.cast_ne_zero.mpr (NeZero.ne N))

private theorem functional_card_le_one_of_has_zero
    (N m : ℕ) [NeZero N] (hN : 3 ≤ N) (hm : 2 ≤ m)
    (hmN : m ≤ N - 2) (x : ZMod N → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hzero : ∃ q, x q = 0)
    (hind : ∀ y : ZMod (N - 1) → ℝ, (∀ i, 0 ≤ y i) →
      @functional (N - 1) (m - 1) ⟨by omega⟩ (N - 1 : ℕ) y ≤ 1) :
    functional N m (N : ℝ) x ≤ 1 := by
  obtain ⟨q, hq⟩ := hzero
  let a : ZMod N := q - ((N - 1 : ℕ) : ZMod N)
  let y : ZMod N → ℝ := fun i ↦ x (i + a)
  have hy : ∀ i, 0 ≤ y i := fun i ↦ hx (i + a)
  have hlast : y ((N - 1 : ℕ) : ZMod N) = 0 := by
    simpa [y, a] using hq
  have hrecurrence := functional_le_deleteLastCoordinate
    N m hN hm hmN (N : ℝ) le_rfl y hy hlast
  have hdeleted : ∀ i, 0 ≤ deleteLastCoordinate N y i := fun i ↦ hy _
  have hcast : (N : ℝ) - 1 = ((N - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  calc
    functional N m (N : ℝ) x = functional N m (N : ℝ) y :=
      (functional_comp_add N m (N : ℝ) x a).symm
    _ ≤ @functional (N - 1) (m - 1) ⟨by omega⟩
        ((N - 1 : ℕ) : ℝ) (deleteLastCoordinate N y) := by
      simpa [hcast] using hrecurrence
    _ ≤ 1 := hind (deleteLastCoordinate N y) hdeleted

private theorem functional_card_le_one_of_positive
    (N m : ℕ) [NeZero N] (hN : 3 ≤ N) (hm₁ : 1 ≤ m)
    (hm₂ : m ≤ N - 2) (x : ZMod N → ℝ) (hx : ∀ i, 0 < x i)
    (hboundary : ∀ a : ZMod N → ℝ, (∀ i, 0 ≤ a i) →
      (∃ i, a i = 0) → functional N m (N : ℝ) a ≤ 1) :
    functional N m (N : ℝ) x ≤ 1 := by
  by_contra hle
  have hxValue : 1 < functional N m (N : ℝ) x := lt_of_not_ge hle
  have hxsum : 0 < ∑ i, x i :=
    Finset.sum_pos (fun i _ ↦ hx i) Finset.univ_nonempty
  let x₀ : ZMod N → ℝ := normalize N x
  have hx₀Simplex : x₀ ∈ stdSimplex ℝ (ZMod N) :=
    normalize_mem_stdSimplex N x (fun i ↦ (hx i).le) hxsum
  have hx₀Positive : x₀ ∈ positiveInvertibles := by
    rw [mem_positiveInvertibles]
    exact fun i ↦ div_pos (hx i) hxsum
  have hx₀Value :
      functional N m (N : ℝ) x₀ = functional N m (N : ℝ) x :=
    functional_normalize N m (N : ℝ) x hxsum.ne'
  let A : Set (ZMod N → ℝ) :=
    {y | y ∈ stdSimplex ℝ (ZMod N) ∧ y ∈ positiveInvertibles ∧
      functional N m (N : ℝ) x ≤ functional N m (N : ℝ) y}
  let K : Set (ZMod N → ℝ) := closure A
  have hx₀A : x₀ ∈ A := by
    exact ⟨hx₀Simplex, hx₀Positive, hx₀Value.ge⟩
  have hKNonempty : K.Nonempty := ⟨x₀, subset_closure hx₀A⟩
  have hKSimplex : K ⊆ stdSimplex ℝ (ZMod N) := by
    exact closure_minimal (fun y hy ↦ hy.1) (isClosed_stdSimplex ℝ (ZMod N))
  have hKCompact : IsCompact K :=
    (isCompact_stdSimplex ℝ (ZMod N)).of_isClosed_subset
      isClosed_closure hKSimplex
  have hmN : m < N := by omega
  have hmNR : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
  have hKPositive : K ⊆ positiveInvertibles := by
    intro a haK
    have haSimplex := hKSimplex haK
    rw [mem_positiveInvertibles]
    intro i
    have haiNonnegative : 0 ≤ a i := haSimplex.1 i
    by_contra hai
    have haiZero : a i = 0 :=
      le_antisymm (not_lt.mp hai) haiNonnegative
    have haSequence : a ∈ seqClosure A := by
      rw [seqClosure_eq_closure]
      exact haK
    obtain ⟨u, huA, huTendsto⟩ := haSequence
    have huPositive : ∀ n j, 0 < u n j := by
      intro n
      exact mem_positiveInvertibles.mp (huA n).2.1
    have huLevel : ∀ n,
        functional N m (N : ℝ) x ≤ functional N m (N : ℝ) (u n) :=
      fun n ↦ (huA n).2.2
    have haNonzero : a ≠ 0 := by
      intro haZero
      have hone : (0 : ℝ) = 1 := by
        simpa [haZero] using haSimplex.2
      norm_num at hone
    by_cases haSingular : ∃ j, forwardDenominator N m (N : ℝ) a j = 0
    · have hlimsup := limsup_functional_le_card_ratio_of_singularDenominator
        m (N : ℝ) u a hmN hmNR le_rfl huTendsto
          (Eventually.of_forall huPositive) haSimplex.1 haNonzero haSingular
      have hlimsupOne :
          limsup (fun n ↦ functional N m (N : ℝ) (u n)) atTop ≤ 1 := by
        have hNcast : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
        simpa [hNcast] using hlimsup
      have huBounded : IsBoundedUnder (· ≤ ·) atTop
          (fun n ↦ functional N m (N : ℝ) (u n)) :=
        Filter.isBoundedUnder_of_eventually_le <|
          Eventually.of_forall fun n ↦
            functional_le_uniformBound_of_positive N m hmN (u n) (huPositive n)
      have hxLimsup : functional N m (N : ℝ) x ≤
          limsup (fun n ↦ functional N m (N : ℝ) (u n)) atTop :=
        Filter.le_limsup_of_frequently_le
          (Eventually.frequently (Eventually.of_forall huLevel)) huBounded
      exact (not_lt_of_ge (hxLimsup.trans hlimsupOne)) hxValue
    · have haRegular : ∀ j, forwardDenominator N m (N : ℝ) a j ≠ 0 := by
        intro j hj
        exact haSingular ⟨j, hj⟩
      have hfunctionalTendsto := tendsto_functional_of_denominators_ne
        N m (N : ℝ) u a huTendsto haRegular
      have hxBoundary : functional N m (N : ℝ) x ≤
          functional N m (N : ℝ) a :=
        ge_of_tendsto' hfunctionalTendsto huLevel
      have haBound := hboundary a haSimplex.1 ⟨i, haiZero⟩
      exact (not_lt_of_ge (hxBoundary.trans haBound)) hxValue
  have hKContinuous : ContinuousOn (functional N m (N : ℝ)) K := by
    intro a haK
    exact (continuousAt_functional_of_positive N m hmN a
      (mem_positiveInvertibles.mp (hKPositive haK))).continuousWithinAt
  obtain ⟨b, hbK, hbMaximum⟩ :=
    hKCompact.exists_isMaxOn hKNonempty hKContinuous
  have hbPositive : b ∈ positiveInvertibles := hKPositive hbK
  have hxb : functional N m (N : ℝ) x ≤
      functional N m (N : ℝ) b := by
    calc
      functional N m (N : ℝ) x = functional N m (N : ℝ) x₀ :=
        hx₀Value.symm
      _ ≤ functional N m (N : ℝ) b :=
        isMaxOn_iff.mp hbMaximum x₀ (subset_closure hx₀A)
  have hbGlobal :
      IsMaxOn (functional N m (N : ℝ)) positiveInvertibles b := by
    rw [isMaxOn_iff]
    intro y hyPositive
    by_cases hyLevel : functional N m (N : ℝ) x ≤
        functional N m (N : ℝ) y
    · have hy : ∀ i, 0 < y i := mem_positiveInvertibles.mp hyPositive
      have hysum : 0 < ∑ i, y i :=
        Finset.sum_pos (fun i _ ↦ hy i) Finset.univ_nonempty
      have hyNormalizeSimplex : normalize N y ∈ stdSimplex ℝ (ZMod N) :=
        normalize_mem_stdSimplex N y (fun i ↦ (hy i).le) hysum
      have hyNormalizePositive : normalize N y ∈ positiveInvertibles := by
        rw [mem_positiveInvertibles]
        exact fun i ↦ div_pos (hy i) hysum
      have hyNormalizeValue : functional N m (N : ℝ) (normalize N y) =
          functional N m (N : ℝ) y :=
        functional_normalize N m (N : ℝ) y hysum.ne'
      have hyNormalizeA : normalize N y ∈ A :=
        ⟨hyNormalizeSimplex, hyNormalizePositive,
          hyLevel.trans hyNormalizeValue.ge⟩
      calc
        functional N m (N : ℝ) y =
            functional N m (N : ℝ) (normalize N y) := hyNormalizeValue.symm
        _ ≤ functional N m (N : ℝ) b :=
          isMaxOn_iff.mp hbMaximum _ (subset_closure hyNormalizeA)
    · exact (lt_of_not_ge hyLevel).le.trans hxb
  have hlocalFunctional :
      IsLocalMaxOn (functional N m (N : ℝ)) positiveInvertibles b :=
    (hbGlobal.isLocalMax
      (isOpen_positiveInvertibles.mem_nhds hbPositive)).on positiveInvertibles
  have hS := forwardMatrix_isUnit_det N m hN hm₁ hm₂ (N : ℝ) le_rfl
  have hlocalLambda : IsLocalMaxOn
      (fun z ↦ lambdaT (inverseOperator (forwardMatrix N m (N : ℝ)))
        (forwardMatrix N m (N : ℝ) *ᵥ z))
      positiveInvertibles b := by
    simpa only [← functional_eq_lambdaT_inverseOperator_mulVec N m
      (N : ℝ) hS] using hlocalFunctional
  have hbScalar : IsScalarVector b :=
    lemma_three_localMax_isScalar
      (forwardMatrix N m (N : ℝ)) (N : ℝ) b hS
      (forwardMatrix_nonnegative_of_sourceRange N m hm₂ (N : ℝ) le_rfl)
      (by exact_mod_cast (show 0 < N by omega))
      (forwardMatrix_mulVec_one N m (N : ℝ))
      (forwardMatrix_transpose_mulVec_one N m (N : ℝ))
      (hessianMatrix_forwardMatrix_posSemidef N m hN hm₁ hm₂ (N : ℝ) le_rfl)
      (fun z hz ↦
        (hessianMatrix_forwardMatrix_mulVec_eq_zero_iff_isScalarVector
          N m hN hm₁ hm₂ (N : ℝ) le_rfl z).mp hz)
      hbPositive hlocalLambda
  have hbValue : 1 < functional N m (N : ℝ) b := hxValue.trans_le hxb
  rw [functional_eq_one_of_isScalarVector N m b
    (mem_positiveInvertibles.mp hbPositive) hbScalar] at hbValue
  exact lt_irrefl 1 hbValue

/-- Yamagami's cyclic reciprocal inequality at the cardinal parameter.  In
the corrected middle range, every nonnegative cyclic vector satisfies
`f_{N,m,N}(x) ≤ 1`, with Lean's totalized value for singular summands. -/
theorem functional_card_le_one
    (N m : ℕ) [NeZero N] (hN : 3 ≤ N) (hm₁ : 1 ≤ m)
    (hm₂ : m ≤ N - 2) (x : ZMod N → ℝ) (hx : ∀ i, 0 ≤ x i) :
    functional N m (N : ℝ) x ≤ 1 := by
  suffices hAll :
      ∀ d : ℕ, (hd : 3 ≤ d) →
        let _ : NeZero d := ⟨by omega⟩
        ∀ k : ℕ, 1 ≤ k → k ≤ d - 2 → ∀ y : ZMod d → ℝ,
          (∀ i, 0 ≤ y i) → functional d k (d : ℝ) y ≤ 1 by
    exact hAll N hN m hm₁ hm₂ x hx
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro hd
      dsimp only
      let _ : NeZero d := ⟨by omega⟩
      intro k hk₁ hk₂ y hy
      by_cases hkOne : k = 1
      · subst k
        exact functional_card_le_one_one d (by omega) y hy
      · have hk : 2 ≤ k := by omega
        have hsmaller : ∀ z : ZMod (d - 1) → ℝ, (∀ i, 0 ≤ z i) →
            @functional (d - 1) (k - 1) ⟨by omega⟩
              (d - 1 : ℕ) z ≤ 1 := by
          intro z hz
          exact ih (d - 1) (by omega) (by omega) (k - 1)
            (by omega) (by omega) z hz
        by_cases hzero : ∃ i, y i = 0
        · exact functional_card_le_one_of_has_zero
            d k hd hk hk₂ y hy hzero hsmaller
        · have hyPositive : ∀ i, 0 < y i := by
            intro i
            exact lt_of_le_of_ne (hy i)
              (Ne.symm fun hi ↦ hzero ⟨i, hi⟩)
          apply functional_card_le_one_of_positive
            d k hd hk₁ hk₂ y hyPositive
          intro a ha haZero
          exact functional_card_le_one_of_has_zero
            d k hd hk hk₂ a ha haZero hsmaller

end Yamagami
