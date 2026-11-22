/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Plane
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Logic.Equiv.Fintype

/-!
# Counting interaction supports and their weights

There is one interaction term per finite support. A support containing a given site is
determined by deleting that site, so if every such support lies in a finite neighbourhood `B`
of the site there are at most `2^{|B| - 1}` of them, whatever the size of the whole system.
Nonnegative weights of the supports meeting a region are bounded by summing the budgets of its
sites, and the total weight of the chains of supports in which each support meets the previous
one is at most `κ^n` for chains of length `n`, with `κ = v b` for supports of at most `v` sites
and site budgets `b`. Repeated supports in a chain are allowed.

On a graph whose edges move lattice coordinates by at most one, a support of range `R` has at
most `v_R = 1 + 2 R (R + 1)` sites, and at most `μ_R = 2^{v_R - 1}` supports of range `R`
contain a given site; a term bound `J` then gives the site budget `μ_R J` and the chain bound
`(v_R μ_R J)^n`. On a finite domain of the square lattice, a support of range `R` meeting a
region `S` lies in the graph neighbourhood `N_R(S)`. Holes and several components are allowed;
no spectral gap, entropy or connectedness is used.

Moved from TNLean, `TNLean/Lattice/GraphInteractionBudget.lean`,
`TNLean/Lattice/GraphInteractionDiamondCounting.lean` and `TNLean/Lattice/FiniteDomain.lean`
(`card_configuration`, `subset_graphNeighborhood_of_isAdmissibleSupport`). Changes: namespace
`ManyBody` in place of `TNLean.PEPS.AreaLaw` and `TNLean.Lattice`; the sites of a domain are
written `↥Λ` and its configurations `↥Λ → Fin q`, without the abbreviations `Site Λ` and
`Configuration Λ q`.

## Main definitions

* `ManyBody.interactionChainWeightSum` — the total weight of the chains of supports of length
  `n` starting at a support.

## Main results

* `ManyBody.card_supportFamily_le_pow` — at most `2^{|B| - 1}` supports in `B` contain a site.
* `ManyBody.sum_supportWeights_meeting_le` — the weight of the supports meeting a region.
* `ManyBody.interactionChainWeightSum_le_pow` — the chain bound `κ^n`.
* `ManyBody.card_support_le_diamond`, `ManyBody.card_supports_containing_le_diamond` — the
  counts `v_R` and `μ_R`.
* `ManyBody.interactionChainWeightSum_le_diamond_pow` — the chain bound `(v_R μ_R J)^n`.
* `ManyBody.subset_graphNeighborhood_of_isAdmissibleSupport` — a support of range `R` meeting
  `S` lies in `N_R(S)`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Section 2, `01-preliminaries.tex`, `eq:ball-count` and the multiplicity bound after it, and
  Section 4, `03-quasilocal.tex`, `eq:quasilocal-budget`.
-/

open scoped BigOperators

namespace ManyBody

section Budget

variable {V : Type*} [DecidableEq V]

/-- Distinct supports containing a site give distinct subsets after that site is removed.
This is the support-counting argument in Section 2 of the area-law manuscript. -/
theorem card_supportFamily_le_pow_card_erase (F : Finset (Finset V)) (B : Finset V) (a : V)
    (hF : ∀ X ∈ F, a ∈ X ∧ X ⊆ B) : F.card ≤ 2 ^ (B.erase a).card := by
  have hinj : Set.InjOn (fun X : Finset V => X.erase a) F := by
    intro X hX Y hY hXY
    calc
      X = insert a (X.erase a) := (Finset.insert_erase (hF X hX).1).symm
      _ = insert a (Y.erase a) := congrArg (insert a) hXY
      _ = Y := Finset.insert_erase (hF Y hY).1
  have hsub : F.image (fun X => X.erase a) ⊆ (B.erase a).powerset := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
    apply Finset.mem_powerset.mpr
    intro x hx
    obtain ⟨hxa, hxY⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_erase.mpr ⟨hxa, (hF Y hY).2 hxY⟩
  calc
    F.card = (F.image (fun X => X.erase a)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (B.erase a).powerset.card := Finset.card_le_card hsub
    _ = 2 ^ (B.erase a).card := Finset.card_powerset _

omit [DecidableEq V] in
/-- At most $2^{|B|-1}$ supports in a neighborhood contain its specified site.
The neighborhood includes the site, so the exponent also covers singleton neighborhoods. -/
theorem card_supportFamily_le_pow (F : Finset (Finset V)) (B : Finset V) (a : V)
    (ha : a ∈ B) (hF : ∀ X ∈ F, a ∈ X ∧ X ⊆ B) :
    F.card ≤ 2 ^ (B.card - 1) := by
  classical
  simpa only [Finset.card_erase_of_mem ha] using
    card_supportFamily_le_pow_card_erase F B a hF

/-- The sum of weights of supports containing a site is bounded by the number of possible
supports times the bound on each term. This applies to operator norms without requiring the
terms to be Hermitian. -/
theorem sum_supportWeights_containing_le (F : Finset (Finset V)) (B : Finset V) (a : V)
    (w : Finset V → ℝ) (J : ℝ) (hJ : 0 ≤ J) (ha : a ∈ B)
    (hB : ∀ X ∈ F, a ∈ X → X ⊆ B) (hw : ∀ X ∈ F, w X ≤ J) :
    (∑ X ∈ F.filter (fun X => a ∈ X), w X) ≤ (2 ^ (B.card - 1) : ℕ) * J := by
  have hcard : (F.filter (fun X => a ∈ X)).card ≤ 2 ^ (B.card - 1) := by
    apply card_supportFamily_le_pow _ B a ha
    intro X hX
    obtain ⟨hXF, haX⟩ := Finset.mem_filter.mp hX
    exact ⟨haX, hB X hXF haX⟩
  calc
    (∑ X ∈ F.filter (fun X => a ∈ X), w X) ≤
        ∑ X ∈ F.filter (fun X => a ∈ X), J := by
      apply Finset.sum_le_sum
      intro X hX
      exact hw X (Finset.mem_filter.mp hX).1
    _ = ((F.filter (fun X => a ∈ X)).card : ℝ) * J := by simp
    _ ≤ (2 ^ (B.card - 1) : ℕ) * J :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hJ

/-- A nonnegative weight on each support is counted at least once by the sites it meets.
Only the weights of the original supports occur; no multiplicity of interaction labels is
allowed in the family. -/
theorem sum_supportWeights_meeting_le_sum_siteWeights (F : Finset (Finset V)) (S : Finset V)
    (w : Finset V → ℝ) (hw : ∀ X ∈ F, 0 ≤ w X) :
    (∑ X ∈ F.filter (fun X => ¬ Disjoint X S), w X) ≤
      ∑ a ∈ S, ∑ X ∈ F.filter (fun X => a ∈ X), w X := by
  classical
  rw [Finset.sum_filter]
  calc
    (∑ X ∈ F, if ¬ Disjoint X S then w X else 0) ≤
        ∑ X ∈ F, ∑ a ∈ S, if a ∈ X then w X else 0 := by
      apply Finset.sum_le_sum
      intro X hX
      by_cases hXS : Disjoint X S
      · simp only [hXS, not_true_eq_false, ite_false]
        exact Finset.sum_nonneg fun a _ => by split_ifs <;> first | exact hw X hX | rfl
      · obtain ⟨a, haX, haS⟩ := Finset.not_disjoint_iff.mp hXS
        simp only [hXS, not_false_eq_true, ite_true]
        calc
          w X = (if a ∈ X then w X else 0) := by simp [haX]
          _ ≤ ∑ b ∈ S, if b ∈ X then w X else 0 := by
            apply Finset.single_le_sum (fun b _ => ?_) haS
            split_ifs <;> first | exact hw X hX | rfl
    _ = ∑ a ∈ S, ∑ X ∈ F.filter (fun X => a ∈ X), w X := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_filter]

/-- A uniform per-site interaction budget gives a budget proportional to the cardinality
of any region. This is the step giving $κ = v_R b₀$ in Section 4 of the area-law manuscript. -/
theorem sum_supportWeights_meeting_le (F : Finset (Finset V)) (S : Finset V)
    (w : Finset V → ℝ) (b : ℝ) (hw : ∀ X ∈ F, 0 ≤ w X)
    (hb : ∀ a ∈ S, (∑ X ∈ F.filter (fun X => a ∈ X), w X) ≤ b) :
    (∑ X ∈ F.filter (fun X => ¬ Disjoint X S), w X) ≤ S.card * b := by
  calc
    (∑ X ∈ F.filter (fun X => ¬ Disjoint X S), w X) ≤
        ∑ a ∈ S, ∑ X ∈ F.filter (fun X => a ∈ X), w X :=
      sum_supportWeights_meeting_le_sum_siteWeights F S w hw
    _ ≤ ∑ _a ∈ S, b := Finset.sum_le_sum hb
    _ = S.card * b := by simp

/-- Total weight of all length-$n$ continuations of an interaction chain beginning at $X$.
Each next support must intersect the current support; repeated supports are permitted.
This is the finite chain sum used in Section 4 of the area-law manuscript. -/
def interactionChainWeightSum (F : Finset (Finset V)) (w : Finset V → ℝ)
    (X : Finset V) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X),
      w Y * interactionChainWeightSum F w Y n

/-- Local site budgets bound the total interaction-chain weight by $κ^n$, where
$κ = v b$, when every original support contains at most $v$ sites.
The estimate is independent of the number of original supports. -/
theorem interactionChainWeightSum_le_pow (F : Finset (Finset V)) (w : Finset V → ℝ)
    (v : ℕ) (b : ℝ) (hb : 0 ≤ b) (hw : ∀ X ∈ F, 0 ≤ w X)
    (hcard : ∀ X ∈ F, X.card ≤ v)
    (hsite : ∀ a : V, (∑ Y ∈ F.filter (fun Y => a ∈ Y), w Y) ≤ b)
    (n : ℕ) (X : Finset V) (hX : X ∈ F) :
    interactionChainWeightSum F w X n ≤ ((v : ℝ) * b) ^ n := by
  induction n generalizing X with
  | zero => simp [interactionChainWeightSum]
  | succ n ih =>
    have hκ : 0 ≤ (v : ℝ) * b := mul_nonneg (Nat.cast_nonneg v) hb
    have hrow : (∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X), w Y) ≤ (v : ℝ) * b := by
      calc
        (∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X), w Y) ≤ X.card * b :=
          sum_supportWeights_meeting_le F X w b hw (fun a _ => hsite a)
        _ ≤ (v : ℝ) * b :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard X hX)) hb
    calc
      interactionChainWeightSum F w X (n + 1) =
          ∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X),
            w Y * interactionChainWeightSum F w Y n := rfl
      _ ≤ ∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X), w Y * ((v : ℝ) * b) ^ n := by
        apply Finset.sum_le_sum
        intro Y hY
        have hYF := (Finset.mem_filter.mp hY).1
        exact mul_le_mul_of_nonneg_left (ih Y hYF) (hw Y hYF)
      _ = (∑ Y ∈ F.filter (fun Y => ¬ Disjoint Y X), w Y) * ((v : ℝ) * b) ^ n :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ ((v : ℝ) * b) * ((v : ℝ) * b) ^ n :=
        mul_le_mul_of_nonneg_right hrow (pow_nonneg hκ n)
      _ = ((v : ℝ) * b) ^ (n + 1) := by rw [pow_succ, mul_comm]

end Budget

section Diamond

variable {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}

omit [Finite V] [DecidableEq V] in
/-- Every finite support of graph range at most `R` has at most `v_R = 1 + 2 R (R + 1)` sites.
The empty support is included. Source: `eq:ball-count` in the area-law manuscript. -/
theorem card_support_le_diamond (coord : V → ℤ × ℤ) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (X : Finset V) (R : ℕ)
    (hrange : ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R) :
    X.card ≤ 1 + 2 * R * (R + 1) := by
  classical
  by_cases hX : X.Nonempty
  · obtain ⟨a, ha⟩ := hX
    exact card_le_diamond_of_walks coord X hcoord hstep a R (hrange a ha)
  · simp only [Finset.not_nonempty_iff_eq_empty] at hX
    simp [hX]

/-- At most `μ_R = 2 ^ (v_R - 1)` original supports contain a specified site, with the exact
ambient diamond count `v_R`. A finite set of supports enforces one term per support.
Source: the interaction multiplicity bound following `eq:ball-count` in the area-law manuscript. -/
theorem card_supports_containing_le_diamond (coord : V → ℤ × ℤ)
    (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (a : V) :
    (F.filter (fun X ↦ a ∈ X)).card ≤ 2 ^ ((1 + 2 * R * (R + 1)) - 1) := by
  classical
  let := Fintype.ofFinite V
  let B : Finset V := Finset.univ.filter (fun x ↦ ∃ p : G.Walk a x, p.length ≤ R)
  have haB : a ∈ B := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ a, SimpleGraph.Walk.nil, by simp⟩
  have hB : B.card ≤ 1 + 2 * R * (R + 1) := by
    apply card_le_diamond_of_walks coord B hcoord hstep a R
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hFB : ∀ X ∈ F.filter (fun X ↦ a ∈ X), a ∈ X ∧ X ⊆ B := by
    intro X hX
    obtain ⟨hXF, haX⟩ := Finset.mem_filter.mp hX
    refine ⟨haX, ?_⟩
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hrange X hXF a haX x hx⟩
  calc
    (F.filter (fun X ↦ a ∈ X)).card ≤ 2 ^ (B.card - 1) :=
      card_supportFamily_le_pow _ B a haB hFB
    _ ≤ 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hB 1)

/-- Term weights bounded by `J ≥ 0` have site budget at most `μ_R * J`, using the exact
constant. Source: `eq:quasilocal-budget` in the area-law manuscript. -/
theorem sum_supportWeights_containing_le_diamond (coord : V → ℤ × ℤ)
    (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (w : Finset V → ℝ) (J : ℝ) (hJ : 0 ≤ J) (hw : ∀ X ∈ F, w X ≤ J) (a : V) :
    (∑ X ∈ F.filter (fun X ↦ a ∈ X), w X) ≤
      (2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J := by
  have hcard := card_supports_containing_le_diamond coord hcoord hstep F R hrange a
  calc
    (∑ X ∈ F.filter (fun X ↦ a ∈ X), w X) ≤
        ((F.filter (fun X ↦ a ∈ X)).card : ℝ) * J := by
      simpa using Finset.sum_le_card_nsmul (F.filter (fun X ↦ a ∈ X)) w J
        (fun X hX ↦ hw X (Finset.mem_filter.mp hX).1)
    _ ≤ (2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hJ

/-- Norms of original terms satisfy the source site budget `μ_R * J`. The terms may live in
any seminormed additive group; no operator or Hamiltonian model is imposed.
Source: `eq:quasilocal-budget` in the area-law manuscript. -/
theorem sum_supportNorms_containing_le_diamond {E : Type*} [SeminormedAddGroup E]
    (coord : V → ℤ × ℤ) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (h : Finset V → E) (J : ℝ) (hJ : 0 ≤ J) (hh : ∀ X ∈ F, ‖h X‖ ≤ J) (a : V) :
    (∑ X ∈ F.filter (fun X ↦ a ∈ X), ‖h X‖) ≤
      (2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J :=
  sum_supportWeights_containing_le_diamond coord hcoord hstep F R hrange
    (fun X ↦ ‖h X‖) J hJ hh a

/-- Weighted interaction-chain continuations are at most `(v_R * μ_R * J) ^ n`, with the
paper's exact diamond and multiplicity constants. Repeated supports are permitted.
Source: the iteration of `eq:quasilocal-budget` in the area-law manuscript. -/
theorem interactionChainWeightSum_le_diamond_pow (coord : V → ℤ × ℤ)
    (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (w : Finset V → ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hw0 : ∀ X ∈ F, 0 ≤ w X) (hwJ : ∀ X ∈ F, w X ≤ J)
    (n : ℕ) (X : Finset V) (hX : X ∈ F) :
    interactionChainWeightSum F w X n ≤
      ((1 + 2 * R * (R + 1) : ℕ) *
        ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J)) ^ n := by
  apply interactionChainWeightSum_le_pow F w (1 + 2 * R * (R + 1))
    ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J)
    (mul_nonneg (Nat.cast_nonneg _) hJ) hw0 _ _ n X hX
  · intro Y hY
    exact card_support_le_diamond coord hcoord hstep Y R (hrange Y hY)
  · intro a
    exact sum_supportWeights_containing_le_diamond coord hcoord hstep F R hrange w J hJ hwJ a

/-- The exact continuation bound specialized to term norms.
Source: the interaction-chain iteration after `eq:quasilocal-budget` in the area-law manuscript. -/
theorem interactionChainWeightSum_norm_le_diamond_pow {E : Type*} [SeminormedAddGroup E]
    (coord : V → ℤ × ℤ) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (F : Finset (Finset V)) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ R)
    (h : Finset V → E) (J : ℝ) (hJ : 0 ≤ J) (hh : ∀ X ∈ F, ‖h X‖ ≤ J)
    (n : ℕ) (X : Finset V) (hX : X ∈ F) :
    interactionChainWeightSum F (fun Y ↦ ‖h Y‖) X n ≤
      ((1 + 2 * R * (R + 1) : ℕ) *
        ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J)) ^ n :=
  interactionChainWeightSum_le_diamond_pow coord hcoord hstep F R hrange
    (fun Y ↦ ‖h Y‖) J hJ (fun _ _ ↦ norm_nonneg _) hh n X hX

end Diamond

/-! ### Finite domains of the square lattice -/

/-- The number of configurations of a domain with local dimension `q` is `q^{|Λ|}`, the
dimension of the tensor product of the site spaces. Area law, Section 1. -/
@[simp] theorem card_configuration (Λ : Finset (ℤ × ℤ)) (q : ℕ) :
    Fintype.card (↥Λ → Fin q) = q ^ Λ.card := by
  simp

/-- A support of graph diameter at most `R` meeting `S` lies in `N_R(S)`. -/
theorem subset_graphNeighborhood_of_isAdmissibleSupport {Λ : Finset (ℤ × ℤ)} {R : ℕ}
    {X : Finset ↥Λ} (hX : IsAdmissibleSupport Λ R X) {S : Finset ↥Λ}
    (hXS : ¬Disjoint X S) : X ⊆ graphNeighborhood (planeDomainGraph Λ) S R :=
  fun y hy ↦ by
    obtain ⟨x, hxX, hxS⟩ := Finset.not_disjoint_iff.mp hXS
    exact mem_graphNeighborhood_iff_exists_walk.mpr ⟨x, hxS, hX.2 x hxX y hy⟩

end ManyBody
