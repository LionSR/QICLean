/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.StrictCombination
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Yamagami's cyclic reciprocal functional

This file begins the source-faithful formalization of the variational cyclic
inequality used for Choi-type positive maps.  It defines the forward-window
functional of Yamagami, records its elementary projective and orientation
properties, and proves the corrected Wolf-range part of the centered open-disk
estimate in Lemma 6 of Yamagami, *Cyclic Inequalities*, Proc. Amer. Math. Soc.
118 (1993), 521--527, specialized to the stride `l = 1` needed by Wolf's
Choi-type maps.  The printed lemma includes the endpoint `m = d - 1` when
`s = d`, but there every nonconstant character has eigenvalue zero and the
claimed strict disk inequality becomes an equality.  The theorem below uses
the valid range `m ≤ d - 2`; the omitted endpoint is valid only when `s > d`.

The source inequality is stated for strictly positive coordinates.  At the
projective boundary Yamagami treats a formal `0 / 0` as an indeterminate limit.
The definitions below are algebraically total because division in Lean is
total; no theorem in this file identifies that convention with Yamagami's
boundary analysis, and the full cyclic inequality is not claimed here.

It also contains the following results.

* `Yamagami.deleteLastCoordinate`, `Yamagami.functional_le_deleteLastCoordinate`: Yamagami's
  regular-boundary recurrence.
-/

open scoped BigOperators

namespace Yamagami

section CyclicReciprocal

variable (d m : ℕ) [NeZero d]

/-- The forward cyclic denominator in Yamagami's inequality, specialized to
stride `l = 1`. -/
noncomputable def forwardDenominator (s : ℝ) (x : ZMod d → ℝ) (i : ZMod d) : ℝ :=
  (s - (m : ℝ)) * x i +
    ∑ k : Fin m, x (i + ((k.1 + 1 : ℕ) : ZMod d))

/-- Yamagami's homogeneous forward-window reciprocal functional. -/
noncomputable def functional (s : ℝ) (x : ZMod d → ℝ) : ℝ :=
  ∑ i, x i / forwardDenominator d m s x i

/-- Normalize a nonzero nonnegative vector to the standard simplex. -/
noncomputable def normalize (x : ZMod d → ℝ) : ZMod d → ℝ :=
  fun i ↦ x i / ∑ j, x j

omit [NeZero d] in
/-- Negating the cyclic index converts Yamagami's forward window to the
backward window used by the Choi-type rank-one weight. -/
theorem forwardDenominator_comp_neg (s : ℝ) (x : ZMod d → ℝ) (i : ZMod d) :
    forwardDenominator d m s (fun j ↦ x (-j)) (-i) =
      (s - (m : ℝ)) * x i +
        ∑ k : Fin m, x (i - ((k.1 + 1 : ℕ) : ZMod d)) := by
  simp only [forwardDenominator, neg_neg]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  congr 1
  abel

/-- Functional-level form of the forward/backward orientation conversion. -/
theorem functional_comp_neg (s : ℝ) (x : ZMod d → ℝ) :
    functional d m s (fun i ↦ x (-i)) =
      ∑ i, x i /
        ((s - (m : ℝ)) * x i +
          ∑ k : Fin m, x (i - ((k.1 + 1 : ℕ) : ZMod d))) := by
  rw [functional]
  calc
    (∑ i, x (-i) / forwardDenominator d m s (fun j ↦ x (-j)) i) =
        ∑ i, x (-(-i)) /
          forwardDenominator d m s (fun j ↦ x (-j)) (-i) := by
            symm
            exact Equiv.sum_comp (Equiv.neg (ZMod d))
              (fun i : ZMod d ↦
                x (-i) / forwardDenominator d m s (fun j ↦ x (-j)) i)
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [forwardDenominator_comp_neg]
      simp

omit [NeZero d] in
/-- The forward denominator scales linearly with its vector argument. -/
theorem forwardDenominator_mul (s c : ℝ) (x : ZMod d → ℝ) (i : ZMod d) :
    forwardDenominator d m s (fun j ↦ c * x j) i =
      c * forwardDenominator d m s x i := by
  simp only [forwardDenominator]
  rw [← Finset.mul_sum]
  ring

/-- The reciprocal functional is invariant under nonzero scalar rescaling.
This is an algebraic statement for Lean's total division. -/
theorem functional_mul (s c : ℝ) (x : ZMod d → ℝ) (hc : c ≠ 0) :
    functional d m s (fun i ↦ c * x i) = functional d m s x := by
  simp only [functional]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [forwardDenominator_mul, mul_div_mul_left _ _ hc]

/-- A nonnegative nonzero vector normalizes to the standard simplex: the normalized
vector has nonnegative coordinates summing to one. -/
theorem normalize_mem_stdSimplex (x : ZMod d → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hsum : 0 < ∑ i, x i) :
    (∀ i, 0 ≤ normalize d x i) ∧ ∑ i, normalize d x i = 1 := by
  refine ⟨fun i ↦ div_nonneg (hx i) hsum.le, ?_⟩
  simp only [normalize, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ hsum.ne'

/-- Normalization does not change the reciprocal functional. -/
theorem functional_normalize (s : ℝ) (x : ZMod d → ℝ)
    (hsum : ∑ i, x i ≠ 0) :
    functional d m s (normalize d x) = functional d m s x := by
  have hnormalize :
      normalize d x = fun i ↦ (∑ j, x j)⁻¹ * x i := by
    funext i
    simp only [normalize, div_eq_mul_inv, mul_comm]
  rw [hnormalize]
  exact functional_mul d m s _ x (inv_ne_zero hsum)

omit [NeZero d] in
/-- The constant vector has denominator `s` at every coordinate. -/
@[simp] theorem forwardDenominator_one (s : ℝ) (i : ZMod d) :
    forwardDenominator d m s (fun _ ↦ 1) i = s := by
  simp [forwardDenominator]

/-- The value on the constant ray is `d / s`. -/
@[simp] theorem functional_one (s : ℝ) :
    functional d m s (fun _ ↦ 1) = (d : ℝ) / s := by
  simp [functional, ZMod.card, div_eq_mul_inv]

/-- The eigenvalue of Yamagami's cyclic matrix at the standard character
indexed by `j`. -/
noncomputable def symbol (s : ℝ) (j : ZMod d) : ℂ :=
  ((s - (m : ℝ) : ℝ) : ℂ) +
    ∑ k : Fin m,
      ZMod.stdAddChar (j * ((k.1 + 1 : ℕ) : ZMod d))

private theorem norm_weighted_sum_lt_sum_of_ne
    {I : Type*} [Fintype I] (w : I → ℝ) (z : I → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i)
    {i j : I} (hij : z i ≠ z j) (hwi : 0 < w i) (hwj : 0 < w j)
    (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖∑ i, (w i : ℂ) * z i‖ < ∑ i, w i := by
  classical
  let W : ℝ := ∑ i, w i
  let w' : I → ℝ := fun i ↦ w i / W
  have hw' : ∀ k ∈ (Finset.univ : Finset I), 0 ≤ w' k := by
    intro k _
    exact div_nonneg (hw k) hW.le
  have hsum : ∑ k ∈ (Finset.univ : Finset I), w' k = 1 := by
    simp only [w', div_eq_mul_inv]
    rw [← Finset.sum_mul]
    change W * W⁻¹ = 1
    exact mul_inv_cancel₀ hW.ne'
  have hstrict := norm_sum_lt_of_strictConvexSpace
    (t := (Finset.univ : Finset I)) (w := w') (z := z) (r := (1 : ℝ))
    hw' hsum (Finset.mem_univ i) (Finset.mem_univ j) hij
    (div_ne_zero hwi.ne' hW.ne') (div_ne_zero hwj.ne' hW.ne')
    (fun k _ ↦ hz k)
  have hrewrite :
      (∑ k, w' k • z k) = (1 / W) • ∑ k, w k • z k := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    change (w k / W) • z k = (1 / W) • w k • z k
    rw [smul_smul]
    congr 1
    field_simp
  rw [hrewrite, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hW)] at hstrict
  have hdiv : ‖∑ k, (w k : ℂ) * z k‖ / W < 1 := by
    simpa [one_div, div_eq_mul_inv, smul_eq_mul, mul_comm] using hstrict
  exact (div_lt_one hW).mp hdiv

private theorem finEquiv_apply_natCast (n : ℕ) [NeZero n] (k : Fin n) :
    ZMod.finEquiv n k = (k.1 : ZMod n) := by
  apply ZMod.val_injective n
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact (ZMod.val_natCast_of_lt k.2).symm

/-- The corrected Wolf-range part of Yamagami's Lemma 6, specialized to stride
`l = 1`: for `m ≤ d - 2`, every nonconstant Fourier eigenvalue lies in the
open disk with center `s / 2` and radius `s / 2`.

The printed range also permits `m = d - 1` at `s = d`; that endpoint is false
with a strict inequality, because the nonconstant eigenvalues are zero. -/
theorem norm_symbol_sub_half_lt_half
    (hd : 3 ≤ d) (hm₁ : 1 ≤ m) (hm₂ : m ≤ d - 2)
    (s : ℝ) (hs : (d : ℝ) ≤ s) {j : ZMod d} (hj : j ≠ 0) :
    ‖symbol d m s j - ((s / 2 : ℝ) : ℂ)‖ < s / 2 := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsd_nonneg : 0 ≤ (s - d) / 2 := by linarith
  let root : ℕ → ℂ := fun k ↦
    ZMod.stdAddChar (j * ((k + 1 : ℕ) : ZMod d))
  have hroot_norm (k : ℕ) : ‖root k‖ = 1 := by
    change ‖ZMod.stdAddChar (j * ((k + 1 : ℕ) : ZMod d))‖ = 1
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  have hroot_ne (k : ℕ) : root k ≠ root (k + 1) := by
    intro h
    have harg := ZMod.injective_stdAddChar h
    apply hj
    calc
      j = j *
          (((k + 2 : ℕ) : ZMod d) - ((k + 1 : ℕ) : ZMod d)) := by
            push_cast
            ring
      _ = 0 := by rw [mul_sub, harg, sub_self]
  have hchar_sum :
      ∑ x : ZMod d, ZMod.stdAddChar (j * x) = 0 := by
    simpa [hj, mul_comm] using
      (AddChar.sum_mulShift j (ZMod.isPrimitive_stdAddChar d))
  have hfull : ∑ k ∈ Finset.range d, root k = 0 := by
    let e : Fin d ≃ ZMod d :=
      (ZMod.finEquiv d).toEquiv.trans (Equiv.addRight (1 : ZMod d))
    have he := Equiv.sum_comp e
      (fun x : ZMod d ↦ ZMod.stdAddChar (j * x))
    have hfin : ∑ k : Fin d, root k.1 = 0 := by
      rw [show (∑ k : Fin d, root k.1) =
          ∑ x : ZMod d, ZMod.stdAddChar (j * x) by
        simpa [e, root, finEquiv_apply_natCast] using he]
      exact hchar_sum
    simpa only [Fin.sum_univ_eq_sum_range] using hfin
  have hbase :
      ‖symbol d m (d : ℝ) j - ((((d : ℝ) / 2 : ℝ)) : ℂ)‖ < (d : ℝ) / 2 := by
    by_cases hlow : 2 * m ≤ d
    · let A : ℝ := (d : ℝ) / 2 - (m : ℝ)
      have hAnonneg : 0 ≤ A := by
        dsimp [A]
        have hlowR : 2 * (m : ℝ) ≤ (d : ℝ) := by exact_mod_cast hlow
        linarith
      let w : Fin (m + 1) → ℝ := Fin.cases A fun _ ↦ 1
      let z : Fin (m + 1) → ℂ := Fin.cases 1 fun k ↦ root k.1
      have hw : ∀ k, 0 ≤ w k := by
        intro k
        refine Fin.cases hAnonneg (fun _ ↦ zero_le_one) k
      have hz : ∀ k, ‖z k‖ ≤ 1 := by
        intro k
        refine Fin.cases (by change ‖(1 : ℂ)‖ ≤ 1; norm_num) (fun r ↦ ?_) k
        rw [show z r.succ = root r.1 by rfl, hroot_norm]
      have hsumw : ∑ k, w k = (d : ℝ) / 2 := by
        rw [Fin.sum_univ_succ]
        simp only [w, Fin.cases_zero, Fin.cases_succ, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        dsimp [A]
        ring
      have hroot_zero_ne_one : root 0 ≠ 1 := by
        intro h
        dsimp [root] at h
        have h' : ZMod.stdAddChar (j * (1 : ZMod d)) = 1 := by
          simpa using h
        rw [← (ZMod.stdAddChar (N := d)).map_zero_eq_one] at h'
        have harg := ZMod.injective_stdAddChar h'
        exact hj (by simpa using harg)
      have hstrict :
          ‖∑ k, (w k : ℂ) * z k‖ < ∑ k, w k := by
        by_cases hmone : m = 1
        · let k₀ : Fin m := ⟨0, by omega⟩
          have hApos : 0 < A := by
            dsimp [A]
            have hmR : (m : ℝ) = 1 := by exact_mod_cast hmone
            have hdR' : (3 : ℝ) ≤ d := by exact_mod_cast hd
            linarith
          have hzne : z 0 ≠ z k₀.succ := by
            simpa [z, k₀] using hroot_zero_ne_one.symm
          exact norm_weighted_sum_lt_sum_of_ne w z hw
            (by rw [hsumw]; positivity) hzne (by simpa [w] using hApos)
            (by simp [w]) hz
        · have hm₂' : 2 ≤ m := by omega
          let k₀ : Fin m := ⟨0, by omega⟩
          let k₁ : Fin m := ⟨1, by omega⟩
          have hzne : z k₀.succ ≠ z k₁.succ := by
            simpa [z, k₀, k₁] using hroot_ne 0
          exact norm_weighted_sum_lt_sum_of_ne w z hw
            (by rw [hsumw]; positivity) hzne (by simp [w]) (by simp [w]) hz
      have hrepr :
          symbol d m (d : ℝ) j - ((((d : ℝ) / 2 : ℝ)) : ℂ) =
            ∑ k, (w k : ℂ) * z k := by
        rw [Fin.sum_univ_succ]
        change
          symbol d m (d : ℝ) j - ((((d : ℝ) / 2 : ℝ)) : ℂ) =
            (A : ℂ) * 1 + ∑ k : Fin m, (1 : ℂ) * root k.1
        simp only [mul_one, one_mul]
        simp only [symbol]
        rw [show
          (∑ k : Fin m,
              ZMod.stdAddChar (j * ((k.1 + 1 : ℕ) : ZMod d))) =
            ∑ k : Fin m, root k.1 by rfl]
        dsimp [A]
        push_cast
        ring
      rw [hrepr]
      simpa only [hsumw] using hstrict
    · have hhigh : d < 2 * m := by omega
      have hmd : m ≤ d := by omega
      let q : ℕ := d - m
      have hq₂ : 2 ≤ q := by omega
      let B : ℝ := (m : ℝ) - (d : ℝ) / 2
      have hBpos : 0 < B := by
        dsimp [B]
        have hhighR : (d : ℝ) < 2 * (m : ℝ) := by exact_mod_cast hhigh
        linarith
      let w : Fin (q + 1) → ℝ := Fin.cases B fun _ ↦ 1
      let z : Fin (q + 1) → ℂ :=
        Fin.cases (-1) fun k ↦ -root (m + k.1)
      let k₀ : Fin q := ⟨0, by omega⟩
      let k₁ : Fin q := ⟨1, by omega⟩
      have hw : ∀ k, 0 ≤ w k := by
        intro k
        refine Fin.cases ?_ (fun _ ↦ zero_le_one) k
        exact hBpos.le
      have hz : ∀ k, ‖z k‖ ≤ 1 := by
        intro k
        refine Fin.cases ?_ (fun r ↦ ?_) k
        · change ‖(-1 : ℂ)‖ ≤ 1
          norm_num
        · rw [show z r.succ = -root (m + r.1) by rfl, norm_neg,
            hroot_norm]
      have hsumw : ∑ k, w k = (d : ℝ) / 2 := by
        rw [Fin.sum_univ_succ]
        simp only [w, Fin.cases_zero, Fin.cases_succ, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        dsimp [B, q]
        rw [Nat.cast_sub hmd]
        ring
      have hzne : z k₀.succ ≠ z k₁.succ := by
        simpa [z, k₀, k₁, add_assoc] using hroot_ne m
      have hstrict := norm_weighted_sum_lt_sum_of_ne w z hw
        (by rw [hsumw]; positivity) hzne (by simp [w]) (by simp [w]) hz
      have hsplit :
          (∑ k ∈ Finset.range m, root k) +
              ∑ k ∈ Finset.range q, root (m + k) = 0 := by
        rw [← Finset.sum_range_add]
        have hmq : m + q = d := by omega
        rw [hmq]
        exact hfull
      have hwindow :
          (∑ k : Fin m, root k.1) = -∑ k : Fin q, root (m + k.1) := by
        rw [Fin.sum_univ_eq_sum_range root m,
          Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ root (m + k)) q]
        exact eq_neg_of_add_eq_zero_left hsplit
      have hrepr :
          symbol d m (d : ℝ) j - ((((d : ℝ) / 2 : ℝ)) : ℂ) =
            ∑ k, (w k : ℂ) * z k := by
        rw [Fin.sum_univ_succ]
        change
          symbol d m (d : ℝ) j - ((((d : ℝ) / 2 : ℝ)) : ℂ) =
            (B : ℂ) * (-1) +
              ∑ k : Fin q, (1 : ℂ) * (-root (m + k.1))
        simp only [mul_neg, mul_one, one_mul, Finset.sum_neg_distrib]
        rw [← hwindow]
        simp only [symbol]
        rw [show
          (∑ k : Fin m,
              ZMod.stdAddChar (j * ((k.1 + 1 : ℕ) : ZMod d))) =
            ∑ k : Fin m, root k.1 by rfl]
        change
          ((((d : ℝ) - (m : ℝ) : ℝ)) : ℂ) +
                ∑ k : Fin m, root k.1 - ((((d : ℝ) / 2 : ℝ)) : ℂ) =
            -(B : ℂ) + ∑ k : Fin m, root k.1
        dsimp [B]
        push_cast
        ring
      rw [hrepr]
      simpa only [hsumw] using hstrict
  have hshift :
      symbol d m s j - ((s / 2 : ℝ) : ℂ) =
        (symbol d m (d : ℝ) j - ((((d : ℝ) / 2 : ℝ)) : ℂ)) +
          ((((s - d) / 2 : ℝ)) : ℂ) := by
    simp only [symbol]
    push_cast
    ring
  rw [hshift]
  calc
    ‖(symbol d m (d : ℝ) j - ((((d : ℝ) / 2 : ℝ)) : ℂ)) +
        ((((s - d) / 2 : ℝ)) : ℂ)‖ ≤
        ‖symbol d m (d : ℝ) j - ((((d : ℝ) / 2 : ℝ)) : ℂ)‖ +
          ‖((((s - d) / 2 : ℝ)) : ℂ)‖ := norm_add_le _ _
    _ < (d : ℝ) / 2 + (s - d) / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsd_nonneg]
      simpa [add_comm] using add_lt_add_right hbase ((s - d) / 2)
    _ = s / 2 := by ring

end CyclicReciprocal

section RegularBoundary

/-!
## Yamagami's regular-boundary recurrence

This file formalizes the dimension-reduction step on p. 525 of
S. Yamagami, *Cyclic inequalities*, Proc. Amer. Math. Soc. 118 (1993),
521--527.  For the stride-one functional, delete a zero final coordinate.
The remaining cyclic order is represented by the map

`ZMod (N - 1) → ZMod N,  i ↦ i.val`.

The reduced forward window skips the deleted coordinate.  Before that
coordinate is reached, the original denominator has one additional
nonnegative term; after it is reached, the two windows agree because the
skipped term is zero.  Consequently the comparison is non-strict.  The
statement uses Lean's total division, so it remains valid when the reduced
vector has a singular denominator.
-/

/-- Delete the final coordinate from a cyclic vector while preserving the
linear order `0, ..., N - 2` used in Yamagami's p. 525 reduction. -/
def deleteLastCoordinate (N : ℕ) (x : ZMod N → ℝ) : ZMod (N - 1) → ℝ :=
  fun i ↦ x (i.val : ZMod N)

/-- Embed a step in the reduced forward window into the original window.
After the path crosses the deleted final coordinate, its step is increased
by one. -/
private def reducedStepEmbedding (N m : ℕ) (i : ZMod (N - 1))
    (hm : 1 ≤ m) (q : Fin (m - 1)) : Fin m :=
  if i.val + q.val + 1 < N - 1 then
    ⟨q.val, by omega⟩
  else
    ⟨q.val + 1, by omega⟩

private theorem reducedStepEmbedding_injective
    (N m : ℕ) (hm : 1 ≤ m) (i : ZMod (N - 1)) :
    Function.Injective (reducedStepEmbedding N m i hm) := by
  intro q r hqr
  apply Fin.ext
  have hval := congrArg Fin.val hqr
  by_cases hq : i.val + q.val + 1 < N - 1 <;>
    by_cases hr : i.val + r.val + 1 < N - 1 <;>
      simp [reducedStepEmbedding, hq, hr] at hval <;> omega

private theorem deleteLastCoordinate_forwardStep
    (N m : ℕ) [NeZero N] (hN : 3 ≤ N) (hm : 1 ≤ m)
    (hmN : m ≤ N - 2) (x : ZMod N → ℝ) (i : ZMod (N - 1))
    (q : Fin (m - 1)) :
    deleteLastCoordinate N x
        (i + ((q.val + 1 : ℕ) : ZMod (N - 1))) =
      x ((i.val : ZMod N) +
        (((reducedStepEmbedding N m i hm q).val + 1 : ℕ) : ZMod N)) := by
  let _ : NeZero (N - 1) := ⟨by omega⟩
  unfold deleteLastCoordinate
  congr 1
  apply ZMod.val_injective N
  have hreducedVal :
      (i + ((q.val + 1 : ℕ) : ZMod (N - 1))).val < N - 1 :=
    ZMod.val_lt _
  rw [ZMod.val_natCast_of_lt (by omega :
    (i + ((q.val + 1 : ℕ) : ZMod (N - 1))).val < N)]
  have hqReduced : q.val + 1 < N - 1 := by omega
  have hqReducedVal :
      (((q.val + 1 : ℕ) : ZMod (N - 1))).val = q.val + 1 :=
    ZMod.val_natCast_of_lt hqReduced
  by_cases hcross : i.val + q.val + 1 < N - 1
  · have hleft :
        i.val + (((q.val + 1 : ℕ) : ZMod (N - 1))).val < N - 1 := by
      omega
    rw [ZMod.val_add_of_lt hleft]
    rw [hqReducedVal]
    simp only [reducedStepEmbedding, hcross, ite_true, Fin.val_mk]
    have hiN : i.val < N := by
      have hi := ZMod.val_lt i
      omega
    have hstepN : q.val + 1 < N := by omega
    have hright :
        ((i.val : ZMod N).val +
          (((q.val + 1 : ℕ) : ZMod N)).val < N) := by
      rw [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hstepN]
      omega
    rw [ZMod.val_add_of_lt hright, ZMod.val_natCast_of_lt hiN,
      ZMod.val_natCast_of_lt hstepN]
  · have hleft :
        N - 1 ≤ i.val + (((q.val + 1 : ℕ) : ZMod (N - 1))).val := by
      omega
    rw [ZMod.val_add_of_le hleft, hqReducedVal]
    simp only [reducedStepEmbedding, hcross, ite_false, Fin.val_mk]
    have hiN : i.val < N := by
      have hi := ZMod.val_lt i
      omega
    have hstepN : q.val + 1 + 1 < N := by omega
    have hright :
        N ≤ (i.val : ZMod N).val +
          (((q.val + 1 + 1 : ℕ) : ZMod N)).val := by
      rw [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hstepN]
      omega
    rw [ZMod.val_add_of_le hright, ZMod.val_natCast_of_lt hiN,
      ZMod.val_natCast_of_lt hstepN]
    omega

private theorem reduced_forward_sum_le
    (N m : ℕ) [NeZero N] (hN : 3 ≤ N) (hm : 1 ≤ m)
    (hmN : m ≤ N - 2) (x : ZMod N → ℝ) (hx : ∀ j, 0 ≤ x j)
    (i : ZMod (N - 1)) :
    (∑ q : Fin (m - 1),
        deleteLastCoordinate N x
          (i + ((q.val + 1 : ℕ) : ZMod (N - 1)))) ≤
      ∑ k : Fin m,
        x ((i.val : ZMod N) + ((k.val + 1 : ℕ) : ZMod N)) := by
  let e : Fin (m - 1) → Fin m := reducedStepEmbedding N m i hm
  have he : Function.Injective e := reducedStepEmbedding_injective N m hm i
  calc
    (∑ q : Fin (m - 1),
        deleteLastCoordinate N x
          (i + ((q.val + 1 : ℕ) : ZMod (N - 1)))) =
        ∑ q : Fin (m - 1),
          x ((i.val : ZMod N) + ((e q).val + 1 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro q _
      exact deleteLastCoordinate_forwardStep N m hN hm hmN x i q
    _ = ∑ k ∈ Finset.univ.image e,
        x ((i.val : ZMod N) + ((k.val + 1 : ℕ) : ZMod N)) := by
      symm
      rw [Finset.sum_image he.injOn]
    _ ≤ ∑ k : Fin m,
        x ((i.val : ZMod N) + ((k.val + 1 : ℕ) : ZMod N)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ ↦ hx _)

private theorem sum_erase_lastCoordinate
    (N : ℕ) [NeZero N] [NeZero (N - 1)] (hN : 2 ≤ N)
    (f : ZMod N → ℝ) :
    (∑ j ∈ (Finset.univ : Finset (ZMod N)).erase
        ((N - 1 : ℕ) : ZMod N), f j) =
      ∑ i : ZMod (N - 1), f (i.val : ZMod N) := by
  symm
  apply Finset.sum_bij (fun i _ ↦ (i.val : ZMod N))
  · intro i _
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro heq
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt (by
      have hi := ZMod.val_lt i
      omega : i.val < N)] at hval
    rw [ZMod.val_natCast_of_lt (by omega : N - 1 < N)] at hval
    have hi := ZMod.val_lt i
    omega
  · intro a _ b _ hab
    apply ZMod.val_injective (N - 1)
    have hval := congrArg ZMod.val hab
    rw [ZMod.val_natCast_of_lt (by
      have ha := ZMod.val_lt a
      omega : a.val < N)] at hval
    rw [ZMod.val_natCast_of_lt (by
      have hb := ZMod.val_lt b
      omega : b.val < N)] at hval
    exact hval
  · intro b hb
    have hbne : b ≠ ((N - 1 : ℕ) : ZMod N) := (Finset.mem_erase.mp hb).1
    have hbvalne : b.val ≠ N - 1 := by
      intro hval
      apply hbne
      apply ZMod.val_injective N
      rw [ZMod.val_natCast_of_lt (by omega : N - 1 < N)]
      exact hval
    have hbsmall : b.val < N - 1 := by
      have hbval := ZMod.val_lt b
      omega
    refine ⟨(b.val : ZMod (N - 1)), Finset.mem_univ _, ?_⟩
    rw [ZMod.val_natCast_of_lt hbsmall, ZMod.natCast_zmod_val]
  · intro i _
    rfl

private theorem retained_summand_le_reduced
    (N m : ℕ) [NeZero N] [NeZero (N - 1)] (hN : 3 ≤ N)
    (hm : 1 ≤ m) (hmN : m ≤ N - 2) (s : ℝ) (hs : (N : ℝ) ≤ s)
    (x : ZMod N → ℝ) (hx : ∀ j, 0 ≤ x j) (i : ZMod (N - 1)) :
    x (i.val : ZMod N) /
        forwardDenominator N m s x (i.val : ZMod N) ≤
      deleteLastCoordinate N x i /
        forwardDenominator (N - 1) (m - 1) (s - 1)
          (deleteLastCoordinate N x) i := by
  have hcoeff :
      (s - 1) - ((m - 1 : ℕ) : ℝ) = s - (m : ℝ) := by
    rw [Nat.cast_sub hm]
    norm_num
  have hsum := reduced_forward_sum_le N m hN hm hmN x hx i
  have hdenominator :
      forwardDenominator (N - 1) (m - 1) (s - 1)
          (deleteLastCoordinate N x) i ≤
        forwardDenominator N m s x (i.val : ZMod N) := by
    unfold forwardDenominator
    rw [hcoeff]
    change
      (s - (m : ℝ)) * x (i.val : ZMod N) +
          ∑ q : Fin (m - 1), deleteLastCoordinate N x
            (i + ((q.val + 1 : ℕ) : ZMod (N - 1))) ≤
        (s - (m : ℝ)) * x (i.val : ZMod N) +
          ∑ k : Fin m,
            x ((i.val : ZMod N) + ((k.val + 1 : ℕ) : ZMod N))
    exact add_le_add_right hsum _
  change
    x (i.val : ZMod N) / forwardDenominator N m s x (i.val : ZMod N) ≤
      x (i.val : ZMod N) /
        forwardDenominator (N - 1) (m - 1) (s - 1)
          (deleteLastCoordinate N x) i
  by_cases hxi : x (i.val : ZMod N) = 0
  · have hxiCast : x (ZMod.cast i : ZMod N) = 0 := by
      rw [ZMod.cast_eq_val]
      exact hxi
    simp [hxiCast]
  · have hxipos : 0 < x (i.val : ZMod N) :=
      lt_of_le_of_ne (hx _) (Ne.symm hxi)
    have hmNlt : m < N := by omega
    have hms : (m : ℝ) < s := by
      have hmNR : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmNlt
      exact hmNR.trans_le hs
    have hsumNonneg :
        0 ≤ ∑ q : Fin (m - 1), deleteLastCoordinate N x
          (i + ((q.val + 1 : ℕ) : ZMod (N - 1))) :=
      Finset.sum_nonneg fun q _ ↦ hx _
    have hdenominatorPos :
        0 < forwardDenominator (N - 1) (m - 1) (s - 1)
          (deleteLastCoordinate N x) i := by
      unfold forwardDenominator
      rw [hcoeff]
      exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr hms) hxipos) hsumNonneg
    exact div_le_div_of_nonneg_left (hx _) hdenominatorPos hdenominator

/-- Yamagami's p. 525 regular-boundary recurrence, with the zero placed in
the final coordinate.  The hypotheses are the exact stride-one source range
used before the `m = 1` base case.  No regularity condition is needed after
adopting Lean's totalized convention `0 / 0 = 0`; in particular, the reduced
vector is allowed to be singular. -/
theorem functional_le_deleteLastCoordinate
    (N m : ℕ) [NeZero N] (hN : 3 ≤ N) (hm : 2 ≤ m)
    (hmN : m ≤ N - 2) (s : ℝ) (hs : (N : ℝ) ≤ s)
    (x : ZMod N → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hlast : x ((N - 1 : ℕ) : ZMod N) = 0) :
    functional N m s x ≤
      @functional (N - 1) (m - 1) ⟨by omega⟩
        (s - 1) (deleteLastCoordinate N x) := by
  let _ : NeZero (N - 1) := ⟨by omega⟩
  unfold functional
  rw [← Finset.sum_erase_add (Finset.univ : Finset (ZMod N))
    (fun i ↦ x i / forwardDenominator N m s x i)
    (Finset.mem_univ ((N - 1 : ℕ) : ZMod N))]
  rw [hlast, zero_div, add_zero]
  rw [sum_erase_lastCoordinate N (by omega)
    (fun i ↦ x i / forwardDenominator N m s x i)]
  exact Finset.sum_le_sum fun i _ ↦
    retained_summand_le_reduced N m hN (by omega) hmN s hs x hx i

end RegularBoundary

end Yamagami
