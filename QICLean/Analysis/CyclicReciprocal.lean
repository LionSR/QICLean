/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.StrictCombination
import Mathlib.Analysis.Fourier.ZMod

/-!
# Yamagami's cyclic reciprocal functional

This file begins the source-faithful formalization of the variational cyclic
inequality used for Choi-type positive maps.  It defines the forward-window
functional of Yamagami, records its elementary projective and orientation
properties, and proves the centered open-disk estimate in Lemma 6 of
Yamagami, *Cyclic Inequalities*, Proc. Amer. Math. Soc. 118 (1993), 521--527,
specialized to the stride `l = 1` needed by Wolf's Choi-type maps.

The source inequality is stated for strictly positive coordinates.  At the
projective boundary Yamagami treats a formal `0 / 0` as an indeterminate limit.
The definitions below are algebraically total because division in Lean is
total; no theorem in this file identifies that convention with Yamagami's
boundary analysis, and the full cyclic inequality is not claimed here.
-/

open scoped BigOperators

namespace CyclicReciprocal

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

/-- A nonnegative nonzero vector normalizes to the standard simplex. -/
theorem normalize_mem_stdSimplex (x : ZMod d → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hsum : 0 < ∑ i, x i) : normalize d x ∈ stdSimplex ℝ (ZMod d) := by
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

/-- Yamagami, Lemma 6, specialized to stride `l = 1`: every nonconstant
Fourier eigenvalue lies in the open disk with center `s / 2` and radius
`s / 2`. -/
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
