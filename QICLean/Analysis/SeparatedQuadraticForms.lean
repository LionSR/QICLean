/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GapPerturbation
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.Linarith

/-!
# Sylvester estimates from separated quadratic forms

A rectangular operator satisfies a dimension-independent Sylvester bound when the real
quadratic forms of the two endomorphisms are separated. Norm attainment for the rectangular
map proves the estimate, including zero maps and zero-dimensional spaces.

These are supporting results for ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines873–886, and the proof of `t:ais`, lines1010–1024.
-/

section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

local instance : CompleteSpace F := FiniteDimensional.complete ℂ F

/-- A nonzero rectangular operator has a unit vector attaining its norm and
satisfying the top eigenvector equation for its Gram operator. Nontriviality
and completeness are derived from the finite-dimensional hypotheses. -/
private theorem exists_unit_norm_eq_and_adjoint_comp_self
    (T : E →L[ℂ] F) (hT : T ≠ 0) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ ∧
      T.adjoint (T x) = ((‖T‖ ^ 2 : ℝ) : ℂ) • x := by
  have : Nontrivial E := (subsingleton_or_nontrivial E).resolve_left fun hE ↦ by
    have : Subsingleton E := hE
    apply hT
    ext z
    change T z = 0
    rw [Subsingleton.elim z 0, map_zero]
  let S : E →L[ℂ] E := T.adjoint ∘L T
  have hS : (S : E →ₗ[ℂ] E).IsSymmetric :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self T).isSymmetric
  have hnegS : ((-S : E →L[ℂ] E) : E →ₗ[ℂ] E).IsSymmetric := by
    intro x y
    change inner ℂ (-((S : E →ₗ[ℂ] E) x)) y =
      inner ℂ x (-((S : E →ₗ[ℂ] E) y))
    simpa only [inner_neg_left, inner_neg_right] using congrArg Neg.neg (hS x y)
  obtain ⟨x, hx, hneg, hmin⟩ :=
    exists_unit_eigenvector_re_inner_le (E := E) (T := -S) hnegS
  have hquad (z : E) : (inner ℂ z (S z)).re = ‖T z‖ ^ 2 :=
    (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right T z).symm
  have hnegQuad (z : E) : (inner ℂ z ((-S) z)).re = -‖T z‖ ^ 2 := by
    simp only [_root_.neg_apply, inner_neg_right, Complex.neg_re, hquad]
  have hupper (z : E) : ‖T z‖ ^ 2 ≤ ‖T x‖ ^ 2 * ‖z‖ ^ 2 := by
    have h := hmin z
    rw [hnegQuad x, hnegQuad z] at h
    nlinarith
  have hnorm : ‖T x‖ = ‖T‖ := by
    apply le_antisymm
    · simpa only [hx, mul_one] using T.le_opNorm x
    · apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg (T x))
      intro z hz
      have h := hupper z
      rw [hz, one_pow, mul_one] at h
      exact le_of_sq_le_sq h (norm_nonneg (T x))
  rw [hnegQuad x] at hneg
  have hSx : S x = ((‖T x‖ ^ 2 : ℝ) : ℂ) • x := by
    simpa only [_root_.neg_apply, Complex.ofReal_neg,
      neg_smul, neg_inj] using hneg
  refine ⟨x, hx, hnorm, ?_⟩
  change S x = ((‖T‖ ^ 2 : ℝ) : ℂ) • x
  simpa only [hnorm] using hSx

/-- A dimension-free Sylvester estimate from real quadratic-form bounds.
No self-adjointness or normality assumption is needed beyond these explicit
bounds. The multiplicative inequality also holds without a positive separation. -/
theorem mul_norm_le_norm_sylvester_of_quadratic_bounds
    (A : F →L[ℂ] F) (B : E →L[ℂ] E) (T : E →L[ℂ] F) (u e : ℝ)
    (hA : ∀ y : F, u * ‖y‖ ^ 2 ≤ (inner ℂ y (A y)).re)
    (hB : ∀ x : E, (inner ℂ x (B x)).re ≤ e * ‖x‖ ^ 2) :
    (u - e) * ‖T‖ ≤ ‖A ∘L T - T ∘L B‖ := by
  by_cases hT : T = 0
  · simp [hT]
  obtain ⟨x, hx, hnorm, htop⟩ := exists_unit_norm_eq_and_adjoint_comp_self T hT
  let y : F := T x
  let R : E →L[ℂ] F := A ∘L T - T ∘L B
  change (u - e) * ‖T‖ ≤ ‖R‖
  have hy : ‖y‖ = ‖T‖ := hnorm
  have htop' : T.adjoint y = ((‖T‖ ^ 2 : ℝ) : ℂ) • x := htop
  have hpair : (inner ℂ y (T (B x))).re =
      ‖T‖ ^ 2 * (inner ℂ x (B x)).re := by
    rw [← ContinuousLinearMap.adjoint_inner_left T (B x) y, htop',
      inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]
  have hsplit : (inner ℂ y (R x)).re =
      (inner ℂ y (A y)).re - ‖T‖ ^ 2 * (inner ℂ x (B x)).re := by
    change (inner ℂ y (A y - T (B x))).re = _
    rw [inner_sub_right, Complex.sub_re, hpair]
  have hlower : (u - e) * ‖T‖ ^ 2 ≤ (inner ℂ y (R x)).re := by
    have ha := hA y
    rw [hy] at ha
    have hb := hB x
    rw [hx, one_pow, mul_one] at hb
    have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖T‖)
    calc
      (u - e) * ‖T‖ ^ 2 = u * ‖T‖ ^ 2 - ‖T‖ ^ 2 * e := by ring
      _ ≤ (inner ℂ y (A y)).re - ‖T‖ ^ 2 * (inner ℂ x (B x)).re :=
        sub_le_sub ha hmul
      _ = (inner ℂ y (R x)).re := hsplit.symm
  have hupper : (inner ℂ y (R x)).re ≤ ‖T‖ * ‖R‖ := by
    calc
      (inner ℂ y (R x)).re ≤ ‖y‖ * ‖R x‖ := re_inner_le_norm (𝕜 := ℂ) y (R x)
      _ ≤ ‖y‖ * (‖R‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (R.le_opNorm x) (norm_nonneg y)
      _ = ‖T‖ * ‖R‖ := by rw [hx, mul_one, hy]
  have hbound := hlower.trans hupper
  have hcancel : ((u - e) * ‖T‖) * ‖T‖ ≤ ‖R‖ * ‖T‖ := by
    calc
      ((u - e) * ‖T‖) * ‖T‖ = (u - e) * ‖T‖ ^ 2 := by ring
      _ ≤ ‖T‖ * ‖R‖ := hbound
      _ = ‖R‖ * ‖T‖ := mul_comm _ _
  exact le_of_mul_le_mul_right hcancel (norm_pos_iff.mpr hT)

/-- A bounded perturbation of the Sylvester equation retains a dimension-free
bound when the quadratic separation exceeds the perturbation norm. This is
the absorption step in the weighted hard-truncation argument supporting ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. The weighted operator
identity and the physical bounds must be derived separately. -/
theorem norm_le_div_of_sylvester_perturbation
    (A V : F →L[ℂ] F) (B : E →L[ℂ] E) (T F0 : E →L[ℂ] F)
    (u e C D : ℝ)
    (hA : ∀ y : F, u * ‖y‖ ^ 2 ≤ (inner ℂ y (A y)).re)
    (hB : ∀ x : E, (inner ℂ x (B x)).re ≤ e * ‖x‖ ^ 2)
    (hV : ‖V‖ ≤ C) (hF0 : ‖F0‖ ≤ D) (hgap : C < u - e)
    (hEq : A ∘L T - T ∘L B = F0 - V ∘L T) :
    ‖T‖ ≤ D / (u - e - C) := by
  have hprod := mul_norm_le_norm_sylvester_of_quadratic_bounds A B T u e hA hB
  rw [hEq] at hprod
  have hcomp : ‖V ∘L T‖ ≤ C * ‖T‖ :=
    (opNorm_comp_le V T).trans
      (mul_le_mul_of_nonneg_right hV (norm_nonneg T))
  have hbound : (u - e) * ‖T‖ ≤ D + C * ‖T‖ :=
    hprod.trans ((norm_sub_le F0 (V ∘L T)).trans (add_le_add hF0 hcomp))
  exact (le_div_iff₀ (sub_pos.mpr hgap)).mpr (by nlinarith only [hbound])
end ContinuousLinearMap
end
