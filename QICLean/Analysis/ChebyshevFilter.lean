/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Chebyshev polynomials for spectral filters

For a natural degree and a real argument at least one, the Chebyshev polynomial
has an exponential lower bound in the square root of the half-angle ratio.
The proof uses the hyperbolic-cosine formula and the existing logarithmic
inequality to compare the inverse hyperbolic cosine with that square root.
Affine rescaling gives an exactly normalized polynomial of the requested degree
with exponential decay on the upper interval and a lower bound on the left.
Degree zero, the endpoint one and singleton upper intervals are included.

References: AKLV, arXiv:1301.1162v1, lines 561–571; ALVV, arXiv:1602.08828v2,
equation `eq:cheb-1b`, lines 839–843.
-/

namespace Polynomial.Chebyshev

/-- AKLV, arXiv:1301.1162v1, source lines 561–571; ALVV,
arXiv:1602.08828v2, eq:cheb-1b, source lines 839–843.
The endpoint x = 1 and degree zero are included. -/
theorem half_exp_sqrt_le_eval_T (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (1 / 2 : ℝ) * Real.exp
      (2 * (n : ℝ) * Real.sqrt ((x - 1) / (x + 1))) ≤
        (T ℝ (n : ℤ)).eval x := by
  have hcompare : 2 * Real.sqrt ((x - 1) / (x + 1)) ≤ Real.arcosh x := by
    let r := Real.sqrt ((x - 1) / (x + 1))
    have hden : 0 < x + 1 := by linarith
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrsq : r ^ 2 = (x - 1) / (x + 1) :=
      Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hx) hden.le)
    have hr1 : r < 1 := by
      nlinarith [(div_lt_one hden).mpr (show x - 1 < x + 1 by linarith)]
    have hrmul : r ^ 2 * (x + 1) = x - 1 := (eq_div_iff hden.ne').mp hrsq
    let y := (1 + r) / (1 - r)
    have hypos : 0 < y := div_pos (by linarith) (sub_pos.mpr hr1)
    have hy1 : 1 ≤ y := (le_div_iff₀ (sub_pos.mpr hr1)).mpr (by linarith)
    have hcosh : Real.cosh (Real.log y) = x := by
      rw [Real.cosh_log hypos]
      dsimp only [y]
      field_simp [(sub_pos.mpr hr1).ne', (show 0 < 1 + r by linarith).ne']
      nlinarith only [hrmul]
    have hlog : Real.log y = Real.arcosh x :=
      (Real.arcosh_cosh (Real.log_nonneg hy1)).symm.trans (congrArg Real.arcosh hcosh)
    have hseries : r ≤ (1 / 2 : ℝ) * Real.log y := by
      simpa using Real.sum_range_le_log_div hr0 hr1 1
    exact (show 2 * r ≤ Real.arcosh x by linarith only [hseries, hlog])
  have hT : Real.cosh ((n : ℝ) * Real.arcosh x) = (T ℝ (n : ℤ)).eval x := by
    simpa only [T_real_cosh, Int.cast_natCast] using
      congrArg (fun z : ℝ ↦ (T ℝ (n : ℤ)).eval z) (Real.cosh_arcosh hx)
  have hexp : Real.exp (2 * (n : ℝ) * Real.sqrt ((x - 1) / (x + 1))) ≤
      Real.exp ((n : ℝ) * Real.arcosh x) :=
    Real.exp_le_exp.mpr (by
      nlinarith only [mul_le_mul_of_nonneg_left hcompare (Nat.cast_nonneg n)])
  rw [← hT, Real.cosh_eq]
  linarith only [hexp, (Real.exp_pos (-((n : ℝ) * Real.arcosh x))).le]

/-- The normalized interval polynomial of AKLV, arXiv:1301.1162v1,
source lines 541–583, with the left-hand lower bound used in ALVV,
arXiv:1602.08828v2, thm:Cheby-AGSP item 2. This scalar statement
includes degree zero and a singleton upper interval. -/
theorem exists_interval_shrinking_polynomial (n : ℕ) {a b u : ℝ}
    (hab : a < b) (hbu : b ≤ u) :
    ∃ p : ℝ[X], p.natDegree = n ∧ p.eval a = 1 ∧
      (∀ x : ℝ, x ≤ a → 1 ≤ p.eval x) ∧
      ∀ x : ℝ, x ∈ Set.Icc b u →
        |p.eval x| ≤ 2 * Real.exp
          (-2 * (n : ℝ) * Real.sqrt ((b - a) / (u - a))) := by
  rcases lt_or_eq_of_le hbu with hbu | rfl
  · have hden : 0 < u - b := sub_pos.mpr hbu
    have hua : 0 < u - a := sub_pos.mpr (hab.trans hbu)
    let f : ℝ[X] := Polynomial.C ((u + b) / (u - b)) + Polynomial.C (-2 / (u - b)) * X
    have hf_eval (x : ℝ) : f.eval x = (u + b - 2 * x) / (u - b) := by
      simp only [f, eval_add, eval_C, eval_mul, eval_X]
      ring
    have hf_degree : f.natDegree = 1 := by
      simpa only [f, natDegree_C_add] using
        natDegree_C_mul_X (-2 / (u - b)) (div_ne_zero (by norm_num) hden.ne')
    have hfa : 1 < f.eval a := (hf_eval a).symm ▸
      (lt_div_iff₀ hden).mpr (by linarith)
    have hf_mono (x y : ℝ) (hxy : x ≤ y) : f.eval y ≤ f.eval x :=
      (hf_eval y).trans_le ((div_le_div_of_nonneg_right
        (show u + b - 2 * y ≤ u + b - 2 * x by linarith) hden.le).trans_eq
          (hf_eval x).symm)
    have hf_interval (x : ℝ) (hx : x ∈ Set.Icc b u) : |f.eval x| ≤ 1 :=
      (hf_eval x).symm ▸ abs_le.mpr
        ⟨(le_div_iff₀ hden).mpr (by linarith [hx.2]),
          (div_le_iff₀ hden).mpr (by linarith [hx.1])⟩
    have hf_scaled : f.eval a * (u - b) = u + b - 2 * a :=
      (eq_div_iff hden.ne').mp (hf_eval a)
    have hf_ratio : (f.eval a - 1) / (f.eval a + 1) = (b - a) / (u - a) :=
      (div_eq_div_iff (show f.eval a + 1 ≠ 0 by linarith) hua.ne').mpr
        (by nlinarith only [hf_scaled])
    let d := (T ℝ (n : ℤ)).eval (f.eval a)
    have hd : 0 < d := lt_of_lt_of_le zero_lt_one (one_le_eval_T_real (n : ℤ) hfa.le)
    let p : ℝ[X] := d⁻¹ • (T ℝ (n : ℤ)).comp f
    have hp_eval (x : ℝ) : p.eval x = (T ℝ (n : ℤ)).eval (f.eval x) / d := by
      simp only [p, eval_smul, smul_eq_mul, eval_comp, div_eq_mul_inv, mul_comm]
    have hp_degree : p.natDegree = n := by
      simpa only [natDegree_comp, natDegree_T, Int.natAbs_natCast, hf_degree, mul_one] using
        natDegree_smul ((T ℝ (n : ℤ)).comp f) (inv_ne_zero hd.ne')
    have hpa : p.eval a = 1 := by rw [hp_eval, div_self hd.ne']
    have hT_eval (y : ℝ) (hy : 1 ≤ y) :
        Real.cosh ((n : ℝ) * Real.arcosh y) = (T ℝ (n : ℤ)).eval y := by
      simpa only [T_real_cosh, Int.cast_natCast] using
        congrArg (fun z : ℝ ↦ (T ℝ (n : ℤ)).eval z) (Real.cosh_arcosh hy)
    refine ⟨p, hp_degree, hpa, ?_, ?_⟩
    · intro x hx
      have hfx : f.eval a ≤ f.eval x := hf_mono x a hx
      have hfx1 : 1 ≤ f.eval x := hfa.le.trans hfx
      rw [hp_eval, le_div_iff₀ hd, one_mul]
      change (T ℝ (n : ℤ)).eval (f.eval a) ≤ (T ℝ (n : ℤ)).eval (f.eval x)
      rw [← hT_eval (f.eval a) hfa.le, ← hT_eval (f.eval x) hfx1]
      exact Real.cosh_strictMonoOn.monotoneOn
        (mul_nonneg (Nat.cast_nonneg n) (Real.arcosh_nonneg hfa.le))
        (mul_nonneg (Nat.cast_nonneg n) (Real.arcosh_nonneg hfx1))
        (mul_le_mul_of_nonneg_left
          ((Real.arcosh_le_arcosh (zero_lt_one.trans_le hfa.le)
            (zero_lt_one.trans_le hfx1)).mpr hfx) (Nat.cast_nonneg n))
    · have hdlower : (1 / 2 : ℝ) * Real.exp
          (2 * (n : ℝ) * Real.sqrt ((b - a) / (u - a))) ≤ d := by
        simpa only [hf_ratio] using half_exp_sqrt_le_eval_T n hfa.le
      have hdinv : 1 / d ≤ 2 * Real.exp
          (-2 * (n : ℝ) * Real.sqrt ((b - a) / (u - a))) := by
        simpa only [neg_mul, Real.exp_neg, div_eq_mul_inv] using
          (div_le_div_iff₀ hd (Real.exp_pos
            (2 * (n : ℝ) * Real.sqrt ((b - a) / (u - a))))).mpr
              (show 1 * Real.exp (2 * (n : ℝ) *
                Real.sqrt ((b - a) / (u - a))) ≤ 2 * d by
                  nlinarith only [hdlower])
      intro x hx
      rw [hp_eval, abs_div, abs_of_pos hd]
      exact (div_le_div_of_nonneg_right
        (abs_eval_T_real_le_one (n : ℤ) (hf_interval x hx)) hd.le).trans hdinv
  · have hden : 0 < b - a := sub_pos.mpr hab
    let g : ℝ[X] := Polynomial.C (b / (b - a)) + Polynomial.C (-1 / (b - a)) * X
    have hg_eval (x : ℝ) : g.eval x = (b - x) / (b - a) := by
      simp only [g, eval_add, eval_C, eval_mul, eval_X]
      ring
    have hg_degree : g.natDegree = 1 := by
      simpa only [g, natDegree_C_add] using
        natDegree_C_mul_X (-1 / (b - a)) (div_ne_zero (by norm_num) hden.ne')
    refine ⟨g ^ n, ?_, ?_, ?_, ?_⟩
    · simp only [natDegree_pow, hg_degree, mul_one]
    · simp only [eval_pow, hg_eval, div_self hden.ne', one_pow]
    · intro x hx
      rw [eval_pow, hg_eval]
      exact one_le_pow₀ ((le_div_iff₀ hden).mpr (by linarith))
    · intro x hx
      have hxb : x = b := le_antisymm hx.2 hx.1
      subst x
      by_cases hn : n = 0
      · simp only [hn, pow_zero, eval_one, abs_one, Nat.cast_zero, mul_zero,
          zero_mul, Real.exp_zero, mul_one]
        norm_num
      · simp only [eval_pow, hg_eval, sub_self, zero_div, zero_pow hn, abs_zero]
        positivity

end Polynomial.Chebyshev
