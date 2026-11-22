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

Near the normalization point the same polynomial loses at most a linear amount: for `x ≤ b`,
`p(x) ≥ 1 - n |x - a| / √((b - a) (u - a))`. The proof compares `T_n` with its tangent at the
normalization point, through the monotonicity of `sinh (n s) / sinh s`. The explicit polynomial
of ALVV, Definition `def:Cheby-AGSP`, shows that this slope cannot carry the exponentially small
factor printed in Theorem `thm:Cheby-AGSP`, item 2.

**Local fix (slope of item 2):** the printed decrease `O(k |λ - η₀| √Δ / (γ ‖H‖))` of ALVV,
arXiv:1602.08828v2, lines 822–824, is replaced by `k |λ - η₀| / √(γ (‖H‖ - η₀))`; the printed form
fails for large `k` (`eval_T_div_eval_T_le_two_mul_exp`). Documented in
`docs/paper-gaps/alvv16_chebyshev_near_ground_slope.tex`.

References: AKLV, arXiv:1301.1162v1, lines 561–571; ALVV, arXiv:1602.08828v2,
equation `eq:cheb-1b`, lines 839–843, and Theorem `thm:Cheby-AGSP`, item 2, lines 822–824 and
844–846.
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

/-- The ratio `sinh (n s) / sinh s` is monotone for `s ≥ 0`, written without division.
Supporting estimate for ALVV, arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`, item 2,
lines 844–846. -/
private theorem sinh_nat_mul_mul_sinh_le (n : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.sinh (n * s) * Real.sinh t ≤ Real.sinh (n * t) * Real.sinh s := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht : 0 ≤ t := hs.trans hst
    have hss : 0 ≤ Real.sinh s := Real.sinh_nonneg_iff.mpr hs
    have hst' : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht
    have hnt : 0 ≤ Real.sinh (n * t) :=
      Real.sinh_nonneg_iff.mpr (mul_nonneg (Nat.cast_nonneg n) ht)
    have hcs : Real.cosh s ≤ Real.cosh t := Real.cosh_le_cosh.mpr (by
      rw [abs_of_nonneg hs, abs_of_nonneg ht]; exact hst)
    have hcn : Real.cosh (n * s) ≤ Real.cosh (n * t) := Real.cosh_le_cosh.mpr (by
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hs),
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) ht)]
      exact mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg n))
    have hcs0 : 0 ≤ Real.cosh s := (Real.cosh_pos s).le
    push_cast
    rw [add_mul, add_mul, one_mul, one_mul, Real.sinh_add, Real.sinh_add]
    nlinarith [mul_le_mul_of_nonneg_right ih hcs0, mul_le_mul_of_nonneg_left hcs
      (mul_nonneg hnt hss), mul_le_mul_of_nonneg_right hcn (mul_nonneg hss hst')]

/-- Convexity of `cosh (n s)` against `cosh s`, measured at the right endpoint `t`: in the
variable `y = cosh s`, the chord of `T_n` on `[cosh s, cosh t]` has slope at most
`n sinh (n t) / sinh t`. Supporting estimate for ALVV, arXiv:1602.08828v2,
Theorem `thm:Cheby-AGSP`, item 2, lines 844–846. -/
private theorem sinh_mul_cosh_nat_mul_sub_le (n : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.sinh t * (Real.cosh (n * t) - Real.cosh (n * s)) ≤
      n * Real.sinh (n * t) * (Real.cosh t - Real.cosh s) := by
  let h : ℝ → ℝ := fun x ↦ n * Real.sinh (n * t) * Real.cosh x - Real.sinh t * Real.cosh (n * x)
  have hderiv (x : ℝ) : HasDerivAt h
      (n * Real.sinh (n * t) * Real.sinh x - Real.sinh t * (Real.sinh (n * x) * (n * 1))) x := by
    have h1 := (Real.hasDerivAt_cosh x).const_mul (n * Real.sinh (n * t))
    have h2 := ((Real.hasDerivAt_cosh (n * x)).comp x
      ((hasDerivAt_id x).const_mul (n : ℝ))).const_mul (Real.sinh t)
    exact h1.sub h2
  have hmono : MonotoneOn h (Set.Icc 0 t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      (fun x _ ↦ (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hderiv x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hderiv x).deriv]
    have := sinh_nat_mul_mul_sinh_le n hx.1.le hx.2.le
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have := hmono ⟨hs, hst⟩ ⟨hs.trans hst, le_rfl⟩ hst
  simp only [h] at this
  linarith

/-- **First-order lower bound for a Chebyshev polynomial on `[1, ∞)`.** For `1 ≤ y ≤ y₀`, the
decrease of `T_n` from `y₀` to `y` is at most `n T_n(y₀) / √(y₀² - 1)` times `y₀ - y`.
This is the scalar estimate behind ALVV, arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`,
item 2, lines 844–846, in the corrected form of the module's local fix. -/
theorem sqrt_mul_eval_T_sub_le (n : ℕ) {y y₀ : ℝ} (hy : 1 ≤ y) (hyy₀ : y ≤ y₀) :
    √(y₀ ^ 2 - 1) * ((T ℝ (n : ℤ)).eval y₀ - (T ℝ (n : ℤ)).eval y) ≤
      n * (y₀ - y) * (T ℝ (n : ℤ)).eval y₀ := by
  have hy₀ : 1 ≤ y₀ := hy.trans hyy₀
  have hT (z : ℝ) (hz : 1 ≤ z) :
      (T ℝ (n : ℤ)).eval z = Real.cosh (n * Real.arcosh z) := by
    simpa only [T_real_cosh, Int.cast_natCast] using
      (congrArg (fun w : ℝ ↦ (T ℝ (n : ℤ)).eval w) (Real.cosh_arcosh hz)).symm
  have hmain := sinh_mul_cosh_nat_mul_sub_le n (Real.arcosh_nonneg hy)
    ((Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr hyy₀)
  rw [Real.sinh_arcosh hy₀, Real.cosh_arcosh hy₀, Real.cosh_arcosh hy] at hmain
  rw [hT y₀ hy₀, hT y hy]
  have hsc := (Real.sinh_lt_cosh (x := n * Real.arcosh y₀)).le
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hsc (mul_nonneg hn (sub_nonneg.mpr hyy₀))]

/-- Tangent-line inequality for `cosh` at the right endpoint `t ≥ s`. Used to bound the source
polynomial of ALVV, arXiv:1602.08828v2, Definition `def:Cheby-AGSP`, lines 795–801, from
above. -/
private theorem cosh_sub_cosh_le_sinh_mul {s t : ℝ} (hst : s ≤ t) :
    Real.cosh t - Real.cosh s ≤ Real.sinh t * (t - s) := by
  let g : ℝ → ℝ := fun x ↦ Real.sinh t * x - Real.cosh x
  have hderiv (x : ℝ) : HasDerivAt g (Real.sinh t * 1 - Real.sinh x) x :=
    ((hasDerivAt_id x).const_mul (Real.sinh t)).sub (Real.hasDerivAt_cosh x)
  have hmono : MonotoneOn g (Set.Icc s t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc s t)
      (fun x _ ↦ (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hderiv x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hderiv x).deriv, mul_one, sub_nonneg]
    exact Real.sinh_le_sinh.mpr hx.2.le
  have := hmono ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  simp only [g] at this
  linarith

/-- **The near-ground lower bound with the corrected slope.** The normalized interval polynomial
of `exists_interval_shrinking_polynomial` also satisfies, for every `x ≤ b`,
`1 - n |x - a| / √((b - a) (u - a)) ≤ p(x)`.

This is ALVV, arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`, item 2, lines 822–824, with
`a = η₀`, `b = η₁`, `u = ‖H‖` and `n = k`, on the whole interval `x ≤ η₁`, which contains the
printed range `λ ≤ η₀ + γ / k`. The decrease is the corrected one of the module's local fix:
there is no factor `√Δ`, and `γ ‖H‖` becomes `√(γ (‖H‖ - η₀))`. -/
theorem exists_interval_shrinking_polynomial_one_sub_le (n : ℕ) {a b u : ℝ}
    (hab : a < b) (hbu : b ≤ u) :
    ∃ p : ℝ[X], p.natDegree = n ∧ p.eval a = 1 ∧
      (∀ x : ℝ, x ≤ a → 1 ≤ p.eval x) ∧
      (∀ x : ℝ, x ≤ b → 1 - n * |x - a| / √((b - a) * (u - a)) ≤ p.eval x) ∧
      ∀ x : ℝ, x ∈ Set.Icc b u →
        |p.eval x| ≤ 2 * Real.exp
          (-2 * (n : ℝ) * Real.sqrt ((b - a) / (u - a))) := by
  have hnear_left (p : ℝ[X]) (hleft : ∀ x : ℝ, x ≤ a → 1 ≤ p.eval x) (x : ℝ) (hxa : x ≤ a) :
      1 - n * |x - a| / √((b - a) * (u - a)) ≤ p.eval x :=
    (sub_le_self _ (by positivity)).trans (hleft x hxa)
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
    have hleft : ∀ x : ℝ, x ≤ a → 1 ≤ p.eval x := by
      intro x hx
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
    refine ⟨p, hp_degree, hpa, hleft, ?_, ?_⟩
    · intro x hxb
      rcases le_total x a with hxa | hax
      · exact hnear_left p hleft x hxa
      set R := √((b - a) * (u - a)) with hRdef
      have hR : 0 < R := Real.sqrt_pos.mpr (mul_pos (sub_pos.mpr hab) hua)
      have hR2 : R ^ 2 = (b - a) * (u - a) :=
        Real.sq_sqrt (mul_pos (sub_pos.mpr hab) hua).le
      have hfx1 : 1 ≤ f.eval x := (hf_eval x).symm ▸ (le_div_iff₀ hden).mpr (by linarith)
      have hsq : f.eval a ^ 2 - 1 = (2 * R / (u - b)) ^ 2 := by
        rw [hf_eval, div_pow, div_pow, mul_pow, hR2]
        field_simp
        ring
      have hsqrt : √(f.eval a ^ 2 - 1) = 2 * R / (u - b) := by
        rw [hsq, Real.sqrt_sq (by positivity)]
      have key := sqrt_mul_eval_T_sub_le n hfx1 (hf_mono a x hax)
      rw [hsqrt] at key
      have hgap : f.eval a - f.eval x = 2 / (u - b) * (x - a) := by
        rw [hf_eval, hf_eval]
        field_simp
        ring
      have key' : 2 / (u - b) * (R * (d - (T ℝ (n : ℤ)).eval (f.eval x))) ≤
          2 / (u - b) * (n * (x - a) * d) := by
        have e1 : 2 * R / (u - b) * (d - (T ℝ (n : ℤ)).eval (f.eval x)) =
            2 / (u - b) * (R * (d - (T ℝ (n : ℤ)).eval (f.eval x))) := by ring
        have e2 : (n : ℝ) * (f.eval a - f.eval x) * d = 2 / (u - b) * (n * (x - a) * d) := by
          rw [hgap]
          ring
        linarith [key, e1, e2]
      have key'' := le_of_mul_le_mul_left key' (by positivity)
      have hdiv : d - (T ℝ (n : ℤ)).eval (f.eval x) ≤ n * (x - a) * d / R :=
        (le_div_iff₀ hR).mpr (by linarith)
      rw [hp_eval, abs_of_nonneg (sub_nonneg.mpr hax), le_div_iff₀ hd]
      have e3 : (1 - n * (x - a) / R) * d = d - n * (x - a) * d / R := by ring
      linarith
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
    have hleft : ∀ x : ℝ, x ≤ a → 1 ≤ (g ^ n).eval x := by
      intro x hx
      rw [eval_pow, hg_eval]
      exact one_le_pow₀ ((le_div_iff₀ hden).mpr (by linarith))
    refine ⟨g ^ n, ?_, ?_, hleft, ?_, ?_⟩
    · simp only [natDegree_pow, hg_degree, mul_one]
    · simp only [eval_pow, hg_eval, div_self hden.ne', one_pow]
    · intro x hxb
      rcases le_total x a with hxa | hax
      · exact hnear_left _ hleft x hxa
      rw [Real.sqrt_mul_self hden.le, abs_of_nonneg (sub_nonneg.mpr hax), eval_pow, hg_eval]
      have ht : -2 ≤ -((x - a) / (b - a)) := by
        rw [neg_le_neg_iff, div_le_iff₀ hden]
        linarith
      have hB := one_add_mul_le_pow ht n
      have e1 : (b - x) / (b - a) = 1 + -((x - a) / (b - a)) := by
        field_simp
        ring
      rw [e1]
      calc 1 - n * (x - a) / (b - a) = 1 + n * -((x - a) / (b - a)) := by ring
        _ ≤ _ := hB
    · intro x hx
      have hxb : x = b := le_antisymm hx.2 hx.1
      subst x
      by_cases hn : n = 0
      · simp only [hn, pow_zero, eval_one, abs_one, Nat.cast_zero, mul_zero,
          zero_mul, Real.exp_zero, mul_one]
        norm_num
      · simp only [eval_pow, hg_eval, sub_self, zero_div, zero_pow hn, abs_zero]
        positivity

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
  obtain ⟨p, hdeg, hpa, hleft, -, hbound⟩ :=
    exists_interval_shrinking_polynomial_one_sub_le n hab hbu
  exact ⟨p, hdeg, hpa, hleft, hbound⟩

/-- **The printed near-ground slope fails** (ALVV, arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`,
item 2, lines 822–824 and Definition `def:Cheby-AGSP`, lines 795–801). Let
`Q_k(x) = T_k(2 (x - η₁)/(u - η₁) - 1)` with `η₀ < η₁ < u`, and `γ = η₁ - η₀`. For every
`k ≥ 1`, the normalized polynomial `P_k = Q_k / Q_k(η₀)` satisfies
`P_k(η₀ + γ / k) ≤ 2 exp (-√(γ / (u - η₀)))`.

The right side does not depend on `k`, and it is below one once `γ / (u - η₀) > (log 2)²`.
The printed lower bound `1 - O(k |λ - η₀| √Δ / (γ ‖H‖))` at `λ = η₀ + γ / k` tends to one,
since `√Δ = 2 exp (-2 k √(γ / (‖H‖ - η₀)))`. Hence no constant makes it hold for all `k`. -/
theorem eval_T_div_eval_T_le_two_mul_exp {k : ℕ} (hk : 1 ≤ k) {η₀ η₁ u : ℝ}
    (h01 : η₀ < η₁) (h1u : η₁ < u) :
    (T ℝ (k : ℤ)).eval (2 * (η₀ + (η₁ - η₀) / k - η₁) / (u - η₁) - 1) /
        (T ℝ (k : ℤ)).eval (2 * (η₀ - η₁) / (u - η₁) - 1) ≤
      2 * Real.exp (-√((η₁ - η₀) / (u - η₀))) := by
  have hden : 0 < u - η₁ := sub_pos.mpr h1u
  have hua : 0 < u - η₀ := sub_pos.mpr (h01.trans h1u)
  have hγ : 0 < η₁ - η₀ := sub_pos.mpr h01
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set x₁ := η₀ + (η₁ - η₀) / k with hx₁
  set y := (u + η₁ - 2 * x₁) / (u - η₁) with hy
  set y₀ := (u + η₁ - 2 * η₀) / (u - η₁) with hy₀
  have hx₁b : x₁ ≤ η₁ := by
    have : (η₁ - η₀) / k ≤ η₁ - η₀ := div_le_self hγ.le hk1
    linarith
  have hneg (x : ℝ) : 2 * (x - η₁) / (u - η₁) - 1 = -((u + η₁ - 2 * x) / (u - η₁)) := by
    field_simp
    ring
  rw [hneg, hneg, T_eval_neg, T_eval_neg, mul_div_mul_left _ _ (by
    exact_mod_cast Units.ne_zero _)]
  have hx₁a : η₀ ≤ x₁ := by
    have : 0 ≤ (η₁ - η₀) / k := div_nonneg hγ.le hkpos.le
    linarith
  have hy1 : 1 ≤ y := (le_div_iff₀ hden).mpr (by linarith)
  have hyy₀ : y ≤ y₀ := div_le_div_of_nonneg_right (by linarith) hden.le
  have hy₀1 : 1 ≤ y₀ := hy1.trans hyy₀
  have hT (z : ℝ) (hz : 1 ≤ z) :
      (T ℝ (k : ℤ)).eval z = Real.cosh (k * Real.arcosh z) := by
    simpa only [T_real_cosh, Int.cast_natCast] using
      (congrArg (fun w : ℝ ↦ (T ℝ (k : ℤ)).eval w) (Real.cosh_arcosh hz)).symm
  set s := Real.arcosh y with hs
  set s₀ := Real.arcosh y₀ with hs₀
  have hs0 : 0 ≤ s := Real.arcosh_nonneg hy1
  have hss₀ : s ≤ s₀ := (Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr hyy₀
  rw [hT y hy1, hT y₀ hy₀1]
  -- `cosh (k s) / cosh (k s₀) ≤ 2 exp (-(k (s₀ - s)))`
  have hratio : Real.cosh (k * s) / Real.cosh (k * s₀) ≤ 2 * Real.exp (-(k * (s₀ - s))) := by
    have hnum : Real.cosh (k * s) ≤ Real.exp (k * s) := by
      rw [Real.cosh_eq]
      have : Real.exp (-(k * s)) ≤ Real.exp (k * s) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have hden' : Real.exp (k * s₀) / 2 ≤ Real.cosh (k * s₀) := by
      rw [Real.cosh_eq]
      linarith [Real.exp_pos (-(k * s₀))]
    rw [div_le_iff₀ (Real.cosh_pos _)]
    calc Real.cosh (k * s) ≤ Real.exp (k * s) := hnum
      _ = 2 * Real.exp (-(k * (s₀ - s))) * (Real.exp (k * s₀) / 2) := by
        rw [show 2 * Real.exp (-(k * (s₀ - s))) * (Real.exp (k * s₀) / 2) =
          Real.exp (-(k * (s₀ - s)) + k * s₀) by rw [Real.exp_add]; ring]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hden' (by positivity)
  refine hratio.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) zero_le_two)
  rw [neg_le_neg_iff]
  set R := √((η₁ - η₀) * (u - η₀)) with hRdef
  have hR : 0 < R := Real.sqrt_pos.mpr (mul_pos hγ hua)
  have hR2 : R ^ 2 = (η₁ - η₀) * (u - η₀) := Real.sq_sqrt (mul_pos hγ hua).le
  have hsq : y₀ ^ 2 - 1 = (2 * R / (u - η₁)) ^ 2 := by
    rw [hy₀, div_pow, div_pow, mul_pow, hR2]
    field_simp
    ring
  have htan := cosh_sub_cosh_le_sinh_mul hss₀
  rw [Real.cosh_arcosh hy₀1, Real.cosh_arcosh hy1, Real.sinh_arcosh hy₀1, hsq,
    Real.sqrt_sq (by positivity)] at htan
  have hgap : y₀ - y = 2 / (u - η₁) * ((η₁ - η₀) / k) := by
    rw [hy₀, hy, hx₁]
    field_simp
    ring
  rw [hgap] at htan
  have hmul : (η₁ - η₀) ≤ k * R * (s₀ - s) := by
    have h2 : 2 / (u - η₁) * ((η₁ - η₀) / k) ≤ 2 / (u - η₁) * (R * (s₀ - s)) := by
      linarith [show 2 * R / (u - η₁) * (s₀ - s) = 2 / (u - η₁) * (R * (s₀ - s)) by ring]
    have h3 := le_of_mul_le_mul_left h2 (by positivity)
    rw [div_le_iff₀ hkpos] at h3
    linarith
  have hsqrt : √((η₁ - η₀) / (u - η₀)) * R = η₁ - η₀ := by
    rw [hRdef, ← Real.sqrt_mul (div_nonneg hγ.le hua.le),
      show (η₁ - η₀) / (u - η₀) * ((η₁ - η₀) * (u - η₀)) = (η₁ - η₀) * (η₁ - η₀) by
        field_simp,
      Real.sqrt_mul_self hγ.le]
  have hfinal : √((η₁ - η₀) / (u - η₀)) * R ≤ (k * (s₀ - s)) * R := by
    rw [hsqrt]
    linarith
  exact le_of_mul_le_mul_right hfinal hR

end Polynomial.Chebyshev
