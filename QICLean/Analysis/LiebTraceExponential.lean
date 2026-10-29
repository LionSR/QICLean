/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.KleinInequality
import QICLean.Analysis.RelativeEntropyResolventIntegral
import QICLean.Channel.Schwarz.RelativeEntropyDataProcessing
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Lieb's concavity theorem for the trace exponential

Let `H` be a Hermitian matrix. Lieb's theorem states that the map
`A ↦ Re tr exp (H + log A)` is concave on the positive definite matrices.

The proof follows Tropp. Write `D(X‖A) = Re tr X (log X - log A)` for the quantum relative
entropy, without trace normalization. For positive definite `X` and `M = H + log A`,
`D(X‖e^M) = D(X‖A) - Re tr X H`, and the unnormalized Klein inequality
`D(X‖Y) ≥ Re tr X - Re tr Y` gives the variational inequality
`Re tr X H - D(X‖A) + Re tr X ≤ Re tr e^M`, with equality at `X = e^M`. The left side is
jointly concave in `(X, A)` by joint convexity of relative entropy, and evaluating it at the
convex combination of the two maximizers yields concavity without taking a supremum.

## Main results

* `re_trace_sub_re_trace_le_quantumRelativeEntropy`: the unnormalized Klein inequality
  `Re tr X - Re tr Y ≤ D(X‖Y)` for positive definite `X` and `Y`.
* `quantumRelativeEntropy_exp_add_log`: `D(X‖exp (H + log A)) = D(X‖A) - Re tr X H`.
* `re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_le`: the variational inequality.
* `re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_exp_add_log`: its equality case.
* `isGreatest_re_trace_exp_add_log`: the variational formula for `Re tr exp (H + log A)`.
* `concaveOn_re_trace_exp_add_log`: Lieb's concavity theorem.

## References

* E. H. Lieb, *Convex trace functions and the Wigner-Yanase-Dyson conjecture*,
  Adv. Math. 11 (1973) 267–288, Theorem 6.
* J. A. Tropp, *From joint convexity of quantum relative entropy to a concavity theorem of
  Lieb*, Proc. Amer. Math. Soc. 140 (2012) 1757–1760.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Scaling the second argument of the relative entropy by `c > 0` shifts it by
`-(log c) Re tr X`, since `log (c Y) = (log c) 1 + log Y`. -/
theorem quantumRelativeEntropy_smul_right (X : Matrix n n ℂ) {Y : Matrix n n ℂ}
    (hY : Y.PosDef) {c : ℝ} (hc : 0 < c) :
    quantumRelativeEntropy X (c • Y) =
      quantumRelativeEntropy X Y - Real.log c * (X.trace).re := by
  rw [quantumRelativeEntropy_eq_trace_mul_log_sub, quantumRelativeEntropy_eq_trace_mul_log_sub,
    CFC.log_smul' Y hc hY.isStrictlyPositive, Algebra.algebraMap_eq_smul_one, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
    Complex.real_smul, Complex.re_ofReal_mul]
  ring

/-- **Klein's inequality without trace normalization.** For positive definite `X` and `Y`,
`Re tr X - Re tr Y ≤ D(X‖Y)`.

Normalizing `X = a ρ` and `Y = b σ` with `a = tr X` and `b = tr Y`, the relative entropy is
`D(X‖Y) = a D(ρ‖σ) + a log (a / b) ≥ a log (a / b) ≥ a - b`, by Klein's inequality for
the density matrices `ρ` and `σ` and the scalar bound `log x ≤ x - 1`. -/
theorem re_trace_sub_re_trace_le_quantumRelativeEntropy {X Y : Matrix n n ℂ}
    (hX : X.PosDef) (hY : Y.PosDef) :
    (X.trace).re - (Y.trace).re ≤ quantumRelativeEntropy X Y := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [quantumRelativeEntropy, Matrix.trace]
  set a := (X.trace).re with ha_def
  set b := (Y.trace).re with hb_def
  have hXtr := Complex.pos_iff.mp hX.trace_pos
  have hYtr := Complex.pos_iff.mp hY.trace_pos
  have ha : 0 < a := hXtr.1
  have hb : 0 < b := hYtr.1
  have hXa : X.trace = (a : ℂ) := Complex.ext (by simp [a]) (by simp [hXtr.2])
  have hYb : Y.trace = (b : ℂ) := Complex.ext (by simp [b]) (by simp [hYtr.2])
  set ρ := a⁻¹ • X with hρ
  set σ := b⁻¹ • Y with hσ
  have hρ_pd : ρ.PosDef := hX.smul (inv_pos.mpr ha)
  have hσ_pd : σ.PosDef := hY.smul (inv_pos.mpr hb)
  have hρ_tr : ρ.trace = 1 := by
    rw [hρ, Matrix.trace_smul, hXa, Complex.real_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ ha.ne', Complex.ofReal_one]
  have hσ_tr : σ.trace = 1 := by
    rw [hσ, Matrix.trace_smul, hYb, Complex.real_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hb.ne', Complex.ofReal_one]
  have hklein : 0 ≤ quantumRelativeEntropy ρ σ :=
    quantumRelativeEntropy_nonneg hρ_pd.posSemidef hρ_tr hσ_pd.posSemidef hσ_tr
      (Matrix.isUnit_iff_isUnit_det _ |>.mp hσ_pd.isUnit)
  -- `X = a ρ` and `(a / b) Y = a σ`.
  have hXρ : X = a • ρ := by rw [hρ, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have hYσ : (a / b) • Y = a • σ := by rw [hσ, smul_smul, div_eq_mul_inv]
  have hY_eq : Y = (b / a) • ((a / b) • Y) := by
    rw [smul_smul, show b / a * (a / b) = 1 by field_simp, one_smul]
  have hscale : quantumRelativeEntropy X ((a / b) • Y) = a * quantumRelativeEntropy ρ σ := by
    rw [hYσ, hXρ, Matrix.quantumRelativeEntropy_smul_posDef hρ_pd hσ_pd ha]
  have hD : quantumRelativeEntropy X Y =
      a * quantumRelativeEntropy ρ σ - Real.log (b / a) * a := by
    conv_lhs => rw [hY_eq]
    rw [quantumRelativeEntropy_smul_right X (hY.smul (div_pos ha hb)) (div_pos hb ha), hscale]
  have hlog : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hlog' : Real.log (b / a) * a ≤ b - a := by
    have := mul_le_mul_of_nonneg_right hlog ha.le
    rwa [sub_mul, div_mul_cancel₀ _ ha.ne', one_mul] at this
  rw [hD]
  nlinarith [mul_nonneg ha.le hklein]

/-- The exponential of a Hermitian matrix is positive definite. -/
theorem Matrix.IsHermitian.posDef_exp {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (NormedSpace.exp M).PosDef := by
  rw [← CFC.real_exp_eq_normedSpace_exp hM.isSelfAdjoint]
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    ((cfc_isStrictlyPositive_iff Real.exp M Real.continuous_exp.continuousOn
      hM.isSelfAdjoint).mpr fun x _ => Real.exp_pos x)

/-- For Hermitian `H`, `D(X‖exp (H + log A)) = D(X‖A) - Re tr X H`, because
`log exp (H + log A) = H + log A`. -/
theorem quantumRelativeEntropy_exp_add_log (X A : Matrix n n ℂ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) :
    quantumRelativeEntropy X (NormedSpace.exp (H + CFC.log A)) =
      quantumRelativeEntropy X A - (X * H).trace.re := by
  rw [quantumRelativeEntropy_eq_trace_mul_log_sub, quantumRelativeEntropy_eq_trace_mul_log_sub,
    CFC.log_exp _ (hH.isSelfAdjoint.add IsSelfAdjoint.log), Matrix.mul_add, Matrix.trace_add,
    Complex.add_re]
  ring

/-- **Variational inequality for the trace exponential** (Tropp 2012, Lemma; Lieb 1973).
For Hermitian `H` and positive definite `X`,
`Re tr X H - D(X‖A) + Re tr X ≤ Re tr exp (H + log A)`.

With `Y = exp (H + log A)`, the left side minus the right side equals
`Re tr X - Re tr Y - D(X‖Y)`, which is nonpositive by the unnormalized Klein inequality. -/
theorem re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_le {X : Matrix n n ℂ}
    (hX : X.PosDef) (A : Matrix n n ℂ) {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (X * H).trace.re - quantumRelativeEntropy X A + (X.trace).re ≤
      (NormedSpace.exp (H + CFC.log A)).trace.re := by
  have h := re_trace_sub_re_trace_le_quantumRelativeEntropy hX
    (hH.add (IsSelfAdjoint.log (a := A)).isHermitian).posDef_exp
  rw [quantumRelativeEntropy_exp_add_log X A hH] at h
  linarith

/-- **Equality case of the variational inequality.** At `X = exp (H + log A)` the
variational expression equals `Re tr exp (H + log A)`. -/
theorem re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_exp_add_log
    (A : Matrix n n ℂ) {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (NormedSpace.exp (H + CFC.log A) * H).trace.re -
        quantumRelativeEntropy (NormedSpace.exp (H + CFC.log A)) A +
        (NormedSpace.exp (H + CFC.log A)).trace.re =
      (NormedSpace.exp (H + CFC.log A)).trace.re := by
  have h := quantumRelativeEntropy_exp_add_log (NormedSpace.exp (H + CFC.log A)) A hH
  rw [quantumRelativeEntropy_self] at h
  linarith

/-- **Variational formula for the trace exponential.** For Hermitian `H`,
`Re tr exp (H + log A)` is the largest value of `Re tr X H - D(X‖A) + Re tr X` over positive
definite `X`, attained at `X = exp (H + log A)`. -/
theorem isGreatest_re_trace_exp_add_log (A : Matrix n n ℂ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) :
    IsGreatest
      ((fun X : Matrix n n ℂ => (X * H).trace.re - quantumRelativeEntropy X A + (X.trace).re) ''
        {X | X.PosDef})
      (NormedSpace.exp (H + CFC.log A)).trace.re := by
  refine ⟨⟨_, (hH.add (IsSelfAdjoint.log (a := A)).isHermitian).posDef_exp,
    re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_exp_add_log A hH⟩, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_le hX A hH

omit [Fintype n] [DecidableEq n] in
/-- The positive definite matrices form a convex set. -/
theorem convex_setOf_posDef : Convex ℝ {A : Matrix n n ℂ | A.PosDef} := by
  rw [convex_iff_forall_pos]
  intro A hA B hB a b ha hb _
  exact (Matrix.PosDef.smul hA ha).add (Matrix.PosDef.smul hB hb)

/-- **Lieb's concavity theorem** (Lieb 1973, Theorem 6; proof of Tropp 2012). For Hermitian
`H`, the map `A ↦ Re tr exp (H + log A)` is concave on the positive definite matrices.

For `A = a A₁ + b A₂`, put `Xᵢ = exp (H + log Aᵢ)` and `X = a X₁ + b X₂`. The variational
inequality at `(X, A)`, joint convexity of relative entropy, linearity of the trace terms in
`X`, and the equality cases at `(Xᵢ, Aᵢ)` give
`Re tr exp (H + log A) ≥ a Re tr exp (H + log A₁) + b Re tr exp (H + log A₂)`. -/
theorem concaveOn_re_trace_exp_add_log {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef}
      (fun A => (NormedSpace.exp (H + CFC.log A)).trace.re) := by
  refine ⟨convex_setOf_posDef, ?_⟩
  intro A₁ hA₁ A₂ hA₂ a b ha hb hab
  set X₁ := NormedSpace.exp (H + CFC.log A₁)
  set X₂ := NormedSpace.exp (H + CFC.log A₂)
  have hX₁ : X₁.PosDef := (hH.add (IsSelfAdjoint.log (a := A₁)).isHermitian).posDef_exp
  have hX₂ : X₂.PosDef := (hH.add (IsSelfAdjoint.log (a := A₂)).isHermitian).posDef_exp
  have hX : (a • X₁ + b • X₂).PosDef := convex_setOf_posDef hX₁ hX₂ ha hb hab
  -- Joint convexity of relative entropy at the two maximizers.
  have hjoint := (TNLean.RelativeEntropyConvexity.convexOn_quantumRelativeEntropy_index (N := n)).2
    (x := (X₁, A₁)) (y := (X₂, A₂)) ⟨hX₁, hA₁⟩ ⟨hX₂, hA₂⟩ ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hjoint
  -- The variational inequality at the convex combination.
  have hvar :=
    re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_le hX (a • A₁ + b • A₂) hH
  -- The equality cases at the two maximizers.
  have heq₁ : (X₁ * H).trace.re = quantumRelativeEntropy X₁ A₁ := by
    linarith [re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_exp_add_log A₁ hH]
  have heq₂ : (X₂ * H).trace.re = quantumRelativeEntropy X₂ A₂ := by
    linarith [re_trace_mul_sub_quantumRelativeEntropy_add_re_trace_exp_add_log A₂ hH]
  -- Linearity of the trace terms in `X`.
  have hlinH : ((a • X₁ + b • X₂) * H).trace.re =
      a * (X₁ * H).trace.re + b * (X₂ * H).trace.re := by
    simp [Matrix.add_mul, Matrix.trace_add, Matrix.trace_smul, Complex.real_smul]
  have hlin : (a • X₁ + b • X₂).trace.re = a * X₁.trace.re + b * X₂.trace.re := by
    simp [Matrix.trace_add, Matrix.trace_smul, Complex.real_smul]
  rw [heq₁, heq₂] at hlinH
  simp only [smul_eq_mul] at hjoint ⊢
  linarith
