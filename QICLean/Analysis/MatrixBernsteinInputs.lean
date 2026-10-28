/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixBernsteinScalar
import QICLean.Analysis.TraceExponentialPerturbation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Deterministic matrix inputs of the matrix Bernstein inequality

The matrix Bernstein inequality bounds the largest eigenvalue of a sum of independent,
centred, Hermitian random matrices `Y_k` with `λ_max(Y_k) ≤ R`. Its proof by the matrix
Laplace transform method combines Lieb's concavity theorem with the following deterministic
facts, proved here. Throughout, `‖·‖` is the operator norm and `g` is the Bernstein function
`Real.bernsteinFactor`.

* **Transfer rule.** For Hermitian `Y ≤ R 1` and `θ ≥ 0`,
  `e^{θY} ≤ 1 + θY + g(θ) Y²` in the Loewner order.
* **Logarithm bound.** For `A > 0` and `C ≥ 0` with `A ≤ 1 + C`, `log A ≤ C`.
* **Trace bounds.** `Tr e^M ≤ d e^{‖M‖}` for Hermitian `M` of size `d`, and
  `e^{θt} ≤ Tr e^{θS}` for `θ ≥ 0` whenever `S` has an eigenvalue at least `t`.
* **Rayleigh quotients.** For Hermitian `S` and a nonzero vector `x`,
  `exp(⟨x, Sx⟩ / ⟨x, x⟩) ≤ Tr e^S`.

## Main results

* `Matrix.IsHermitian.exp_smul_le_one_add_add_bernsteinFactor_smul_sq`
* `Matrix.PosDef.log_le_of_le_one_add`
* `Matrix.IsHermitian.re_trace_exp_le_card_mul_exp_norm`
* `Matrix.IsHermitian.exp_mul_le_re_trace_exp_smul_of_not_le`
* `Matrix.IsHermitian.exp_re_dotProduct_div_le_re_trace_exp`

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. 12 (2012) 389–434, §2.4–§2.5, Proposition 3.1, Corollary 3.7,
  Lemma 6.7.
* J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*,
  Found. Trends Mach. Learn. 8 (2015), Proposition 2.1.4, equation (2.1.18),
  Proposition 3.2.1, Lemma 6.6.2.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exponential of `θ S` as the functional calculus of `x ↦ e^{θx}` at `S`. -/
lemma IsHermitian.exp_smul_eq_cfc {S : Matrix n n ℂ} (hS : S.IsHermitian) (θ : ℝ) :
    NormedSpace.exp (θ • S) = cfc (fun x ↦ Real.exp (θ * x)) S := by
  rw [← CFC.real_exp_eq_normedSpace_exp (hS.smul (IsSelfAdjoint.all θ)).isSelfAdjoint]
  exact (cfc_comp_smul θ Real.exp S).symm

/-- **Transfer of the Bernstein bound.** For Hermitian `Y ≤ R 1` with `R > 0` and for
`θ ≥ 0`, `e^{θY} ≤ 1 + θY + g(θ) Y²` in the Loewner order. This is the semidefinite bound
in the proof of Tropp 2012, Lemma 6.7, and of Tropp 2015, Lemma 6.6.2, obtained from
the scalar bound by the transfer rule (Tropp 2015, Proposition 2.1.4). -/
theorem IsHermitian.exp_smul_le_one_add_add_bernsteinFactor_smul_sq {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) {R θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ) (hYR : Y ≤ R • 1) :
    NormedSpace.exp (θ • Y) ≤ 1 + θ • Y + Real.bernsteinFactor R θ • Y ^ 2 := by
  have hspec : ∀ x ∈ spectrum ℝ Y, x ≤ R := by
    rw [← Algebra.algebraMap_eq_smul_one] at hYR
    exact (le_algebraMap_iff_spectrum_le (a := Y) hY.isSelfAdjoint).mp hYR
  have hrhs : cfc (fun x ↦ 1 + θ * x + Real.bernsteinFactor R θ * x ^ 2) Y =
      1 + θ • Y + Real.bernsteinFactor R θ • Y ^ 2 := by
    rw [cfc_add .., cfc_add .., cfc_const_one ℝ Y, cfc_const_mul .., cfc_const_mul ..,
      cfc_pow .., cfc_id' ℝ Y]
  rw [hY.exp_smul_eq_cfc, ← hrhs]
  exact cfc_mono fun x hx ↦
    Real.exp_mul_le_one_add_add_bernsteinFactor_mul_sq hR hθ (hspec x hx)

/-- **Logarithm of a perturbed identity.** For positive definite `A` and positive
semidefinite `C` with `A ≤ 1 + C`, `log A ≤ C`. The logarithm is operator monotone
(Tropp 2012, equation (2.8); Tropp 2015, equation (2.1.18)), and `log(1 + C) ≤ C` by the
transfer rule applied to `log y ≤ y - 1`. This is the step from the matrix moment
generating function to the cumulant generating function in Tropp 2015, Lemma 6.6.2. -/
theorem PosDef.log_le_of_le_one_add {A C : Matrix n n ℂ} (hA : A.PosDef) (hC : C.PosSemidef)
    (hAC : A ≤ 1 + C) : CFC.log A ≤ C := by
  have h1 : CFC.log A ≤ CFC.log (1 + C) := CFC.log_le_log hAC hA.isStrictlyPositive
  refine h1.trans ?_
  have hsa : IsSelfAdjoint (1 + C) := (isHermitian_one.add hC.isHermitian).isSelfAdjoint
  have hone : (1 : Matrix n n ℂ) ≤ 1 + C := le_add_of_nonneg_right hC.nonneg
  have hspec : ∀ y ∈ spectrum ℝ (1 + C), 1 ≤ y := by
    rw [← map_one (algebraMap ℝ (Matrix n n ℂ))] at hone
    exact (algebraMap_le_iff_le_spectrum (a := 1 + C) hsa).mp hone
  have hsub : cfc (fun y : ℝ ↦ y - 1) (1 + C) = C := by
    rw [cfc_sub (R := ℝ) (fun y ↦ y) (fun _ ↦ 1) (1 + C), cfc_id' ℝ (1 + C),
      cfc_const_one ℝ (1 + C)]
    abel
  calc CFC.log (1 + C) = cfc Real.log (1 + C) := rfl
    _ ≤ cfc (fun y : ℝ ↦ y - 1) (1 + C) :=
        cfc_mono (fun y hy ↦ Real.log_le_sub_one_of_pos (by linarith [hspec y hy]))
          (Real.continuousOn_log.mono fun y hy ↦ by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hspec y hy])
    _ = C := hsub

/-- For Hermitian `M ≤ c 1` of size `d`, `Tr e^M ≤ d e^c`. This is the bound of the trace
by the dimension times the largest eigenvalue in Tropp 2012, proof of Corollary 3.7. -/
theorem IsHermitian.re_trace_exp_le_card_mul_exp_of_le {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {c : ℝ} (hMc : M ≤ c • 1) :
    (NormedSpace.exp M).trace.re ≤ Fintype.card n * Real.exp c := by
  have hc : (c • (1 : Matrix n n ℂ)).IsHermitian := isHermitian_one.smul (IsSelfAdjoint.all c)
  refine (hM.re_trace_exp_le hc hMc).trans_eq ?_
  have := exp_add_smul_one (0 : Matrix n n ℂ) c
  rw [zero_add, NormedSpace.exp_zero] at this
  rw [this, trace_smul, trace_one, Complex.real_smul, Complex.re_ofReal_mul]
  simp [mul_comm]

/-- For Hermitian `M` of size `d`, `Tr e^M ≤ d e^{‖M‖}` with `‖M‖` the operator norm
(Tropp 2012, proof of Corollary 3.7). -/
theorem IsHermitian.re_trace_exp_le_card_mul_exp_norm {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (NormedSpace.exp M).trace.re ≤ Fintype.card n * Real.exp ‖M‖ := by
  refine hM.re_trace_exp_le_card_mul_exp_of_le ?_
  simpa [Algebra.algebraMap_eq_smul_one] using hM.isSelfAdjoint.le_algebraMap_norm_self

/-- The trace of `e^{θS}` is `∑ᵢ e^{θλᵢ}` over the eigenvalues `λᵢ` of `S`. -/
theorem IsHermitian.re_trace_exp_smul_eq_sum {S : Matrix n n ℂ} (hS : S.IsHermitian) (θ : ℝ) :
    (NormedSpace.exp (θ • S)).trace.re = ∑ i, Real.exp (θ * hS.eigenvalues i) := by
  rw [hS.exp_smul_eq_cfc, hS.cfc_eq]
  exact hS.trace_cfc_eq_sum_re _

/-- If some eigenvalue of the Hermitian matrix `S` is at least `t`, then
`e^{θt} ≤ Tr e^{θS}` for `θ ≥ 0`. This is the bound `e^{λ_max(θY)} ≤ Tr e^{θY}` in the
proof of Tropp 2012, Proposition 3.1 (Tropp 2015, Proposition 3.2.1). -/
theorem IsHermitian.exp_mul_le_re_trace_exp_smul {S : Matrix n n ℂ} (hS : S.IsHermitian)
    {θ t : ℝ} (hθ : 0 ≤ θ) {i : n} (hi : t ≤ hS.eigenvalues i) :
    Real.exp (θ * t) ≤ (NormedSpace.exp (θ • S)).trace.re := by
  rw [hS.re_trace_exp_smul_eq_sum]
  calc Real.exp (θ * t) ≤ Real.exp (θ * hS.eigenvalues i) := by gcongr
    _ ≤ ∑ j, Real.exp (θ * hS.eigenvalues j) :=
      Finset.single_le_sum (f := fun j ↦ Real.exp (θ * hS.eigenvalues j))
        (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i)

/-- If the Hermitian matrix `S` does not satisfy `S ≤ t 1`, then `e^{θt} ≤ Tr e^{θS}` for
`θ ≥ 0` (Tropp 2012, proof of Proposition 3.1). -/
theorem IsHermitian.exp_mul_le_re_trace_exp_smul_of_not_le {S : Matrix n n ℂ}
    (hS : S.IsHermitian) {θ t : ℝ} (hθ : 0 ≤ θ) (hSt : ¬ S ≤ t • 1) :
    Real.exp (θ * t) ≤ (NormedSpace.exp (θ • S)).trace.re := by
  rw [← Algebra.algebraMap_eq_smul_one, le_algebraMap_iff_spectrum_le (a := S) hS.isSelfAdjoint,
    hS.spectrum_real_eq_range_eigenvalues] at hSt
  push Not at hSt
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hSt
  exact hS.exp_mul_le_re_trace_exp_smul hθ hi.le

omit [DecidableEq n] in
/-- The real part of `x* x` is the sum of the squared moduli of the entries of `x`. -/
lemma re_star_dotProduct_self_eq_sum (x : n → ℂ) :
    (star x ⬝ᵥ x).re = ∑ i, Complex.normSq (x i) := by
  simp [dotProduct, Complex.re_sum, Complex.normSq_apply]

/-- **Rayleigh quotients and the trace exponential.** For Hermitian `S` and a nonzero vector
`x`, `exp(⟨x, Sx⟩ / ⟨x, x⟩) ≤ Tr e^S`. In the eigenbasis of `S` the Rayleigh quotient is
a convex combination of eigenvalues, so convexity of the exponential bounds its exponential
by the same combination of `e^{λᵢ}`, which is at most `∑ᵢ e^{λᵢ}`. Combined with the
Rayleigh-quotient bound for the largest eigenvalue, this is `e^{λ_max(S)} ≤ Tr e^S` from
Tropp 2012, proof of Proposition 3.1, and the variational argument after Tropp 2015,
equation (2.1.28). -/
theorem IsHermitian.exp_re_dotProduct_div_le_re_trace_exp {S : Matrix n n ℂ}
    (hS : S.IsHermitian) {x : n → ℂ} (hx : x ≠ 0) :
    Real.exp ((star x ⬝ᵥ (S *ᵥ x)).re / (star x ⬝ᵥ x).re) ≤
      (NormedSpace.exp S).trace.re := by
  set U : Matrix n n ℂ := (hS.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set c : n → ℂ := star U *ᵥ x with hc
  have hUU : U * star U = 1 := by rw [hUdef]; exact Unitary.coe_mul_star_self _
  have hstar : star x ᵥ* U = star c := by
    rw [hc, star_mulVec, star_eq_conjTranspose, conjTranspose_conjTranspose]
  have hquad : star x ⬝ᵥ (S *ᵥ x) = ∑ i, (hS.eigenvalues i : ℂ) * Complex.normSq (c i) := by
    conv_lhs => rw [hS.spectral_form]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hstar, ← hc]
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.normSq_eq_conj_mul_self]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [RCLike.star_def]; ring
  have hnorm : star x ⬝ᵥ x = star c ⬝ᵥ c := by
    rw [← hstar, ← dotProduct_mulVec, hc, mulVec_mulVec, hUU, one_mulVec]
  set N := (star x ⬝ᵥ x).re with hN
  have hNsum : N = ∑ i, Complex.normSq (c i) := by
    rw [hN, hnorm, re_star_dotProduct_self_eq_sum]
  have hNpos : 0 < N := by
    rw [hN, re_star_dotProduct_self_eq_sum]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr hj)
      (Finset.single_le_sum (f := fun i ↦ Complex.normSq (x i))
        (fun i _ ↦ Complex.normSq_nonneg _) (Finset.mem_univ j))
  set p : n → ℝ := fun i ↦ Complex.normSq (c i) / N with hp
  have hp0 : ∀ i ∈ Finset.univ, 0 ≤ p i := fun i _ ↦ div_nonneg (Complex.normSq_nonneg _) hNpos.le
  have hp1 : ∑ i, p i = 1 := by
    rw [hp]; simp only; rw [← Finset.sum_div, ← hNsum, div_self hNpos.ne']
  have hp_le : ∀ i, p i ≤ 1 := fun i ↦ hp1 ▸
    Finset.single_le_sum (f := p) hp0 (Finset.mem_univ i)
  have hre : (star x ⬝ᵥ (S *ᵥ x)).re / N = ∑ i, p i • hS.eigenvalues i := by
    rw [hquad, Complex.re_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re, hp, smul_eq_mul]; ring
  rw [hre, hS.re_trace_exp_eq_sum]
  calc Real.exp (∑ i, p i • hS.eigenvalues i) ≤ ∑ i, p i • Real.exp (hS.eigenvalues i) :=
        convexOn_exp.map_sum_le hp0 hp1 fun i _ ↦ Set.mem_univ _
    _ ≤ ∑ i, Real.exp (hS.eigenvalues i) := Finset.sum_le_sum fun i _ ↦ by
        rw [smul_eq_mul]
        exact mul_le_of_le_one_left (Real.exp_pos _).le (hp_le i)

/-- For Hermitian `S` and a unit vector `w`, `exp ⟨w, Sw⟩ ≤ Tr e^S`. -/
theorem IsHermitian.exp_re_dotProduct_le_re_trace_exp {S : Matrix n n ℂ}
    (hS : S.IsHermitian) {w : n → ℂ} (hw : star w ⬝ᵥ w = 1) :
    Real.exp (star w ⬝ᵥ (S *ᵥ w)).re ≤ (NormedSpace.exp S).trace.re := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  simpa [hw] using hS.exp_re_dotProduct_div_le_re_trace_exp hw0

end Matrix
