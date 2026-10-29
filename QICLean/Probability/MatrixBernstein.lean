/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.MatrixCumulantSubadditivity
import QICLean.Analysis.HermitianDilation
import Mathlib.Probability.IdentDistrib

/-!
# The matrix Bernstein inequality

Let `Z_k` be independent centred random complex `d₁ × d₂` matrices with `‖Z_k‖ ≤ R` almost
surely, and put `σ² = max (‖∑ₖ E Z_k Z_k*‖, ‖∑ₖ E Z_k* Z_k‖)`. The matrix Bernstein inequality of
Tropp 2012, Theorem 1.6, states that for `t ≥ 0`,
`P(‖∑ₖ Z_k‖ ≥ t) ≤ (d₁ + d₂) exp (-(t²/2) / (σ² + Rt/3))`.

The proof is the matrix Laplace transform method. For centred Hermitian summands `Y_k` with
`‖Y_k‖ ≤ R`, the transfer rule gives `E e^{θY_k} ≤ 1 + g(θ) E Y_k²` with the Bernstein function
`g`, so `log E e^{θY_k} ≤ g(θ) E Y_k²`; subadditivity of the matrix cumulant generating functions
and the dimension bound for the trace exponential give
`E Tr e^{θ ∑ₖ Y_k} ≤ d e^{g(θ) σ²}`, and Markov's inequality with the optimal `θ` gives the
Hermitian tail bound (Tropp 2012, Theorem 6.1). The rectangular case is the Hermitian case for
the Hermitian dilations `𝒟(Z_k)`, which have norm `‖Z_k‖` and squares
`diag (Z_k Z_k*, Z_k* Z_k)`. The average form for independent identically distributed
summands, quoted by Landau, Vazirani and Vidick, follows by rescaling.

**Scope restriction (bounded Hermitian summands):** Tropp 2012, Theorem 6.1, assumes only
the one-sided bound `λ_max(Y_k) ≤ R`. The Hermitian theorems of this module,
`integral_re_trace_exp_smul_sum_le` and `measureReal_exists_le_mem_spectrum_sum_le`, assume
the two-sided bound `‖Y_k‖ ≤ R`, which is the hypothesis of the rectangular theorem and all
that its proof uses. The rectangular theorem and the average form carry the hypotheses of their
sources. Documented in `docs/paper-gaps/tropp12_bounded_summands_scope.tex`.

The index types of the matrices are assumed nonempty in the rectangular theorem and the average
form. With both index types empty, every matrix is zero and the event `‖∑ₖ Z_k‖ ≥ 0` is certain,
while the bound reads `0`; Tropp and Landau–Vazirani–Vidick take positive dimensions.

## Main results

* `Matrix.integral_re_trace_exp_smul_sum_le`: the trace moment generating function bound
  `E Tr e^{θ ∑ₖ Y_k} ≤ d e^{g(θ) σ²}` (Tropp 2012, Lemma 6.7 and Corollary 3.7).
* `Matrix.measureReal_exists_le_mem_spectrum_sum_le`: the Hermitian matrix Bernstein inequality
  for summands bounded in norm (Tropp 2012, Theorem 6.1).
* `Matrix.measureReal_le_norm_sum_le`: the rectangular matrix Bernstein inequality
  (Tropp 2012, Theorem 1.6).
* `Matrix.measureReal_le_norm_average_sub_le`: the matrix Bernstein inequality for averages of
  independent identically distributed matrices (Landau–Vazirani–Vidick 2013, Theorem `t:mcb`).

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. 12 (2012) 389–434, Theorems 1.4, 1.6 and 6.1, Corollary 3.7,
  Lemma 6.7.
* J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*,
  Found. Trends Mach. Learn. 8 (2015), Chapter 6.
* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, Theorem `t:mcb` (source lines 616–624).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Markov step of the matrix Laplace transform method.** If `e^{θt} ≤ f` almost surely on
the event `A`, with `f ≥ 0` integrable and `E f ≤ d e^{g(θ) σ²}`, then
`P(A) ≤ d e^{-θt + g(θ) σ²}`, which the choice of `θ` bounds by the Bernstein exponent. -/
private lemma measureReal_le_mul_exp_of_integral_le [IsFiniteMeasure μ] {A : Set Ω} {f : Ω → ℝ}
    (hf0 : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) {d R σsq t θ : ℝ}
    (hA : ∀ᵐ ω ∂μ, ω ∈ A → Real.exp (θ * t) ≤ f ω)
    (hmgf : ∫ ω, f ω ∂μ ≤ d * Real.exp (Real.bernsteinFactor R θ * σsq))
    (hθ : -(θ * t) + Real.bernsteinFactor R θ * σsq ≤ -(t ^ 2 / 2 / (σsq + R * t / 3))) :
    μ.real A ≤ d * Real.exp (-(t ^ 2 / 2 / (σsq + R * t / 3))) := by
  have hle : μ.real A ≤ μ.real {ω | Real.exp (θ * t) ≤ f ω} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hA)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hf0 hfi (Real.exp (θ * t))
  have hpos := Real.exp_pos (θ * t)
  have h1 : μ.real A ≤ d * Real.exp (Real.bernsteinFactor R θ * σsq) / Real.exp (θ * t) := by
    rw [le_div_iff₀ hpos, mul_comm]
    exact (mul_le_mul_of_nonneg_left hle hpos.le).trans (hmarkov.trans hmgf)
  refine h1.trans ?_
  have hd : 0 ≤ d :=
    nonneg_of_mul_nonneg_left ((integral_nonneg_of_ae hf0).trans hmgf) (Real.exp_pos _)
  rw [mul_div_assoc, ← Real.exp_sub]
  gcongr
  linarith

/-- **Trace moment generating function bound** (Tropp 2012, Lemma 6.7 with Lemma 3.4 and the
proof of Corollary 3.7). Let `Y_k` be independent random matrices, almost surely Hermitian,
centred, with `‖Y_k‖ ≤ R` almost surely for some `R > 0`. For `θ ≥ 0`,
`E Tr e^{θ ∑ₖ Y_k} ≤ d e^{g(θ) σ²}` with `σ² = ‖∑ₖ E Y_k²‖`, `g = Real.bernsteinFactor R` and
`d` the dimension.

The transfer rule `e^{θY} ≤ 1 + θY + g(θ) Y²` integrates to `E e^{θY_k} ≤ 1 + g(θ) E Y_k²`,
since the linear term has mean zero; hence `log E e^{θY_k} ≤ g(θ) E Y_k²`. Subadditivity of the
cumulant generating functions, monotonicity of the trace exponential and
`Tr e^M ≤ d e^{‖M‖}` conclude.

**Scope restriction (bounded Hermitian summands):** the two-sided bound `‖Y_k‖ ≤ R` replaces
Tropp's `λ_max(Y_k) ≤ R`; see the module docstring and
`docs/paper-gaps/tropp12_bounded_summands_scope.tex`. -/
theorem integral_re_trace_exp_smul_sum_le [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {Y : ι → Ω → Matrix n n ℂ} (hind : iIndepFun Y μ) (hYm : ∀ k, Measurable (Y k))
    (hY : ∀ k, ∀ᵐ ω ∂μ, (Y k ω).IsHermitian) (hmean : ∀ k, ∫ ω, Y k ω ∂μ = 0) {R : ℝ}
    (hR0 : 0 < R) (hR : ∀ k, ∀ᵐ ω ∂μ, ‖Y k ω‖ ≤ R) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫ ω, (NormedSpace.exp (θ • ∑ k, Y k ω)).trace.re ∂μ ≤
      Fintype.card n * Real.exp (Real.bernsteinFactor R θ * ‖∑ k, ∫ ω, Y k ω ^ 2 ∂μ‖) := by
  set g := Real.bernsteinFactor R θ
  have hg0 : 0 ≤ g := Real.bernsteinFactor_nonneg R θ
  have hθYH : ∀ k, ∀ᵐ ω ∂μ, (θ • Y k ω).IsHermitian := fun k ↦ by
    filter_upwards [hY k] with ω h using h.smul (IsSelfAdjoint.all θ)
  have hθYR : ∀ k, ∀ᵐ ω ∂μ, ‖θ • Y k ω‖ ≤ θ * R := fun k ↦ by
    filter_upwards [hR k] with ω h
    rw [norm_smul_of_nonneg hθ]
    exact mul_le_mul_of_nonneg_left h hθ
  -- subadditivity for the family `θ Y_k`
  have hsub := integral_re_trace_exp_add_sum_le (R := θ * R) (Y := fun k ω ↦ θ • Y k ω)
    (hind.comp (fun _ A ↦ θ • A) fun _ ↦ measurable_const_smul θ)
    (fun k ↦ (hYm k).const_smul θ) hθYH hθYR Finset.univ isHermitian_zero
  simp only [zero_add, ← Finset.smul_sum] at hsub
  refine hsub.trans ?_
  -- the cumulant bound for each summand
  set V := ∑ k, ∫ ω, Y k ω ^ 2 ∂μ with hV
  have hint : ∀ k, Integrable (Y k) μ := fun k ↦
    Integrable.of_bound (hYm k).aestronglyMeasurable R (hR k)
  have hsq_int : ∀ k, Integrable (fun ω ↦ Y k ω ^ 2) μ := fun k ↦ by
    refine Integrable.of_bound ((continuous_pow 2).comp_aestronglyMeasurable
      (hYm k).aestronglyMeasurable) (R ^ 2) ?_
    filter_upwards [hR k] with ω h
    exact (norm_pow_le' _ two_pos).trans (pow_le_pow_left₀ (norm_nonneg _) h 2)
  have hsq_nonneg : ∀ k, 0 ≤ ∫ ω, Y k ω ^ 2 ∂μ := fun k ↦ by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hY k] with ω h using h.isSelfAdjoint.sq_nonneg
  have hexp_int : ∀ k, Integrable (fun ω ↦ NormedSpace.exp (θ • Y k ω)) μ := fun k ↦
    integrable_exp ((hYm k).const_smul θ).aestronglyMeasurable (hθYH k) (hθYR k)
  have hlog : ∀ k, CFC.log (∫ ω, NormedSpace.exp (θ • Y k ω) ∂μ) ≤ g • ∫ ω, Y k ω ^ 2 ∂μ := by
    intro k
    have hupper : ∫ ω, NormedSpace.exp (θ • Y k ω) ∂μ ≤ 1 + g • ∫ ω, Y k ω ^ 2 ∂μ := by
      have hi1 : Integrable (fun ω ↦ (1 : Matrix n n ℂ) + θ • Y k ω) μ :=
        (integrable_const _).add ((hint k).smul θ)
      have hi2 : Integrable (fun ω ↦ g • Y k ω ^ 2) μ := (hsq_int k).smul g
      have hle := integral_mono_ae (g := fun ω ↦ 1 + θ • Y k ω + g • Y k ω ^ 2) (hexp_int k)
        (hi1.add hi2) (by
          filter_upwards [hY k, hR k] with ω h1 h2
          exact h1.exp_smul_le_one_add_add_bernsteinFactor_smul_sq hR0 hθ
            (h1.le_smul_one_of_norm_le h2))
      refine hle.trans_eq ?_
      have hθY : Integrable (fun ω ↦ θ • Y k ω) μ := (hint k).smul θ
      rw [integral_add hi1 hi2, integral_add (integrable_const _) hθY,
        integral_smul, integral_smul, hmean k, integral_const]
      simp
    have hlower : Real.exp (-(θ * R)) • (1 : Matrix n n ℂ) ≤
        ∫ ω, NormedSpace.exp (θ • Y k ω) ∂μ := by
      have hle := integral_mono_ae (integrable_const (Real.exp (-(θ * R)) • (1 : Matrix n n ℂ)))
        (hexp_int k) (by
          filter_upwards [hθYH k, hθYR k] with ω h1 h2 using (h1.exp_mem_Icc_of_norm_le h2).1)
      simpa using hle
    have hpd : (∫ ω, NormedSpace.exp (θ • Y k ω) ∂μ).PosDef :=
      posDef_of_smul_one_le (Real.exp_pos _) hlower
    have hC : (g • ∫ ω, Y k ω ^ 2 ∂μ).PosSemidef :=
      nonneg_iff_posSemidef.mp (smul_nonneg hg0 (hsq_nonneg k))
    exact hpd.log_le_of_le_one_add hC hupper
  have hsum : ∑ k, CFC.log (∫ ω, NormedSpace.exp (θ • Y k ω) ∂μ) ≤ g • V := by
    rw [hV, Finset.smul_sum]
    exact Finset.sum_le_sum fun k _ ↦ hlog k
  have hVH : (g • V).IsHermitian :=
    (nonneg_iff_posSemidef.mp
      (smul_nonneg hg0 (Finset.sum_nonneg fun k _ ↦ hsq_nonneg k))).isHermitian
  have hLH : (∑ k, CFC.log (∫ ω, NormedSpace.exp (θ • Y k ω) ∂μ)).IsHermitian :=
    isSelfAdjoint_sum _ fun k _ ↦ IsSelfAdjoint.log
  calc (NormedSpace.exp (∑ k, CFC.log (∫ ω, NormedSpace.exp (θ • Y k ω) ∂μ))).trace.re
      ≤ (NormedSpace.exp (g • V)).trace.re := hLH.re_trace_exp_le hVH hsum
    _ ≤ Fintype.card n * Real.exp ‖g • V‖ := hVH.re_trace_exp_le_card_mul_exp_norm
    _ = Fintype.card n * Real.exp (g * ‖V‖) := by rw [norm_smul_of_nonneg hg0]

/-- **The Hermitian matrix Bernstein inequality for summands bounded in norm** (Tropp 2012,
Theorem 6.1 and Theorem 1.4). Let `Y_k` be independent random `d × d` matrices, almost surely
Hermitian, centred, with `‖Y_k‖ ≤ R` almost surely, and put `σ² = ‖∑ₖ E Y_k²‖`. For `t ≥ 0`,
the probability that `∑ₖ Y_k` has an eigenvalue at least `t` is at most
`d exp (-(t²/2) / (σ² + Rt/3))`.

**Scope restriction (bounded Hermitian summands):** Tropp assumes only `λ_max(Y_k) ≤ R`; see
the module docstring and `docs/paper-gaps/tropp12_bounded_summands_scope.tex`. -/
theorem measureReal_exists_le_mem_spectrum_sum_le [IsProbabilityMeasure μ] {ι : Type*}
    [Fintype ι] {Y : ι → Ω → Matrix n n ℂ} (hind : iIndepFun Y μ) (hYm : ∀ k, Measurable (Y k))
    (hY : ∀ k, ∀ᵐ ω ∂μ, (Y k ω).IsHermitian) (hmean : ∀ k, ∫ ω, Y k ω ∂μ = 0) {R : ℝ}
    (hR : ∀ k, ∀ᵐ ω ∂μ, ‖Y k ω‖ ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ x ∈ spectrum ℝ (∑ k, Y k ω), t ≤ x} ≤
      Fintype.card n *
        Real.exp (-(t ^ 2 / 2 / (‖∑ k, ∫ ω, Y k ω ^ 2 ∂μ‖ + R * t / 3))) := by
  have hSH : ∀ᵐ ω ∂μ, (∑ k, Y k ω).IsHermitian := by
    filter_upwards [ae_all_iff.mpr hY] with ω hω using isSelfAdjoint_sum _ fun k _ ↦ hω k
  have hSR : ∀ᵐ ω ∂μ, ‖∑ k, Y k ω‖ ≤ Fintype.card ι * R :=
    (ae_norm_sum_le_card_mul hR Finset.univ).mono fun ω h ↦ by rwa [Finset.card_univ] at h
  rcases ht.eq_or_lt with rfl | ht0
  · -- with `t = 0` the bound is at least `1` unless the dimension is zero
    rcases isEmpty_or_nonempty n with hn | hn
    · simp
    · refine measureReal_le_one.trans ?_
      simpa using (Nat.one_le_cast (α := ℝ)).mpr (Fintype.card_pos (α := n))
  rcases le_or_gt R 0 with hR0 | hR0
  · -- with `R ≤ 0` the sum vanishes almost surely, and the event is null
    have hnull : μ {ω | ∃ x ∈ spectrum ℝ (∑ k, Y k ω), t ≤ x} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hSH, hSR] with ω h1 h2
      rintro ⟨x, hx, htx⟩
      have h0 : ‖∑ k, Y k ω‖ < t := h2.trans_lt
        ((mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hR0).trans_lt ht0)
      have hxn : x ≤ ‖∑ k, Y k ω‖ := by
        have := h1.le_smul_one_of_norm_le le_rfl
        rw [← Algebra.algebraMap_eq_smul_one,
          le_algebraMap_iff_spectrum_le (a := ∑ k, Y k ω) h1.isSelfAdjoint] at this
        exact this x hx
      linarith
    rw [measureReal_def, hnull, ENNReal.toReal_zero]
    positivity
  obtain ⟨θ, hθ, hθt⟩ := Real.exists_neg_mul_add_bernsteinFactor_mul_le hR0
    (norm_nonneg (∑ k, ∫ ω, Y k ω ^ 2 ∂μ)) ht
  have hθS : ∀ᵐ ω ∂μ, (θ • ∑ k, Y k ω).IsHermitian := by
    filter_upwards [hSH] with ω h using h.smul (IsSelfAdjoint.all θ)
  refine measureReal_le_mul_exp_of_integral_le
    (f := fun ω ↦ (NormedSpace.exp (θ • ∑ k, Y k ω)).trace.re)
    (by filter_upwards [hθS] with ω h using h.re_trace_exp_nonneg)
    (integrable_re_trace_exp (R := θ * (Fintype.card ι * R))
      (((Finset.measurable_sum _ fun k _ ↦ hYm k).const_smul θ).aestronglyMeasurable) hθS
      (by
        filter_upwards [hSR] with ω h
        rw [norm_smul_of_nonneg hθ]
        exact mul_le_mul_of_nonneg_left h hθ))
    ?_ (integral_re_trace_exp_smul_sum_le hind hYm hY hmean hR0 hR hθ) hθt
  filter_upwards [hSH] with ω h hω
  obtain ⟨x, hx, htx⟩ := hω
  rw [h.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact h.exp_mul_le_re_trace_exp_smul hθ htx

end Matrix

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The rectangular matrix Bernstein inequality** (Tropp 2012, Theorem 1.6). Let `Z_k` be
independent random complex `d₁ × d₂` matrices with `E Z_k = 0` and `‖Z_k‖ ≤ R` almost surely,
and put `σ² = max (‖∑ₖ E Z_k Z_k*‖, ‖∑ₖ E Z_k* Z_k‖)`. For `t ≥ 0`,
`P(‖∑ₖ Z_k‖ ≥ t) ≤ (d₁ + d₂) exp (-(t²/2) / (σ² + Rt/3))`.

As in Tropp's proof, the Hermitian dilations `𝒟(Z_k)` are independent, centred, Hermitian, of
norm `‖Z_k‖`, with `∑ₖ E 𝒟(Z_k)² = diag (∑ₖ E Z_k Z_k*, ∑ₖ E Z_k* Z_k)` of norm `σ²`. The
trace moment generating function bound for the dilations and
`e^{θ‖Z‖} ≤ Tr e^{θ𝒟(Z)}` give the claim by Markov's inequality. The cases `t = 0` and
`R ≤ 0` are immediate. Integrability is not assumed: it follows from the almost sure bound.
The index types are assumed nonempty, see the module docstring. -/
theorem measureReal_le_norm_sum_le [Nonempty (m ⊕ n)] [IsProbabilityMeasure μ] {ι : Type*}
    [Fintype ι] {Z : ι → Ω → Matrix m n ℂ} (hind : iIndepFun Z μ)
    (hZm : ∀ k, Measurable (Z k)) (hmean : ∀ k, ∫ ω, Z k ω ∂μ = 0) {R : ℝ}
    (hR : ∀ k, ∀ᵐ ω ∂μ, ‖Z k ω‖ ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, Z k ω‖} ≤
      (Fintype.card m + Fintype.card n) *
        Real.exp (-(t ^ 2 / 2 / (max ‖∑ k, ∫ ω, Z k ω * (Z k ω)ᴴ ∂μ‖
          ‖∑ k, ∫ ω, (Z k ω)ᴴ * Z k ω ∂μ‖ + R * t / 3))) := by
  set σsq := max ‖∑ k, ∫ ω, Z k ω * (Z k ω)ᴴ ∂μ‖ ‖∑ k, ∫ ω, (Z k ω)ᴴ * Z k ω ∂μ‖
  have hcard : (1 : ℝ) ≤ Fintype.card m + Fintype.card n := by
    have := Fintype.card_pos (α := m ⊕ n)
    rw [Fintype.card_sum] at this
    exact_mod_cast this
  have hSR : ∀ᵐ ω ∂μ, ‖∑ k, Z k ω‖ ≤ Fintype.card ι * R :=
    (ae_norm_sum_le_card_mul hR Finset.univ).mono fun ω h ↦ by rwa [Finset.card_univ] at h
  -- the trivial cases `t = 0` and `R ≤ 0`
  rcases ht.eq_or_lt with rfl | ht0
  · refine measureReal_le_one.trans ?_
    simpa using hcard
  rcases le_or_gt R 0 with hR0 | hR0
  · have hnull : μ {ω | t ≤ ‖∑ k, Z k ω‖} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hSR] with ω h
      simp only [not_le]
      exact h.trans_lt ((mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hR0).trans_lt ht0)
    rw [measureReal_def, hnull, ENNReal.toReal_zero]
    positivity
  -- the Hermitian dilations
  let D : Matrix m n ℂ →L[ℝ] Matrix (m ⊕ n) (m ⊕ n) ℂ := LinearMap.toContinuousLinearMap
    { toFun := hermitianDilation
      map_add' := hermitianDilation_add
      map_smul' := hermitianDilation_smul }
  have hDapp : ∀ Z, D Z = hermitianDilation Z := fun _ ↦ rfl
  have hint : ∀ k, Integrable (Z k) μ := fun k ↦
    Integrable.of_bound (hZm k).aestronglyMeasurable R (hR k)
  set Y : ι → Ω → Matrix (m ⊕ n) (m ⊕ n) ℂ := fun k ω ↦ hermitianDilation (Z k ω) with hYdef
  have hindY : iIndepFun Y μ := hind.comp (fun _ ↦ D) fun _ ↦ D.continuous.measurable
  have hYm : ∀ k, Measurable (Y k) := fun k ↦ D.continuous.measurable.comp (hZm k)
  have hYH : ∀ k, ∀ᵐ ω ∂μ, (Y k ω).IsHermitian := fun k ↦
    Filter.Eventually.of_forall fun ω ↦ isHermitian_hermitianDilation _
  have hYmean : ∀ k, ∫ ω, Y k ω ∂μ = 0 := fun k ↦ by
    simp only [hYdef, ← hDapp]
    rw [D.integral_comp_comm (hint k), hmean k, map_zero]
  have hYR : ∀ k, ∀ᵐ ω ∂μ, ‖Y k ω‖ ≤ R := fun k ↦ by
    filter_upwards [hR k] with ω h
    rwa [hYdef, norm_hermitianDilation]
  -- the variance of the dilations
  let P : Matrix m m ℂ × Matrix n n ℂ →L[ℝ] Matrix (m ⊕ n) (m ⊕ n) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun x ↦ fromBlocks x.1 0 0 x.2
        map_add' := fun x y ↦ by simp [fromBlocks_add]
        map_smul' := fun c x ↦ by simp [fromBlocks_smul] }
  have hPapp : ∀ x, P x = fromBlocks x.1 0 0 x.2 := fun _ ↦ rfl
  have hint1 : ∀ k, Integrable (fun ω ↦ Z k ω * (Z k ω)ᴴ) μ := fun k ↦ by
    refine Integrable.of_bound ((continuous_id.matrix_mul continuous_id.matrix_conjTranspose
      ).comp_aestronglyMeasurable (hZm k).aestronglyMeasurable) (R * R) ?_
    filter_upwards [hR k] with ω h
    refine (l2_opNorm_mul _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    exact mul_self_le_mul_self (norm_nonneg _) h
  have hint2 : ∀ k, Integrable (fun ω ↦ (Z k ω)ᴴ * Z k ω) μ := fun k ↦ by
    refine Integrable.of_bound ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id
      ).comp_aestronglyMeasurable (hZm k).aestronglyMeasurable) (R * R) ?_
    filter_upwards [hR k] with ω h
    refine (l2_opNorm_mul _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    exact mul_self_le_mul_self (norm_nonneg _) h
  have hvar : ‖∑ k, ∫ ω, Y k ω ^ 2 ∂μ‖ = σsq := by
    have hk : ∀ k, ∫ ω, Y k ω ^ 2 ∂μ =
        P (∫ ω, Z k ω * (Z k ω)ᴴ ∂μ, ∫ ω, (Z k ω)ᴴ * Z k ω ∂μ) := fun k ↦ by
      rw [← integral_pair (hint1 k) (hint2 k), ← P.integral_comp_comm ((hint1 k).prodMk (hint2 k))]
      simp only [hYdef, hPapp, hermitianDilation_sq]
    simp_rw [hk]
    rw [← map_sum, hPapp, l2_opNorm_fromBlocks_zero_zero, Prod.fst_sum, Prod.snd_sum]
  obtain ⟨θ, hθ, hθt⟩ := Real.exists_neg_mul_add_bernsteinFactor_mul_le hR0
    (le_max_of_le_left (norm_nonneg _) : 0 ≤ σsq) ht
  have hmgf := integral_re_trace_exp_smul_sum_le hindY hYm hYH hYmean hR0 hYR hθ
  rw [hvar, Fintype.card_sum, Nat.cast_add] at hmgf
  have hSH : ∀ ω, (θ • ∑ k, Y k ω).IsHermitian := fun ω ↦
    (show (∑ k, Y k ω).IsHermitian from
      isSelfAdjoint_sum _ fun k _ ↦ isHermitian_hermitianDilation (Z k ω)).smul
      (IsSelfAdjoint.all θ)
  have hsum : ∀ ω, ∑ k, Y k ω = hermitianDilation (∑ k, Z k ω) := fun ω ↦
    (hermitianDilation_sum _ _).symm
  refine measureReal_le_mul_exp_of_integral_le
    (f := fun ω ↦ (NormedSpace.exp (θ • ∑ k, Y k ω)).trace.re)
    (Filter.Eventually.of_forall fun ω ↦ (hSH ω).re_trace_exp_nonneg)
    (integrable_re_trace_exp (R := θ * (Fintype.card ι * R))
      (((Finset.measurable_sum _ fun k _ ↦ hYm k).const_smul θ).aestronglyMeasurable)
      (Filter.Eventually.of_forall hSH)
      (by
        filter_upwards [hSR] with ω h
        rw [norm_smul_of_nonneg hθ, hsum, norm_hermitianDilation]
        exact mul_le_mul_of_nonneg_left h hθ))
    (Filter.Eventually.of_forall fun ω hω ↦ ?_) hmgf hθt
  rw [hsum]
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hθ)).trans
    (exp_mul_norm_le_re_trace_exp_smul_hermitianDilation _ θ)

end Matrix

namespace Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The matrix Bernstein inequality for averages** (Landau–Vazirani–Vidick,
arXiv:1307.5143v1, Theorem `t:mcb`, source lines 616–624, derived there from Tropp 2012,
Theorem 1.6). Let `X_1, …, X_ℓ` be independent identically distributed random complex
`d × d` matrices with `E X_k = Xbar` and `‖X_k - Xbar‖ ≤ R` almost surely, and put
`σ² = max (‖E (X_1 - Xbar)(X_1 - Xbar)*‖, ‖E (X_1 - Xbar)*(X_1 - Xbar)‖)`. For `ℓ ≥ 1` and `t ≥ 0`,
`P(‖(1/ℓ) ∑ₖ X_k - Xbar‖ ≥ t) ≤ 2d exp (-ℓt² / (2σ² + 2Rt/3))`.

The rescaled summands `Z_k = (X_k - Xbar)/ℓ` are independent and centred, with `‖Z_k‖ ≤ R/ℓ`
and, by identical distribution, variance parameter `σ²/ℓ`; Tropp 2012, Theorem 1.6, with
`t²/2 / (σ²/ℓ + Rt/(3ℓ)) = ℓt² / (2σ² + 2Rt/3)` gives the claim.

**Local fix (operator norms in the variance):** the source prints `σ²` as the maximum of the
two matrices `E (X_i - X)(X_i - X)*` and `E (X_i - X)*(X_i - X)`; the variance parameter of
Tropp 2012, Theorem 1.6, from which the source derives the bound, is the maximum of their
operator norms, which is the reading formalized here. Documented in
`docs/paper-gaps/lvv13_matrix_bernstein_variance_norm.tex`. -/
theorem measureReal_le_norm_average_sub_le [Nonempty d] [IsProbabilityMeasure μ] {ℓ : ℕ}
    [NeZero ℓ] {X : Fin ℓ → Ω → Matrix d d ℂ} (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ) (hXm : ∀ k, Measurable (X k))
    {Xbar : Matrix d d ℂ} (hmean : ∀ k, ∫ ω, X k ω ∂μ = Xbar) {R : ℝ}
    (hR : ∀ k, ∀ᵐ ω ∂μ, ‖X k ω - Xbar‖ ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖(ℓ : ℝ)⁻¹ • ∑ k, X k ω - Xbar‖} ≤
      2 * Fintype.card d *
        Real.exp (-(ℓ * t ^ 2 / (2 * max ‖∫ ω, (X 0 ω - Xbar) * (X 0 ω - Xbar)ᴴ ∂μ‖
          ‖∫ ω, (X 0 ω - Xbar)ᴴ * (X 0 ω - Xbar) ∂μ‖ + 2 * R * t / 3))) := by
  set c : ℝ := (ℓ : ℝ)⁻¹ with hc
  have hℓ : (0 : ℝ) < ℓ := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne ℓ))
  have hc0 : 0 < c := inv_pos.mpr hℓ
  set V₁ := ∫ ω, (X 0 ω - Xbar) * (X 0 ω - Xbar)ᴴ ∂μ
  set V₂ := ∫ ω, (X 0 ω - Xbar)ᴴ * (X 0 ω - Xbar) ∂μ
  set Z : Fin ℓ → Ω → Matrix d d ℂ := fun k ω ↦ c • (X k ω - Xbar) with hZ
  have hcont : Continuous fun A : Matrix d d ℂ ↦ c • (A - Xbar) :=
    (continuous_id.sub continuous_const).const_smul c
  have hindZ : iIndepFun Z μ := hind.comp (fun _ A ↦ c • (A - Xbar)) fun _ ↦ hcont.measurable
  have hZm : ∀ k, Measurable (Z k) := fun k ↦ hcont.measurable.comp (hXm k)
  have hXint : ∀ k, Integrable (X k) μ := fun k ↦ by
    refine Integrable.of_bound (hXm k).aestronglyMeasurable (R + ‖Xbar‖) ?_
    filter_upwards [hR k] with ω h
    calc ‖X k ω‖ = ‖(X k ω - Xbar) + Xbar‖ := by rw [sub_add_cancel]
      _ ≤ ‖X k ω - Xbar‖ + ‖Xbar‖ := norm_add_le _ _
      _ ≤ R + ‖Xbar‖ := by linarith
  have hZmean : ∀ k, ∫ ω, Z k ω ∂μ = 0 := fun k ↦ by
    simp only [hZ]
    rw [integral_smul, integral_sub (hXint k) (integrable_const _), hmean k, integral_const]
    simp
  have hZR : ∀ k, ∀ᵐ ω ∂μ, ‖Z k ω‖ ≤ c * R := fun k ↦ by
    filter_upwards [hR k] with ω h
    simp only [hZ]
    rw [norm_smul_of_nonneg hc0.le]
    exact mul_le_mul_of_nonneg_left h hc0.le
  have hsum : ∀ ω, ∑ k, Z k ω = c • ∑ k, X k ω - Xbar := fun ω ↦ by
    simp only [hZ]
    rw [← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hc,
      inv_mul_cancel₀ hℓ.ne', one_smul]
  -- the variances of the rescaled summands
  have hcstar : ∀ A : Matrix d d ℂ, (c • A)ᴴ = c • Aᴴ := fun A ↦ by
    rw [conjTranspose_smul, star_trivial]
  have hident1 : ∀ k, ∫ ω, (X k ω - Xbar) * (X k ω - Xbar)ᴴ ∂μ = V₁ := fun k ↦
    ((hident k).comp (u := fun A : Matrix d d ℂ ↦ (A - Xbar) * (A - Xbar)ᴴ)
      ((continuous_id.sub continuous_const).matrix_mul
        (continuous_id.sub continuous_const).matrix_conjTranspose).measurable).integral_eq
  have hident2 : ∀ k, ∫ ω, (X k ω - Xbar)ᴴ * (X k ω - Xbar) ∂μ = V₂ := fun k ↦
    ((hident k).comp (u := fun A : Matrix d d ℂ ↦ (A - Xbar)ᴴ * (A - Xbar))
      ((continuous_id.sub continuous_const).matrix_conjTranspose.matrix_mul
        (continuous_id.sub continuous_const)).measurable).integral_eq
  have hvar1 : ∑ k, ∫ ω, Z k ω * (Z k ω)ᴴ ∂μ = c • V₁ := by
    simp only [hZ, hcstar, smul_mul_smul_comm, integral_smul, hident1, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    rw [hc]; field_simp
  have hvar2 : ∑ k, ∫ ω, (Z k ω)ᴴ * Z k ω ∂μ = c • V₂ := by
    simp only [hZ, hcstar, smul_mul_smul_comm, integral_smul, hident2, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    rw [hc]; field_simp
  have h := measureReal_le_norm_sum_le (m := d) (n := d) hindZ hZm hZmean hZR ht
  simp only [hsum, hvar1, hvar2, norm_smul, Real.norm_of_nonneg hc0.le] at h
  refine h.trans_eq ?_
  rw [← mul_max_of_nonneg _ _ hc0.le]
  congr 2
  · ring
  · congr 1
    have hden : c * max ‖V₁‖ ‖V₂‖ + c * R * t / 3 =
        (2 * max ‖V₁‖ ‖V₂‖ + 2 * R * t / 3) / (2 * ℓ) := by
      rw [hc]; field_simp
    rw [hden, div_div_eq_mul_div]
    ring

end Matrix
