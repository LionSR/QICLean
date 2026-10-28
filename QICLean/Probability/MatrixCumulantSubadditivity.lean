/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LiebTraceExponential
import QICLean.Analysis.MatrixBernsteinInputs
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Subadditivity of matrix cumulant generating functions

For independent random Hermitian matrices `Y_k` and a Hermitian matrix `H`,
`E Tr exp (H + ∑ₖ Y_k) ≤ Tr exp (H + ∑ₖ log E e^{Y_k})`. This is the subadditivity of matrix
cumulant generating functions of Tropp 2012, Lemma 3.4, the probabilistic core of the matrix
Laplace transform method. Its one-variable case, `E Tr exp (H + Y) ≤ Tr exp (H + log E e^Y)`,
is Jensen's inequality for the concave map `A ↦ Tr exp (H + log A)` of Lieb's theorem
(Tropp 2012, Corollary 3.3), applied to `A = e^Y` because `log e^Y = Y`. The general case
follows by induction on the number of summands, integrating out one independent summand at a
time with Fubini's theorem.

Random matrices are measurable maps into the Borel space of matrices, and expectations are
Bochner integrals for the operator norm. The summands are assumed almost surely bounded in
operator norm, which makes every expectation finite; the random matrices `e^{Y_k}` then take
values in a compact Loewner interval `[e^{-R}, e^R]` of positive definite matrices, on which
`log` is continuous and Jensen's inequality applies.

**Scope restriction (bounded summands):** Tropp 2012, Corollary 3.3 and Lemma 3.4, assume only
that the matrix moment generating functions exist. Both theorems of this module assume the
random matrices almost surely bounded in operator norm, the setting of the matrix Bernstein
inequality. Documented in `docs/paper-gaps/tropp12_bounded_summands_scope.tex`.

## Main results

* `Matrix.integral_re_trace_exp_add_le`: the Jensen step (Tropp 2012, Corollary 3.3).
* `Matrix.integral_re_trace_exp_add_sum_le`: subadditivity of matrix cumulant generating
  functions (Tropp 2012, Lemma 3.4).

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. 12 (2012) 389–434, Corollary 3.3 and Lemma 3.4.
* J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*,
  Found. Trends Mach. Learn. 8 (2015), Chapter 3.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For Hermitian `M` of size `d`, `|Tr e^M| ≤ d e^{‖M‖}`. -/
lemma IsHermitian.abs_re_trace_exp_le {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    |(NormedSpace.exp M).trace.re| ≤ Fintype.card n * Real.exp ‖M‖ := by
  rw [abs_of_nonneg hM.re_trace_exp_nonneg]
  exact hM.re_trace_exp_le_card_mul_exp_norm

/-- A Hermitian matrix of operator norm at most `R` satisfies `Y ≤ R 1`. -/
lemma IsHermitian.le_smul_one_of_norm_le {Y : Matrix n n ℂ} (hY : Y.IsHermitian) {R : ℝ}
    (hYR : ‖Y‖ ≤ R) : Y ≤ R • 1 := by
  have h := hY.isSelfAdjoint.le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one] at h
  refine h.trans ?_
  have : (0 : Matrix n n ℂ) ≤ (R - ‖Y‖) • 1 :=
    smul_nonneg (sub_nonneg.mpr hYR) zero_le_one
  rw [sub_smul, sub_nonneg] at this
  exact this

/-- A Hermitian matrix of operator norm at most `R` satisfies `-R 1 ≤ Y`. -/
lemma IsHermitian.neg_smul_one_le_of_norm_le {Y : Matrix n n ℂ} (hY : Y.IsHermitian) {R : ℝ}
    (hYR : ‖Y‖ ≤ R) : (-R) • (1 : Matrix n n ℂ) ≤ Y := by
  have h := hY.neg.le_smul_one_of_norm_le (R := R) (by rwa [norm_neg])
  rw [neg_smul]
  exact neg_le.mp h

/-- A Hermitian matrix in the Loewner interval `[a 1, b 1]` has its spectrum in `[a, b]`. -/
lemma IsHermitian.spectrum_subset_Icc {A : Matrix n n ℂ} (hA : A.IsHermitian) {a b : ℝ}
    (h : A ∈ Set.Icc (a • (1 : Matrix n n ℂ)) (b • 1)) : spectrum ℝ A ⊆ Set.Icc a b := by
  intro x hx
  rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at h
  exact ⟨(algebraMap_le_iff_le_spectrum (a := A) hA.isSelfAdjoint).mp h.1 x hx,
    (le_algebraMap_iff_spectrum_le (a := A) hA.isSelfAdjoint).mp h.2 x hx⟩

/-- For Hermitian `Y` with `‖Y‖ ≤ R`, the exponential `e^Y` lies in the Loewner interval
`[e^{-R} 1, e^R 1]`. -/
lemma IsHermitian.exp_mem_Icc_of_norm_le {Y : Matrix n n ℂ} (hY : Y.IsHermitian) {R : ℝ}
    (hYR : ‖Y‖ ≤ R) : NormedSpace.exp Y ∈
      Set.Icc (Real.exp (-R) • (1 : Matrix n n ℂ)) (Real.exp R • 1) := by
  have hspec := hY.spectrum_subset_Icc
    ⟨hY.neg_smul_one_le_of_norm_le hYR, hY.le_smul_one_of_norm_le hYR⟩
  rw [← CFC.real_exp_eq_normedSpace_exp hY.isSelfAdjoint, ← Algebra.algebraMap_eq_smul_one,
    ← Algebra.algebraMap_eq_smul_one, ← cfc_const (Real.exp (-R)) Y,
    ← cfc_const (Real.exp R) Y]
  exact ⟨cfc_mono fun x hx ↦ Real.exp_le_exp.mpr (hspec hx).1,
    cfc_mono fun x hx ↦ Real.exp_le_exp.mpr (hspec hx).2⟩

omit [Fintype n] in
/-- A matrix bounded below by `a 1` with `a > 0` is positive definite. -/
lemma posDef_of_smul_one_le {A : Matrix n n ℂ} {a : ℝ} (ha : 0 < a)
    (h : a • (1 : Matrix n n ℂ) ≤ A) : A.PosDef := by
  have h1 : (a • (1 : Matrix n n ℂ)).PosDef := PosDef.one.smul ha
  have h2 : (A - a • 1).PosSemidef := h
  simpa using h1.add_posSemidef h2

/-- A Hermitian matrix of operator norm at most `R` satisfies `‖e^Y‖ ≤ e^R`. -/
lemma IsHermitian.norm_exp_le_of_norm_le {Y : Matrix n n ℂ} (hY : Y.IsHermitian) {R : ℝ}
    (hYR : ‖Y‖ ≤ R) : ‖NormedSpace.exp Y‖ ≤ Real.exp R := by
  have hmem := hY.exp_mem_Icc_of_norm_le hYR
  have h0 : 0 ≤ NormedSpace.exp Y :=
    (posDef_of_smul_one_le (Real.exp_pos _) hmem.1).posSemidef.nonneg
  rw [CStarAlgebra.norm_le_iff_le_algebraMap _ (Real.exp_pos R).le h0,
    Algebra.algebraMap_eq_smul_one]
  exact hmem.2

/-- The matrix exponential is continuous. -/
lemma continuous_exp : Continuous (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) := by
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous

/-- The map `A ↦ Tr exp (H + log A)` is continuous on a Loewner interval `[a 1, b 1]` with
`a > 0`, since `log` is continuous on `[a, b]` and the continuous functional calculus is
continuous in the matrix. -/
lemma continuousOn_re_trace_exp_add_log (H : Matrix n n ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun A : Matrix n n ℂ ↦ (NormedSpace.exp (H + CFC.log A)).trace.re)
      (Set.Icc (a • (1 : Matrix n n ℂ)) (b • 1)) := by
  have hlog : ContinuousOn (fun A : Matrix n n ℂ ↦ CFC.log A)
      (Set.Icc (a • (1 : Matrix n n ℂ)) (b • 1)) :=
    ContinuousOn.cfc' isCompact_Icc Real.log continuousOn_id
      (fun A hA ↦ (posDef_of_smul_one_le ha hA.1).isHermitian.spectrum_subset_Icc hA)
      (fun A hA ↦ (posDef_of_smul_one_le ha hA.1).isHermitian.isSelfAdjoint)
      (Real.continuousOn_log.mono fun x hx ↦ by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact (ha.trans_le hx.1).ne')
  exact Complex.continuous_re.comp_continuousOn (continuous_id.matrix_trace.comp_continuousOn
    (continuous_exp.comp_continuousOn (continuousOn_const.add hlog)))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The trace exponential of an almost surely bounded, almost surely Hermitian random matrix
is integrable. -/
lemma integrable_re_trace_exp [IsFiniteMeasure μ] {Y : Ω → Matrix n n ℂ}
    (hYm : AEStronglyMeasurable Y μ) (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) {R : ℝ}
    (hR : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R) :
    Integrable (fun ω ↦ (NormedSpace.exp (Y ω)).trace.re) μ := by
  refine Integrable.of_bound ?_ (Fintype.card n * Real.exp R) ?_
  · have hc : Continuous fun A : Matrix n n ℂ ↦ (NormedSpace.exp A).trace.re :=
      Complex.continuous_re.comp (continuous_id.matrix_trace.comp continuous_exp)
    exact hc.comp_aestronglyMeasurable hYm
  · filter_upwards [hY, hR] with ω h1 h2
    rw [Real.norm_eq_abs]
    exact h1.abs_re_trace_exp_le.trans (by gcongr)

/-- The exponential of an almost surely bounded, almost surely Hermitian random matrix is
integrable. -/
lemma integrable_exp [IsFiniteMeasure μ] {Y : Ω → Matrix n n ℂ}
    (hYm : AEStronglyMeasurable Y μ) (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) {R : ℝ}
    (hR : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R) : Integrable (fun ω ↦ NormedSpace.exp (Y ω)) μ :=
  Integrable.of_bound (continuous_exp.comp_aestronglyMeasurable hYm) (Real.exp R) <| by
    filter_upwards [hY, hR] with ω h1 h2 using h1.norm_exp_le_of_norm_le h2

omit [Fintype n] [DecidableEq n] in
/-- If each `Y_k` has norm at most `R` almost surely, then almost surely
`‖∑_{k ∈ s} Y_k‖ ≤ |s| R`. -/
lemma _root_.MeasureTheory.ae_norm_sum_le_card_mul {ι E : Type*} [SeminormedAddCommGroup E]
    {Y : ι → Ω → E} {R : ℝ} (hR : ∀ k, ∀ᵐ ω ∂μ, ‖Y k ω‖ ≤ R) (s : Finset ι) :
    ∀ᵐ ω ∂μ, ‖∑ k ∈ s, Y k ω‖ ≤ s.card * R := by
  filter_upwards [(ae_all_iff (ι := s)).mpr fun k ↦ hR k] with ω hω
  calc ‖∑ k ∈ s, Y k ω‖ ≤ ∑ _k ∈ s, R := norm_sum_le_of_le _ fun k hk ↦ hω ⟨k, hk⟩
    _ = s.card * R := by simp

/-- **The Jensen step of the matrix Laplace transform method** (Tropp 2012, Corollary 3.3).
For a Hermitian matrix `H` and an almost surely Hermitian random matrix `Y` with `‖Y‖ ≤ R`
almost surely, `E Tr exp (H + Y) ≤ Tr exp (H + log E e^Y)`.

Write `H + Y = H + log e^Y`. The random matrix `e^Y` takes values in the closed convex Loewner
interval `[e^{-R} 1, e^R 1]` of positive definite matrices, where `A ↦ Tr exp (H + log A)` is
concave by Lieb's theorem (`concaveOn_re_trace_exp_add_log`) and continuous, so Jensen's
inequality applies. -/
theorem integral_re_trace_exp_add_le [IsProbabilityMeasure μ] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {Y : Ω → Matrix n n ℂ} (hYm : AEStronglyMeasurable Y μ)
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R) :
    ∫ ω, (NormedSpace.exp (H + Y ω)).trace.re ∂μ ≤
      (NormedSpace.exp (H + CFC.log (∫ ω, NormedSpace.exp (Y ω) ∂μ))).trace.re := by
  set s := Set.Icc (Real.exp (-R) • (1 : Matrix n n ℂ)) (Real.exp R • 1)
  have hsub : s ⊆ {A | A.PosDef} := fun A hA ↦ posDef_of_smul_one_le (Real.exp_pos _) hA.1
  have hconc := (concaveOn_re_trace_exp_add_log hH).subset hsub (convex_Icc _ _)
  have hcont := continuousOn_re_trace_exp_add_log H (b := Real.exp R) (Real.exp_pos (-R))
  have hfs : ∀ᵐ ω ∂μ, NormedSpace.exp (Y ω) ∈ s := by
    filter_upwards [hY, hR] with ω h1 h2 using h1.exp_mem_Icc_of_norm_le h2
  have hfi : Integrable (fun ω ↦ NormedSpace.exp (Y ω)) μ := integrable_exp hYm hY hR
  have hlogexp : (fun ω ↦ (NormedSpace.exp (H + Y ω)).trace.re) =ᵐ[μ]
      (fun A : Matrix n n ℂ ↦ (NormedSpace.exp (H + CFC.log A)).trace.re) ∘
        fun ω ↦ NormedSpace.exp (Y ω) := by
    filter_upwards [hY] with ω hω
    simp [CFC.log_exp _ hω.isSelfAdjoint]
  have hgi' : Integrable (fun ω ↦ (NormedSpace.exp (H + Y ω)).trace.re) μ :=
    integrable_re_trace_exp (R := ‖H‖ + R)
      ((continuous_const.add continuous_id).comp_aestronglyMeasurable hYm)
      (by filter_upwards [hY] with ω h using hH.add h)
      (by filter_upwards [hR] with ω h using (norm_add_le _ _).trans (by linarith))
  have hgi := hgi'.congr hlogexp
  have := hconc.le_map_integral hcont isClosed_Icc hfs hfi hgi
  exact le_of_eq_of_le (integral_congr_ae hlogexp) this

/-- **Subadditivity of matrix cumulant generating functions** (Tropp 2012, Lemma 3.4). Let
`Y_k` be independent random matrices, almost surely Hermitian with `‖Y_k‖ ≤ R` almost surely,
and let `H` be Hermitian. For every finite set `s` of indices,
`E Tr exp (H + ∑_{k ∈ s} Y_k) ≤ Tr exp (H + ∑_{k ∈ s} log E e^{Y_k})`.

The proof is Tropp's induction. For `s = insert j s'`, the partial sum `S = ∑_{k ∈ s'} Y_k` is
independent of `Y_j`, so the expectation is an iterated integral against the product of the
laws of `S` and `Y_j`. The Jensen step `integral_re_trace_exp_add_le`, applied with the
Hermitian matrix `H + S`, bounds the inner integral by `Tr exp (H + S + log E e^{Y_j})`, and the
induction hypothesis with the Hermitian matrix `H + log E e^{Y_j}` concludes. The almost sure
bound is the scope restriction of the module docstring. -/
theorem integral_re_trace_exp_add_sum_le [IsProbabilityMeasure μ] {ι : Type*}
    {Y : ι → Ω → Matrix n n ℂ} (hind : iIndepFun Y μ) (hYm : ∀ k, Measurable (Y k))
    (hY : ∀ k, ∀ᵐ ω ∂μ, (Y k ω).IsHermitian) {R : ℝ} (hR : ∀ k, ∀ᵐ ω ∂μ, ‖Y k ω‖ ≤ R)
    (s : Finset ι) {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∫ ω, (NormedSpace.exp (H + ∑ k ∈ s, Y k ω)).trace.re ∂μ ≤
      (NormedSpace.exp (H + ∑ k ∈ s, CFC.log (∫ ω, NormedSpace.exp (Y k ω) ∂μ))).trace.re := by
  classical
  induction s using Finset.induction_on generalizing H with
  | empty => simp
  | insert j s hj ih =>
    set L := CFC.log (∫ ω, NormedSpace.exp (Y j ω) ∂μ)
    have hLH : L.IsHermitian :=
      (IsSelfAdjoint.log (a := ∫ ω, NormedSpace.exp (Y j ω) ∂μ)).isHermitian
    set S : Ω → Matrix n n ℂ := ∑ k ∈ s, Y k
    have hSapp : ∀ ω, S ω = ∑ k ∈ s, Y k ω := fun ω ↦ Finset.sum_apply ω s Y
    have hSm : Measurable S := by
      rw [show S = fun ω ↦ ∑ k ∈ s, Y k ω from funext hSapp]
      exact Finset.measurable_sum s fun k _ ↦ hYm k
    have hSH : ∀ᵐ ω ∂μ, (S ω).IsHermitian := by
      have := (ae_all_iff (ι := s)).mpr fun k ↦ hY k
      filter_upwards [this] with ω hω
      rw [hSapp]
      exact isSelfAdjoint_sum s fun k hk ↦ hω ⟨k, hk⟩
    have hSR : ∀ᵐ ω ∂μ, ‖S ω‖ ≤ s.card * R := by
      filter_upwards [ae_norm_sum_le_card_mul hR s] with ω hω
      rwa [hSapp]
    have hindep : IndepFun S (Y j) μ := hind.indepFun_finsetSum_of_notMem hYm hj
    have hmap := (indepFun_iff_map_prod_eq_prod_map_map hSm.aemeasurable
      (hYm j).aemeasurable).mp hindep
    set F : Matrix n n ℂ × Matrix n n ℂ → ℝ :=
      fun p ↦ (NormedSpace.exp (H + p.1 + p.2)).trace.re with hF
    have hFc : Continuous F := Complex.continuous_re.comp (continuous_id.matrix_trace.comp
      (continuous_exp.comp ((continuous_const.add continuous_fst).add continuous_snd)))
    have hpair : AEMeasurable (fun ω ↦ (S ω, Y j ω)) μ :=
      (hSm.prodMk (hYm j)).aemeasurable
    have hFint : Integrable (F ∘ fun ω ↦ (S ω, Y j ω)) μ :=
      integrable_re_trace_exp (R := ‖H‖ + s.card * R + R)
        (((continuous_const.add continuous_fst).add continuous_snd).comp_aestronglyMeasurable
          hpair.aestronglyMeasurable)
        (by filter_upwards [hSH, hY j] with ω h1 h2 using (hH.add h1).add h2)
        (by filter_upwards [hSR, hR j] with ω h1 h2 using
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (by linarith)) h2))
    have hFint' : Integrable F ((μ.map S).prod (μ.map (Y j))) := by
      rw [← hmap, integrable_map_measure hFc.aestronglyMeasurable hpair]
      exact hFint
    -- the left side as an iterated integral
    have hlhs : ∫ ω, (NormedSpace.exp (H + ∑ k ∈ insert j s, Y k ω)).trace.re ∂μ =
        ∫ a, ∫ b, F (a, b) ∂(μ.map (Y j)) ∂(μ.map S) := by
      rw [← integral_prod F hFint', ← hmap, integral_map hpair hFc.aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
      simp only [hF, Finset.sum_insert hj, hSapp]
      congr 3
      abel
    -- the inner integral, by the Jensen step
    set G : Matrix n n ℂ → ℝ := fun a ↦ (NormedSpace.exp ((H + L) + a)).trace.re with hG
    have hGc : Continuous G := Complex.continuous_re.comp (continuous_id.matrix_trace.comp
      (continuous_exp.comp (continuous_const.add continuous_id)))
    have hSH' : ∀ᵐ a ∂(μ.map S), a.IsHermitian := by
      have hmeas : MeasurableSet {a : Matrix n n ℂ | a.IsHermitian} :=
        (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
      exact (ae_map_iff hSm.aemeasurable hmeas).mpr hSH
    have hinner : ∀ᵐ a ∂(μ.map S), ∫ b, F (a, b) ∂(μ.map (Y j)) ≤ G a := by
      filter_upwards [hSH'] with a ha
      rw [integral_map (f := fun b ↦ F (a, b)) (hYm j).aemeasurable
        (hFc.comp (Continuous.prodMk_right a)).aestronglyMeasurable]
      have := integral_re_trace_exp_add_le (hH.add ha) (hYm j).aestronglyMeasurable (hY j) (hR j)
      refine this.trans_eq ?_
      simp only [hG]
      congr 3
      abel
    have hGint : Integrable G (μ.map S) := by
      rw [integrable_map_measure hGc.aestronglyMeasurable hSm.aemeasurable]
      exact integrable_re_trace_exp (R := ‖H + L‖ + s.card * R)
        ((continuous_const.add continuous_id).comp_aestronglyMeasurable hSm.aestronglyMeasurable)
        (by filter_upwards [hSH] with ω h using (hH.add hLH).add h)
        (by filter_upwards [hSR] with ω h using (norm_add_le _ _).trans (by linarith))
    calc ∫ ω, (NormedSpace.exp (H + ∑ k ∈ insert j s, Y k ω)).trace.re ∂μ
        = ∫ a, ∫ b, F (a, b) ∂(μ.map (Y j)) ∂(μ.map S) := hlhs
      _ ≤ ∫ a, G a ∂(μ.map S) := integral_mono_ae hFint'.integral_prod_left hGint hinner
      _ = ∫ ω, (NormedSpace.exp ((H + L) + ∑ k ∈ s, Y k ω)).trace.re ∂μ := by
          rw [integral_map hSm.aemeasurable hGc.aestronglyMeasurable]
          simp only [hG, hSapp]
      _ ≤ (NormedSpace.exp ((H + L) +
            ∑ k ∈ s, CFC.log (∫ ω, NormedSpace.exp (Y k ω) ∂μ))).trace.re := ih (hH.add hLH)
      _ = _ := by rw [Finset.sum_insert hj, add_assoc]

end Matrix
