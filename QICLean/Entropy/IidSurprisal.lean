/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Entropy
import QICLean.Analysis.CfcKronecker
import QICLean.Algebra.KroneckerFactorPositivity
import QICLean.Analysis.SurprisalMoment
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Concentration of the surprisal of independent copies

The spectral distribution of a finite tensor power consists of products of
one-copy eigenvalue weights. Its surprisal has variance linear in the number
of copies. Chebyshev's inequality therefore gives a shrinking tail at a
window of width `k ^ (3 / 4)`.

Zero eigenvalues carry no probability. The logarithm of a product is expanded
only on its positive support; no positive-definiteness hypothesis is used.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 255–281, `comparator:high-label`, at
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The joint label selection and its polynomial mass bound are separate results.

Independently formalized; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Labels: comparator:high-label.
-/

open scoped BigOperators Matrix Kronecker ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace Matrix

private theorem finKronecker_mul {k : ℕ} {n : Type*} [Fintype n]
    (A B : Fin k → Matrix n n ℂ) :
    finKronecker (fun j ↦ A j * B j) = finKronecker A * finKronecker B := by
  ext x y
  simp only [finKronecker_apply, mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

private theorem finKronecker_diagonal {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (d : Fin k → n → ℂ) :
    finKronecker (fun j ↦ diagonal (d j)) =
      diagonal (fun x : Fin k → n ↦ ∏ j, d j (x j)) := by
  ext x y
  by_cases h : x = y
  · subst y
    simp only [finKronecker_apply, diagonal_apply_eq]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    rw [diagonal_apply_ne _ h, finKronecker_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (diagonal_apply_ne _ hj)

private theorem finKronecker_one {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n] :
    finKronecker (fun _ : Fin k ↦ (1 : Matrix n n ℂ)) = 1 := by
  simpa only [diagonal_one, Finset.prod_const_one] using
    (finKronecker_diagonal (fun _ : Fin k ↦ (fun _ : n ↦ (1 : ℂ))))

private theorem star_finKronecker {k : ℕ} {n : Type*} [Fintype n]
    (A : Fin k → Matrix n n ℂ) :
    star (finKronecker A) = finKronecker (fun j ↦ star (A j)) := by
  ext x y
  simp only [star_eq_conjTranspose, conjTranspose_apply, finKronecker_apply, star_prod]

private theorem finKronecker_mem_unitary {k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (U : Fin k → unitary (Matrix n n ℂ)) :
    finKronecker (fun j ↦ (U j : Matrix n n ℂ)) ∈
      Matrix.unitaryGroup (Fin k → n) ℂ := by
  rw [mem_unitaryGroup_iff]
  rw [star_finKronecker, ← finKronecker_mul]
  simpa only [← Unitary.coe_star, Unitary.coe_mul_star_self] using
    (finKronecker_one (k := k) (n := n))

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

/-- The actual tensor-power surprisal has the product eigenvalue distribution.
OpenAI area-law manuscript, `07-comparators.tex`, lines 255–263,
`comparator:high-label`. The function is arbitrary because all spectra are finite. -/
theorem PosSemidef.re_trace_finKronecker_mul_cfc_surprisal (hρ : ρ.PosSemidef)
    (k : ℕ) (f : ℝ → ℝ) :
    let p := hρ.isHermitian.eigenvalues
    let ρk := finKronecker (fun _ : Fin k ↦ ρ)
    (ρk * cfc f (-CFC.log ρk)).trace.re =
      ∑ x : Fin k → n, (∏ j, p (x j)) * f (-Real.log (∏ j, p (x j))) := by
  let U := hρ.isHermitian.eigenvectorUnitary
  let Uk : unitary (Matrix (Fin k → n) (Fin k → n) ℂ) :=
    ⟨finKronecker (fun _ : Fin k ↦ (U : Matrix n n ℂ)),
      finKronecker_mem_unitary (fun _ : Fin k ↦ U)⟩
  let q : (Fin k → n) → ℝ := fun x ↦ ∏ j, hρ.isHermitian.eigenvalues (x j)
  have hconj : finKronecker (fun _ : Fin k ↦ ρ) =
      (Uk : Matrix (Fin k → n) (Fin k → n) ℂ) * diagonal (fun x ↦ (q x : ℂ)) *
        star (Uk : Matrix (Fin k → n) (Fin k → n) ℂ) := by
    trans finKronecker (fun _ : Fin k ↦ (U : Matrix n n ℂ) *
      diagonal (fun i ↦ (hρ.isHermitian.eigenvalues i : ℂ)) * star (U : Matrix n n ℂ))
    · exact congrArg finKronecker (funext fun _ : Fin k ↦ hρ.isHermitian.spectral_form)
    · rw [finKronecker_mul, finKronecker_mul, finKronecker_diagonal]
      simp only [Uk, q, Complex.ofReal_prod, star_finKronecker]
  have hk : (finKronecker (fun _ : Fin k ↦ ρ)).IsHermitian :=
    (finKronecker_posSemidef (fun _ : Fin k ↦ ρ) (fun _ ↦ hρ)).isHermitian
  have hcomp : cfc f (-CFC.log (finKronecker (fun _ : Fin k ↦ ρ))) =
      cfc (fun t ↦ f (-Real.log t)) (finKronecker (fun _ : Fin k ↦ ρ)) := by
    rw [CFC.log, ← cfc_neg]
    exact (cfc_comp' f (fun t : ℝ ↦ -Real.log t) (finKronecker (fun _ : Fin k ↦ ρ))
      (((finKronecker (fun _ : Fin k ↦ ρ)).finite_real_spectrum.image _).continuousOn f)
      ((finKronecker (fun _ : Fin k ↦ ρ)).finite_real_spectrum.continuousOn _)
      hk.isSelfAdjoint).symm
  have hD : (diagonal (fun x ↦ (q x : ℂ))).IsHermitian := by
    simp [isHermitian_diagonal_iff, IsSelfAdjoint]
  change ((finKronecker (fun _ : Fin k ↦ ρ)) *
    cfc f (-CFC.log (finKronecker (fun _ : Fin k ↦ ρ)))).trace.re =
      ∑ x, q x * f (-Real.log (q x))
  rw [hcomp, hk.cfc_eq, hk.self_mul_cfc, ← hk.cfc_eq, hconj]
  rw [cfc_conj_unitary hD _ Uk,
    cfc_diagonal q (fun t ↦ t * f (-Real.log t)) ((Set.finite_range q).continuousOn _)]
  rw [trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]

end Matrix

namespace Entropy

open MeasureTheory ProbabilityTheory

variable {n : Type*} [Fintype n]

/-- Chebyshev concentration for independent copies of a finite surprisal law.
OpenAI area-law manuscript, `07-comparators.tex`, lines 255–263,
`comparator:high-label`. Zero weights are permitted. -/
theorem surprisalTail_pi_le_variance {p : n → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (k : ℕ) {w : ℝ} (hw : 0 < w) :
    surprisalTail (fun x : Fin k → n ↦ ∏ j, p (x j))
      ((k : ℝ) * ∑ i, Real.negMulLog (p i)) w ≤
        (k : ℝ) * (∑ i, p i * (-Real.log (p i) - ∑ a, Real.negMulLog (p a)) ^ 2) / w ^ 2 := by
  classical
  let : MeasurableSpace n := ⊤
  have hpE : ∑ i, ENNReal.ofReal (p i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hp i), hs, ENNReal.ofReal_one]
  let P := PMF.ofFintype (fun i ↦ ENNReal.ofReal (p i)) hpE
  let μ := P.toMeasure
  let ν := Measure.pi (fun _ : Fin k ↦ μ)
  let X : n → ℝ := fun i ↦ -Real.log (p i)
  let Y : (Fin k → n) → ℝ := fun x ↦ ∑ j, X (x j)
  have hmean : ∫ i, X i ∂μ = ∑ i, Real.negMulLog (p i) := by
    rw [PMF.integral_eq_sum P X]
    simp only [P, PMF.ofFintype_apply, X, smul_eq_mul,
      ENNReal.toReal_ofReal (hp _), Real.negMulLog, mul_neg, neg_mul]
  have hEY : ∫ x, Y x ∂ν = (k : ℝ) * ∑ i, Real.negMulLog (p i) := by
    change (∫ x, ∑ j, X (x j) ∂Measure.pi (fun _ : Fin k ↦ μ)) = _
    rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
    simp_rw [integral_comp_eval (AEStronglyMeasurable.of_discrete), hmean]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hVX : variance X μ =
      ∑ i, p i * (-Real.log (p i) - ∑ a, Real.negMulLog (p a)) ^ 2 := by
    rw [variance_eq_integral (MemLp.of_discrete : MemLp X 2 μ).aemeasurable, hmean,
      PMF.integral_eq_sum P]
    simp only [P, PMF.ofFintype_apply, X, smul_eq_mul, ENNReal.toReal_ofReal (hp _)]
  have hVY : variance Y ν = (k : ℝ) * variance X μ := by
    change variance (fun x ↦ ∑ j, X (x j)) (Measure.pi (fun _ : Fin k ↦ μ)) = _
    simpa only [Finset.sum_fn, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using
      (variance_sum_pi (fun _ : Fin k ↦ (MemLp.of_discrete : MemLp X 2 μ)))
  have hCheby := meas_ge_le_variance_div_sq (MemLp.of_discrete : MemLp Y 2 ν) hw
  rw [hEY] at hCheby
  have hν : ∀ x : Fin k → n, ν {x} = ENNReal.ofReal (∏ j, p (x j)) := by
    intro x
    simp only [ν, Measure.pi_singleton, μ, PMF.toMeasure_apply_singleton P _
      (measurableSet_singleton _), P, PMF.ofFintype_apply]
    exact (ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ hp (x j))).symm
  let T : Finset (Fin k → n) := Finset.univ.filter
    (fun x ↦ w ≤ |Y x - (k : ℝ) * ∑ i, Real.negMulLog (p i)|)
  have hT : (T : Set (Fin k → n)) =
      {x | w ≤ |Y x - (k : ℝ) * ∑ i, Real.negMulLog (p i)|} := by
    ext x
    simp only [T, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq]
  have hmass : ν.real (T : Set (Fin k → n)) = ∑ x ∈ T, ∏ j, p (x j) := by
    rw [← sum_measureReal_singleton]
    simp only [measureReal_def, hν]
    exact Finset.sum_congr rfl (fun x _ ↦
      ENNReal.toReal_ofReal (Finset.prod_nonneg (fun j _ ↦ hp (x j))))
  have htail : surprisalTail (fun x : Fin k → n ↦ ∏ j, p (x j))
      ((k : ℝ) * ∑ i, Real.negMulLog (p i)) w ≤ ν.real (T : Set (Fin k → n)) := by
    rw [hmass, surprisalTail, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro x _
    by_cases hzero : (∏ j, p (x j)) = 0
    · simp only [hzero, ite_self, le_refl]
    · have hlog : Y x = -Real.log (∏ j, p (x j)) := by
        rw [Real.log_prod (Finset.prod_ne_zero_iff.mp hzero)]
        simp only [Y, X, Finset.sum_neg_distrib]
      rw [hlog]
      split_ifs with hstrict hweak
      · exact le_refl _
      · exact False.elim (hweak hstrict.le)
      · exact Finset.prod_nonneg (fun j _ ↦ hp (x j))
      · exact le_refl _
  apply htail.trans
  rw [measureReal_def, hT]
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hCheby
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg Y ν) (sq_nonneg w)),
    hVY, hVX] at hr
  exact hr

end Entropy

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

/-- The spectral mass outside an entropy window for an actual tensor-power density matrix.
OpenAI area-law manuscript, `07-comparators.tex`, lines 255–263,
`comparator:high-label`. The logarithm is interpreted on the support; zero eigenvalues
contribute no mass. -/
theorem PosSemidef.re_trace_surprisalTail_finKronecker_le (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (k : ℕ) {w : ℝ} (hw : 0 < w) :
    let S := vonNeumannEntropy ρ hρ.isHermitian
    let p := hρ.isHermitian.eigenvalues
    let ρk := finKronecker (fun _ : Fin k ↦ ρ)
    (ρk * cfc (fun t : ℝ ↦ if w < |t - (k : ℝ) * S| then 1 else 0)
      (-CFC.log ρk)).trace.re ≤
        (k : ℝ) * (∑ i, p i * (-Real.log (p i) - S) ^ 2) / w ^ 2 := by
  dsimp only
  rw [hρ.re_trace_finKronecker_mul_cfc_surprisal]
  simp only [mul_ite, mul_one, mul_zero]
  exact Entropy.surprisalTail_pi_le_variance hρ.eigenvalues_nonneg
    (posSemidef_trace_one_eigenvalues_sum_one hρ htr) k hw

/-- At a window of width `k ^ (3 / 4)`, the tail mass is at most the one-copy
surprisal variance divided by `sqrt k`. OpenAI area-law manuscript,
`07-comparators.tex`, lines 255–263, `comparator:high-label`. -/
theorem PosSemidef.re_trace_surprisalTail_finKronecker_three_quarters_le
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {k : ℕ} (hk : 0 < k) :
    let S := vonNeumannEntropy ρ hρ.isHermitian
    let p := hρ.isHermitian.eigenvalues
    let ρk := finKronecker (fun _ : Fin k ↦ ρ)
    (ρk * cfc (fun t : ℝ ↦ if (k : ℝ) ^ (3 / 4 : ℝ) < |t - (k : ℝ) * S|
      then 1 else 0) (-CFC.log ρk)).trace.re ≤
        (∑ i, p i * (-Real.log (p i) - S) ^ 2) / Real.sqrt k := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have h := hρ.re_trace_surprisalTail_finKronecker_le htr k
    (Real.rpow_pos_of_pos hkR (3 / 4 : ℝ))
  dsimp only at h ⊢
  apply h.trans_eq
  have hden : ((k : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = (k : ℝ) * Real.sqrt k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hkR.le]
    norm_num
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hkR,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hden, mul_div_mul_left _ _ hkR.ne']

end Matrix
