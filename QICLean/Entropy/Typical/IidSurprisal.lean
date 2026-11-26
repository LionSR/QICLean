/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.VonNeumann.Entropy
import QICLean.Analysis.FunctionalCalculus.FiniteKroneckerPowers
import QICLean.Algebra.Kronecker.KroneckerFactorPositivity
import QICLean.Channel.Schmidt.SurprisalMoment
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.Moments.SubGaussian

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

It also contains the following results.

* `Entropy.surprisalMoment_pi`: exact surprisal moments of independent copies.
* `Entropy.exists_surprisal_upper_tail_pi_le_exp`,
  `Matrix.PosSemidef.exists_re_trace_surprisal_upper_tail_piKronecker_le_exp`: exponential upper
  tails of finite independent-copy surprisal.
* `Matrix.IsHermitian.exp_smul_sub_smul_one_eq_cfc`,
  `Matrix.PosSemidef.re_trace_piKronecker_exp_centered_surprisal`: exact centered exponential
  moments of tensor-power densities.
-/

section IidSurprisal

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

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

/-- The actual tensor-power surprisal has the product eigenvalue distribution.
OpenAI area-law manuscript, `07-comparators.tex`, lines 255–263,
`comparator:high-label`. The function is arbitrary because all spectra are finite. -/
theorem PosSemidef.re_trace_piKronecker_mul_cfc_surprisal (hρ : ρ.PosSemidef)
    (k : ℕ) (f : ℝ → ℝ) :
    let p := hρ.isHermitian.eigenvalues
    let ρk := piKronecker (fun _ : Fin k ↦ ρ)
    (ρk * cfc f (-CFC.log ρk)).trace.re =
      ∑ x : Fin k → n, (∏ j, p (x j)) * f (-Real.log (∏ j, p (x j))) := by
  let U := hρ.isHermitian.eigenvectorUnitary
  let Uk : unitary (Matrix (Fin k → n) (Fin k → n) ℂ) :=
    ⟨piKronecker (fun _ : Fin k ↦ (U : Matrix n n ℂ)),
      piKronecker_mem_unitaryGroup fun _ : Fin k ↦ U.2⟩
  let q : (Fin k → n) → ℝ := fun x ↦ ∏ j, hρ.isHermitian.eigenvalues (x j)
  have hconj : piKronecker (fun _ : Fin k ↦ ρ) =
      (Uk : Matrix (Fin k → n) (Fin k → n) ℂ) * diagonal (fun x ↦ (q x : ℂ)) *
        star (Uk : Matrix (Fin k → n) (Fin k → n) ℂ) := by
    trans piKronecker (fun _ : Fin k ↦ (U : Matrix n n ℂ) *
      diagonal (fun i ↦ (hρ.isHermitian.eigenvalues i : ℂ)) * star (U : Matrix n n ℂ))
    · exact congrArg piKronecker (funext fun _ : Fin k ↦ hρ.isHermitian.spectral_form)
    · rw [← piKronecker_mul, ← piKronecker_mul, piKronecker_diagonal]
      simp only [Uk, q, Complex.ofReal_prod, star_eq_conjTranspose, conjTranspose_piKronecker]
  have hk : (piKronecker (fun _ : Fin k ↦ ρ)).IsHermitian :=
    (piKronecker_posSemidef (fun _ : Fin k ↦ ρ) (fun _ ↦ hρ)).isHermitian
  have hcomp : cfc f (-CFC.log (piKronecker (fun _ : Fin k ↦ ρ))) =
      cfc (fun t ↦ f (-Real.log t)) (piKronecker (fun _ : Fin k ↦ ρ)) := by
    rw [CFC.log, ← cfc_neg]
    exact (cfc_comp' f (fun t : ℝ ↦ -Real.log t) (piKronecker (fun _ : Fin k ↦ ρ))
      (((piKronecker (fun _ : Fin k ↦ ρ)).finite_real_spectrum.image _).continuousOn f)
      ((piKronecker (fun _ : Fin k ↦ ρ)).finite_real_spectrum.continuousOn _)
      hk.isSelfAdjoint).symm
  have hD : (diagonal (fun x ↦ (q x : ℂ))).IsHermitian := by
    simp [isHermitian_diagonal_iff, IsSelfAdjoint]
  change ((piKronecker (fun _ : Fin k ↦ ρ)) *
    cfc f (-CFC.log (piKronecker (fun _ : Fin k ↦ ρ)))).trace.re =
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
theorem PosSemidef.re_trace_surprisalTail_piKronecker_le (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (k : ℕ) {w : ℝ} (hw : 0 < w) :
    let S := vonNeumannEntropy ρ hρ.isHermitian
    let p := hρ.isHermitian.eigenvalues
    let ρk := piKronecker (fun _ : Fin k ↦ ρ)
    (ρk * cfc (fun t : ℝ ↦ if w < |t - (k : ℝ) * S| then 1 else 0)
      (-CFC.log ρk)).trace.re ≤
        (k : ℝ) * (∑ i, p i * (-Real.log (p i) - S) ^ 2) / w ^ 2 := by
  dsimp only
  rw [hρ.re_trace_piKronecker_mul_cfc_surprisal]
  simp only [mul_ite, mul_one, mul_zero]
  exact Entropy.surprisalTail_pi_le_variance hρ.eigenvalues_nonneg
    (posSemidef_trace_one_eigenvalues_sum_one hρ htr) k hw

/-- At a window of width `k ^ (3 / 4)`, the tail mass is at most the one-copy
surprisal variance divided by `sqrt k`. OpenAI area-law manuscript,
`07-comparators.tex`, lines 255–263, `comparator:high-label`. -/
theorem PosSemidef.re_trace_surprisalTail_piKronecker_three_quarters_le
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {k : ℕ} (hk : 0 < k) :
    let S := vonNeumannEntropy ρ hρ.isHermitian
    let p := hρ.isHermitian.eigenvalues
    let ρk := piKronecker (fun _ : Fin k ↦ ρ)
    (ρk * cfc (fun t : ℝ ↦ if (k : ℝ) ^ (3 / 4 : ℝ) < |t - (k : ℝ) * S|
      then 1 else 0) (-CFC.log ρk)).trace.re ≤
        (∑ i, p i * (-Real.log (p i) - S) ^ 2) / Real.sqrt k := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have h := hρ.re_trace_surprisalTail_piKronecker_le htr k
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

end

end IidSurprisal

section SurprisalProductMoment

/-!
## Exact surprisal moments of independent copies

The moment of a finite product law is the corresponding power of the
one-copy moment. Zero weights contribute zero before logarithms are
expanded. The identity also holds for zero copies and does not require
normalization of the weights.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 218--238,
`comparator:signed-label-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators

namespace Entropy

/-- Independent finite copies have multiplicative surprisal moments.
The weights may vanish and need not sum to one. Source:
`07-comparators.tex`, lines 218--238. -/
theorem surprisalMoment_pi {n : Type*} [Fintype n]
    (p : n → ℝ) (k : ℕ) (u : ℝ) :
    surprisalMoment (fun x : Fin k → n ↦ ∏ j, p (x j)) u =
      surprisalMoment p u ^ k := by
  unfold surprisalMoment
  trans ∑ x : Fin k → n, ∏ j, p (x j) * Real.exp (u * -Real.log (p (x j)))
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : ∏ j, p (x j) = 0
    · simp only [Finset.prod_mul_distrib, hx, zero_mul]
    · rw [Real.log_prod (Finset.prod_ne_zero_iff.mp hx),
        ← Finset.sum_neg_distrib, Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]
  · simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Fintype.prod_sum (fun (_ : Fin k) i ↦ p i * Real.exp (u * -Real.log (p i)))).symm

end Entropy

end SurprisalProductMoment

section IidSurprisalExponential

/-!
## Exponential upper tails of finite independent-copy surprisal

A finite probability law has bounded surprisal on its positive support.
Hoeffding's inequality therefore bounds the probability that the surprisal
of `k` independent copies exceeds `k` times the entropy plus one by an
exponentially decreasing function of `k`. The rate depends on the fixed
one-copy law. Zero weights are permitted and contribute zero probability.

The matrix consequence concerns the actual tensor power of a positive
semidefinite trace-one matrix. It uses its exact spectral distribution,
without a positive-definiteness or moment-generating-function hypothesis.

### References

OpenAI, *A two-dimensional area law from a global spectral gap*, September
24, 2026, `07-comparators.tex`, lines 332–343, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix Kronecker ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace Entropy

open MeasureTheory ProbabilityTheory

variable {n : Type*} [Fintype n]

/-- The upper surprisal tail of the actual finite product law decreases
exponentially at entropy plus one. The rate is derived from the fixed finite
law, and zero weights are allowed.

OpenAI area-law manuscript, `07-comparators.tex`, lines 339–343. -/
theorem exists_surprisal_upper_tail_pi_le_exp {p : n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      (∑ x : Fin k → n,
        if (k : ℝ) * ((∑ i, Real.negMulLog (p i)) + 1) <
            -Real.log (∏ j, p (x j)) then ∏ j, p (x j) else 0) ≤
        Real.exp (-c * (k : ℝ)) := by
  classical
  let : MeasurableSpace n := ⊤
  have hpE : ∑ i, ENNReal.ofReal (p i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hp i), hs, ENNReal.ofReal_one]
  let P := PMF.ofFintype (fun i ↦ ENNReal.ofReal (p i)) hpE
  let μ := P.toMeasure
  let X : n → ℝ := fun i ↦ -Real.log (p i)
  let H : ℝ := ∑ i, Real.negMulLog (p i)
  have hmean : ∫ i, X i ∂μ = H := by
    rw [PMF.integral_eq_sum P X]
    simp only [P, PMF.ofFintype_apply, X, H, smul_eq_mul,
      ENNReal.toReal_ofReal (hp _), Real.negMulLog, mul_neg, neg_mul]
  have hp_one (i : n) : p i ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ ↦ hp j) (Finset.mem_univ i)
  let M : ℝ := 1 + ∑ i, ‖X i‖
  have hM : 0 < M := by
    dsimp only [M]
    positivity
  have hX (i : n) : X i ∈ Set.Icc 0 M := by
    refine ⟨neg_nonneg.mpr (Real.log_nonpos (hp i) (hp_one i)), ?_⟩
    have hnorm : ‖X i‖ ≤ ∑ j, ‖X j‖ :=
      Finset.single_le_sum (fun j _ ↦ norm_nonneg (X j)) (Finset.mem_univ i)
    have hle : X i ≤ ‖X i‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (X i)
    dsimp only [M]
    linarith
  let v : NNReal := (‖M‖₊ / 2) ^ 2
  have hv : 0 < v := by
    exact pow_pos (div_pos (nnnorm_pos.mpr hM.ne') (by norm_num)) 2
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  refine ⟨(2 * (v : ℝ))⁻¹, inv_pos.mpr (mul_pos (by norm_num) hvR), ?_⟩
  intro k hk
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hk
  let ν := Measure.pi (fun _ : Fin k ↦ μ)
  have hmean_eval (j : Fin k) : ∫ x : Fin k → n, X (x j) ∂ν = H := by
    change (∫ x : Fin k → n, X (x j) ∂Measure.pi (fun _ : Fin k ↦ μ)) = H
    rw [integral_comp_eval (AEStronglyMeasurable.of_discrete), hmean]
  have hsubG (j : Fin k) :
      HasSubgaussianMGF (fun x : Fin k → n ↦ X (x j) - H) v ν := by
    have h := hasSubgaussianMGF_of_mem_Icc
      (μ := ν) (X := fun x : Fin k → n ↦ X (x j))
      (AEStronglyMeasurable.of_discrete.aemeasurable)
      (ae_of_all _ (fun x ↦ hX (x j)))
    simpa only [sub_zero, hmean_eval j] using h
  have hindep : iIndepFun (fun j (x : Fin k → n) ↦ X (x j) - H) ν := by
    exact iIndepFun_pi fun _ ↦
      (AEStronglyMeasurable.of_discrete :
        AEStronglyMeasurable (fun i : n ↦ X i - H) μ).aemeasurable
  have hHoeffding :
      ν.real {x : Fin k → n | (k : ℝ) ≤ ∑ j, (X (x j) - H)} ≤
        Real.exp (-(k : ℝ) ^ 2 / (2 * ((k : ℝ) * (v : ℝ)))) := by
    simpa [nsmul_eq_mul] using
      (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep
        (s := Finset.univ) (c := fun _ ↦ v)
        (fun j _ ↦ hsubG j) (ε := (k : ℝ)) (Nat.cast_nonneg k))
  have hν : ∀ x : Fin k → n, ν {x} = ENNReal.ofReal (∏ j, p (x j)) := by
    intro x
    simp only [ν, Measure.pi_singleton, μ, PMF.toMeasure_apply_singleton P _
      (measurableSet_singleton _), P, PMF.ofFintype_apply]
    exact (ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ hp (x j))).symm
  let T : Finset (Fin k → n) := Finset.univ.filter
    (fun x ↦ (k : ℝ) ≤ ∑ j, (X (x j) - H))
  have hT : (T : Set (Fin k → n)) =
      {x | (k : ℝ) ≤ ∑ j, (X (x j) - H)} := by
    ext x
    simp only [T, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq]
  have hmass : ν.real (T : Set (Fin k → n)) = ∑ x ∈ T, ∏ j, p (x j) := by
    rw [← sum_measureReal_singleton]
    simp only [measureReal_def, hν]
    exact Finset.sum_congr rfl (fun x _ ↦
      ENNReal.toReal_ofReal (Finset.prod_nonneg (fun j _ ↦ hp (x j))))
  have htail :
      (∑ x : Fin k → n,
        if (k : ℝ) * (H + 1) < -Real.log (∏ j, p (x j)) then
          ∏ j, p (x j) else 0) ≤
        ν.real {x : Fin k → n | (k : ℝ) ≤ ∑ j, (X (x j) - H)} := by
    rw [← hT, hmass, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro x _
    by_cases hzero : (∏ j, p (x j)) = 0
    · simp only [hzero, ite_self, le_refl]
    · have hsum : (∑ j : Fin k, (X (x j) - H)) =
          -Real.log (∏ j, p (x j)) - (k : ℝ) * H := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul,
          Real.log_prod (Finset.prod_ne_zero_iff.mp hzero)]
        simp only [X, Finset.sum_neg_distrib]
      have himp : (k : ℝ) * (H + 1) < -Real.log (∏ j, p (x j)) →
          (k : ℝ) ≤ ∑ j, (X (x j) - H) := by
        rw [hsum]
        intro h
        nlinarith
      by_cases hx : (k : ℝ) * (H + 1) < -Real.log (∏ j, p (x j))
      · rw [ite_eq_left hx, ite_eq_left (himp hx)]
      · rw [ite_eq_right hx]
        split_ifs
        · exact Finset.prod_nonneg (fun j _ ↦ hp (x j))
        · exact le_rfl
  have hexponent : -(k : ℝ) ^ 2 / (2 * ((k : ℝ) * (v : ℝ))) =
      -(2 * (v : ℝ))⁻¹ * (k : ℝ) := by
    field_simp [hkR.ne', hvR.ne']
  rw [hexponent] at hHoeffding
  exact htail.trans hHoeffding

end Entropy

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

/-- For an actual positive semidefinite trace-one matrix, the upper surprisal
tail of its tensor powers decreases exponentially at entropy plus one.
The rate depends on the fixed matrix; singular densities are included.

OpenAI area-law manuscript, `07-comparators.tex`, lines 339–343. -/
theorem PosSemidef.exists_re_trace_surprisal_upper_tail_piKronecker_le_exp
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      let S := vonNeumannEntropy ρ hρ.isHermitian
      let ρk := piKronecker (fun _ : Fin k ↦ ρ)
      (ρk * cfc (fun t : ℝ ↦ if (k : ℝ) * (S + 1) < t then 1 else 0)
        (-CFC.log ρk)).trace.re ≤ Real.exp (-c * (k : ℝ)) := by
  obtain ⟨c, hc, htail⟩ := Entropy.exists_surprisal_upper_tail_pi_le_exp
    hρ.eigenvalues_nonneg (posSemidef_trace_one_eigenvalues_sum_one hρ htr)
  refine ⟨c, hc, ?_⟩
  intro k hk
  dsimp only
  rw [hρ.re_trace_piKronecker_mul_cfc_surprisal]
  simp only [mul_ite, mul_one, mul_zero]
  exact htail k hk

end Matrix

end

end IidSurprisalExponential

section IidSurprisalMomentExponential

/-!
## Exact centered exponential moments of tensor-power densities

The weighted exponential of the actual tensor-power surprisal has the
product moment of the original eigenvalue weights. A scalar center is
arbitrary. Neither invertibility nor trace-one normalization is required
for this identity; zero eigenvalues carry zero weight.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 218--238,
`comparator:signed-label-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Centering and scaling a Hermitian matrix in the exponential agree
with the corresponding scalar functional calculus. Source:
`07-comparators.tex`, lines 218--238. -/
theorem IsHermitian.exp_smul_sub_smul_one_eq_cfc
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (u s : ℝ) :
    NormedSpace.exp ((u : ℂ) • (A - (s : ℂ) • 1)) =
      cfc (fun x : ℝ ↦ Real.exp (u * (x - s))) A := by
  simp only [Complex.coe_smul]
  rw [cfc_comp' Real.exp (fun x : ℝ ↦ u * (x - s)) A (ha := hA.isSelfAdjoint)]
  rw [cfc_const_mul u (fun x : ℝ ↦ x - s) A (by fun_prop),
    cfc_sub (fun x : ℝ ↦ x) (fun _ ↦ s) A (by fun_prop) (by fun_prop),
    cfc_id' ℝ A hA.isSelfAdjoint,
    cfc_const s A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  exact (CFC.real_exp_eq_normedSpace_exp ((IsSelfAdjoint.all u).smul
    (hA.isSelfAdjoint.sub ((IsSelfAdjoint.all s).smul
      (IsSelfAdjoint.one (Matrix n n ℂ)))))).symm

/-- The actual centered tensor-power surprisal moment is the power of
the one-copy moment times its scalar centering factor. Singular and zero
densities, arbitrary centers and zero copies are included. Source:
`07-comparators.tex`, lines 218--238. -/
theorem PosSemidef.re_trace_piKronecker_exp_centered_surprisal
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (k : ℕ) (u s : ℝ) :
    let ρk := piKronecker (fun _ : Fin k ↦ ρ)
    (ρk * NormedSpace.exp ((u : ℂ) • (-CFC.log ρk - (s : ℂ) • 1))).trace.re =
      Real.exp (-u * s) * Entropy.surprisalMoment hρ.isHermitian.eigenvalues u ^ k := by
  intro ρk
  rw [(show (-CFC.log ρk).IsHermitian from IsSelfAdjoint.log.neg).exp_smul_sub_smul_one_eq_cfc,
    hρ.re_trace_piKronecker_mul_cfc_surprisal k (fun x ↦ Real.exp (u * (x - s)))]
  rw [← Entropy.surprisalMoment_pi hρ.isHermitian.eigenvalues k u]
  simp_rw [Entropy.surprisalMoment, Finset.mul_sum, mul_sub, sub_eq_add_neg, Real.exp_add]
  simp only [mul_neg, mul_comm, mul_left_comm]

end Matrix

end

end IidSurprisalMomentExponential
