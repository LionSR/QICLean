/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.IidSurprisal
import Mathlib.Probability.Moments.SubGaussian

/-!
# Exponential upper tails of finite independent-copy surprisal

A finite probability law has bounded surprisal on its positive support.
Hoeffding's inequality therefore bounds the probability that the surprisal
of `k` independent copies exceeds `k` times the entropy plus one by an
exponentially decreasing function of `k`. The rate depends on the fixed
one-copy law. Zero weights are permitted and contribute zero probability.

The matrix consequence concerns the actual tensor power of a positive
semidefinite trace-one matrix. It uses its exact spectral distribution,
without a positive-definiteness or moment-generating-function hypothesis.

## References

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
theorem PosSemidef.exists_re_trace_surprisal_upper_tail_finKronecker_le_exp
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      let S := vonNeumannEntropy ρ hρ.isHermitian
      let ρk := finKronecker (fun _ : Fin k ↦ ρ)
      (ρk * cfc (fun t : ℝ ↦ if (k : ℝ) * (S + 1) < t then 1 else 0)
        (-CFC.log ρk)).trace.re ≤ Real.exp (-c * (k : ℝ)) := by
  obtain ⟨c, hc, htail⟩ := Entropy.exists_surprisal_upper_tail_pi_le_exp
    hρ.eigenvalues_nonneg (posSemidef_trace_one_eigenvalues_sum_one hρ htr)
  refine ⟨c, hc, ?_⟩
  intro k hk
  dsimp only
  rw [hρ.re_trace_finKronecker_mul_cfc_surprisal]
  simp only [mul_ite, mul_one, mul_zero]
  exact htail k hk

end Matrix
