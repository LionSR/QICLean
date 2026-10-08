/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.WeylCharacter
import QICLean.Representation.ReplicaGammaIntegral
import QICLean.Analysis.CfcConjugation

/-!
# The spectral law of the replica metrics

Fix `d ≥ 1` and `t > 0`. The proof of Lemma 6.2 of the area-law paper (*A two-dimensional area
law from a global spectral gap*, `05-replicas.tex`, lines 336–347) chooses the eigenvalues `s`
of a density matrix on `ℂ^d` with density proportional to `Δ(s) Δ(s^t)` on the simplex and an
independent Haar-distributed unitary eigenbasis. Here the eigenvalues are `x/∑ x` for `x` in
the positive orthant with density proportional to `a_δ(x) a_δ(x^t) e^{-∑ x}`; since
`a_δ(x) a_δ(x^t)` is homogeneous, this is the same law of `s`.

This file defines the law and its samples `σ = U diag(x/∑x) U†`, and proves that
`∫ (σ^t)^{⊗k}` is the label observable of the common label function on `(ℂ^d)^{⊗k}`:

* the integral over the unitary is the twirl of `diag(s^t)^{⊗k}`, a central label function with
  eigenvalue `χ_λ(s^t)/dim V_λ`;
* by the Weyl character formula, `a_δ(x^t) χ_λ(x^t) = a_l(x^t)`, so the average of the
  eigenvalue is the normalized gamma integral, which is `w_k(λ)`.

The proofs are written from the paper; no Lean source was adapted.

## Main declarations

* `TensorPower.specDensity`, `TensorPower.specNorm`, `TensorPower.specMeasure`.
* `TensorPower.specSample` — `σ = U diag(x/∑ x) U†`.
* `TensorPower.integral_specSample_tensorPow` — `∫ (σ^t)^{⊗k} = ∑_λ w_k(λ) π^λ`.
-/

open MeasureTheory Matrix Finset PermutationRepresentation Partition
open scoped MatrixOrder ComplexOrder ENNReal NNReal

namespace TensorPower

variable {d : ℕ}

/-! ### The spectral density -/

/-- The unnormalized spectral density `a_δ(x) a_δ(x^t) e^{-∑ x}` on the orthant. -/
noncomputable def specDensity (d : ℕ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  alternant (delta d) x * alternant (delta d) (fun i => x i ^ t) * Real.exp (-∑ i, x i)

/-- The normalization `∫ a_δ(x) a_δ(x^t) e^{-∑ x} dx`. -/
noncomputable def specNorm (d : ℕ) (t : ℝ) : ℝ := gammaIntegral d t (delta d) 0

theorem gammaIntegrand_zero (t : ℝ) (x : Fin d → ℝ) :
    alternant (delta d) x * alternant (delta d) (fun i => x i ^ t) * (∑ i, x i) ^ (-(0 : ℝ)) *
      Real.exp (-∑ i, x i) = specDensity d t x := by
  simp [specDensity]

theorem specNorm_eq_integral (t : ℝ) : specNorm d t = ∫ x, specDensity d t x ∂(orthant d) := by
  simp only [specNorm, gammaIntegral, gammaIntegrand_zero]

theorem continuous_alternant (α : Fin d → ℕ) : Continuous (alternant (R := ℝ) α) := by
  unfold alternant
  fun_prop

theorem measurable_specDensity {t : ℝ} (ht : 0 ≤ t) : Measurable (specDensity d t) := by
  have h1 := continuous_alternant (d := d) (delta d)
  have h2 : Continuous fun x : Fin d → ℝ => alternant (delta d) (fun i => x i ^ t) :=
    h1.comp (continuous_pi fun i => (Real.continuous_rpow_const ht).comp (continuous_apply i))
  unfold specDensity
  exact ((h1.mul h2).mul (Real.continuous_exp.comp
    (continuous_finsetSum _ fun i _ => continuous_apply i).neg)).measurable

theorem specDensity_nonneg {t : ℝ} (ht : 0 ≤ t) {x : Fin d → ℝ} (hx : ∀ i, 0 < x i) :
    0 ≤ specDensity d t x :=
  mul_nonneg (alternant_delta_mul_rpow_nonneg ht hx) (Real.exp_pos _).le

theorem integrable_specDensity (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (specDensity d t) (orthant d) := by
  have h := integrable_gammaIntegrand hd ht (delta d) le_rfl (by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity)
  simpa only [gammaIntegrand_zero] using h

theorem delta_injective : Function.Injective (fun i : Fin d => ((delta d i : ℕ) : ℝ)) := by
  intro i j h
  have h' : delta d i = delta d j := by
    have h'' : ((delta d i : ℕ) : ℝ) = delta d j := h
    exact_mod_cast h''
  simp only [shiftedPart, Pi.zero_apply, zero_add] at h'
  exact Fin.ext (by have := i.2; have := j.2; omega)

theorem specNorm_pos (hd : 0 < d) {t : ℝ} (ht : 0 < t) : 0 < specNorm d t := by
  have hnn : 0 ≤ specNorm d t := by
    rw [specNorm_eq_integral]
    exact integral_nonneg_of_ae (ae_orthant_pos.mono fun x hx => specDensity_nonneg ht.le hx)
  refine hnn.lt_of_ne fun h0 => ?_
  have hD : (0 : ℝ) < d + (d.choose 2 : ℕ) + t * ∑ i, ((delta d i : ℕ) : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have h := gammaIntegral_eq hd ht.le (delta d) le_rfl hD
  rw [← specNorm, ← h0, sub_zero, div_self (Real.Gamma_pos_of_pos hD).ne', mul_one] at h
  have hG : (0 : ℝ) < ∏ j, Real.Gamma (1 + t * ((delta d j : ℕ) : ℝ)) :=
    prod_pos fun j _ => Real.Gamma_pos_of_pos (by positivity)
  have hf : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  have := alternant_delta_ne_zero (delta_injective (d := d))
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hf (pow_ne_zero _ ht.ne')) hG.ne') this) h.symm

/-- The normalized spectral density, as a nonnegative function. -/
noncomputable def specWeight (d : ℕ) (t : ℝ) (x : Fin d → ℝ) : ℝ≥0 :=
  Real.toNNReal (specDensity d t x / specNorm d t)

/-- The spectral law on the orthant. -/
noncomputable def specMeasure (d : ℕ) (t : ℝ) : Measure (Fin d → ℝ) :=
  (orthant d).withDensity fun x => (specWeight d t x : ℝ≥0∞)

theorem measurable_specWeight {t : ℝ} (ht : 0 ≤ t) : Measurable (specWeight d t) :=
  ((measurable_specDensity ht).div_const _).real_toNNReal

theorem coe_specWeight_ae (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂(orthant d), (specWeight d t x : ℝ) = specDensity d t x / specNorm d t := by
  filter_upwards [ae_orthant_pos] with x hx
  exact Real.coe_toNNReal _ (div_nonneg (specDensity_nonneg ht.le hx) (specNorm_pos hd ht).le)

theorem isProbabilityMeasure_specMeasure (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (specMeasure d t) := by
  constructor
  rw [specMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (fun x => (specWeight d t x : ℝ)) (orthant d) :=
    ((integrable_specDensity hd ht.le).div_const (specNorm d t)).congr
      ((coe_specWeight_ae hd ht).mono fun x hx => hx.symm)
  rw [lintegral_coe_eq_integral _ hint, integral_congr_ae (coe_specWeight_ae hd ht),
    integral_div, ← specNorm_eq_integral, div_self (specNorm_pos hd ht).ne', ENNReal.ofReal_one]

theorem integral_specMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hd : 0 < d) {t : ℝ} (ht : 0 < t) (g : (Fin d → ℝ) → E) :
    ∫ x, g x ∂(specMeasure d t) = ∫ x, (specDensity d t x / specNorm d t) • g x ∂(orthant d) := by
  rw [specMeasure, integral_withDensity_eq_integral_smul (measurable_specWeight ht.le)]
  refine integral_congr_ae ((coe_specWeight_ae hd ht).mono fun x hx => ?_)
  simp only [NNReal.smul_def, hx]

theorem ae_specMeasure_pos {t : ℝ} :
    ∀ᵐ x ∂(specMeasure d t), ∀ i, 0 < x i :=
  (withDensity_absolutelyContinuous _ _).ae_le ae_orthant_pos

/-! ### Characters at real diagonal matrices -/

theorem tensorPow_smul {Ω : Type*} [DecidableEq Ω] {k : ℕ} (c : ℂ)
    (A : Matrix Ω Ω ℂ) : tensorPow (k := k) (c • A) = c ^ k • tensorPow A := by
  ext x y
  simp [tensorPow_apply, prod_mul_distrib, prod_const]

theorem glChar_mul_left {q k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k))) (c : ℂ)
    (y : Fin q → ℂ) : glChar q l (fun i => c * y i) = c ^ k * glChar q l y := by
  have : diagonal (fun i => c * y i) = c • diagonal y := by
    rw [← diagonal_smul]; rfl
  rw [glChar, glChar, this, tensorPow_smul, mul_smul_comm, trace_smul, smul_eq_mul]

theorem alternant_ofReal (α : Fin d → ℕ) (y : Fin d → ℝ) :
    alternant α (fun i => (y i : ℂ)) = (alternant (R := ℝ) α y : ℂ) := by
  simp only [alternant_eq_sum]
  push_cast
  rfl

/-- The Weyl character formula at real points. -/
theorem alternant_mul_glChar_ofReal {k : ℕ} {l : IrrepLabel (Equiv.Perm (Fin k))}
    (hl : HasRows d l) (y : Fin d → ℝ) :
    (alternant (R := ℝ) (delta d) y : ℂ) * glChar d l (fun i => (y i : ℂ)) =
      (alternant (R := ℝ) (shiftedPart (part d l)) y : ℂ) := by
  rw [← alternant_ofReal, ← alternant_ofReal]
  exact alternant_mul_glChar hl _

/-- The spectral density times the eigenvalue of the twirl is the gamma integrand. -/
theorem specDensity_mul_glChar {t : ℝ} {k : ℕ} {l : IrrepLabel (Equiv.Perm (Fin k))}
    (hl : HasRows d l) (hd : 0 < d) {x : Fin d → ℝ} (hx : ∀ i, 0 < x i) :
    (specDensity d t x : ℂ) * glChar d l (fun i => (((x i / ∑ j, x j) ^ t : ℝ) : ℂ)) =
      ((alternant (delta d) x * alternant (shiftedPart (part d l)) (fun i => x i ^ t) *
        (∑ i, x i) ^ (-(t * k)) * Real.exp (-∑ i, x i) : ℝ) : ℂ) := by
  set S := ∑ i, x i
  have hS : 0 < S := sum_pos (fun i _ => hx i) ⟨⟨0, hd⟩, mem_univ _⟩
  have hy : (fun i => (((x i / S) ^ t : ℝ) : ℂ)) =
      fun i => ((S ^ (-t) : ℝ) : ℂ) * ((x i ^ t : ℝ) : ℂ) := by
    funext i
    rw [Real.div_rpow (hx i).le hS.le, Real.rpow_neg hS.le]
    push_cast
    ring
  rw [hy, glChar_mul_left]
  have hw := alternant_mul_glChar_ofReal hl (fun i => x i ^ t)
  have hpow : ((S ^ (-t) : ℝ) : ℂ) ^ k = ((S ^ (-(t * k)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hS.le]
    congr 2
    ring
  rw [hpow]
  simp only [specDensity, Complex.ofReal_mul]
  linear_combination (alternant (R := ℝ) (delta d) x : ℂ) * ((S ^ (-(t * k)) : ℝ) : ℂ) *
    (Real.exp (-S) : ℂ) * hw

/-! ### Samples -/

/-- The sample `σ = U diag(x/∑ x) U†`. -/
noncomputable def specSample (x : Fin d → ℝ) (U : unitaryGroup (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) * diagonal (fun i => ((x i / ∑ j, x j : ℝ) : ℂ)) *
    star (U : Matrix (Fin d) (Fin d) ℂ)

theorem specSample_rpow (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) {x : Fin d → ℝ}
    (hx : ∀ i, 0 < x i)
    (U : unitaryGroup (Fin d) ℂ) :
    specSample x U ^ t = (U : Matrix (Fin d) (Fin d) ℂ) *
      diagonal (fun i => (((x i / ∑ j, x j) ^ t : ℝ) : ℂ)) *
        star (U : Matrix (Fin d) (Fin d) ℂ) := by
  have hS : 0 < ∑ j, x j := by
    exact sum_pos (fun j _ => hx j) ⟨⟨0, hd⟩, mem_univ _⟩
  have hD : (diagonal (fun i => ((x i / ∑ j, x j : ℝ) : ℂ))).PosSemidef :=
    PosSemidef.diagonal fun i => Complex.zero_le_real.mpr (div_nonneg (hx i).le hS.le)
  rw [specSample, rpow_conj_unitary hD t U, CFC.rpow_eq_cfc_real hD.nonneg,
    cfc_diagonal _ _ (Real.continuous_rpow_const ht).continuousOn]

theorem specSample_posDef (hd : 0 < d) {x : Fin d → ℝ} (hx : ∀ i, 0 < x i)
    (U : unitaryGroup (Fin d) ℂ) :
    (specSample x U).PosDef := by
  have hS : 0 < ∑ j, x j := by
    exact sum_pos (fun j _ => hx j) ⟨⟨0, hd⟩, mem_univ _⟩
  have hD : (diagonal (fun i => ((x i / ∑ j, x j : ℝ) : ℂ))).PosDef :=
    posDef_diagonal_iff.mpr fun i => Complex.zero_lt_real.mpr (div_pos (hx i) hS)
  have hinj : Function.Injective (star (U : Matrix (Fin d) (Fin d) ℂ)).mulVec := by
    refine Function.LeftInverse.injective (g := fun v => (U : Matrix (Fin d) (Fin d) ℂ) *ᵥ v)
      fun v => ?_
    simp only [mulVec_mulVec, (mem_unitaryGroup_iff.mp U.2), one_mulVec]
  have := hD.conjTranspose_mul_mul_same hinj
  rwa [star_eq_conjTranspose, conjTranspose_conjTranspose] at this

theorem trace_specSample (hd : 0 < d) {x : Fin d → ℝ} (hx : ∀ i, 0 < x i)
    (U : unitaryGroup (Fin d) ℂ) :
    (specSample x U).trace = 1 := by
  have hS : 0 < ∑ j, x j := by
    exact sum_pos (fun j _ => hx j) ⟨⟨0, hd⟩, mem_univ _⟩
  rw [specSample, trace_mul_cycle, mem_unitaryGroup_iff'.mp U.2, Matrix.one_mul, trace_diagonal]
  rw [← Complex.ofReal_sum, ← sum_div, div_self hS.ne', Complex.ofReal_one]

end TensorPower
