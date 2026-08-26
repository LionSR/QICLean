/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.MatrixSqrt
import QICLean.Channel.GaugeConjugation
import QICLean.Channel.Schwarz.Basic

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Gauge normalizations for finite Kraus families

Positive definite fixed points and eigenvectors of a Kraus map or its adjoint give the standard
trace-preserving and unital gauge normalizations.

## Main declarations

* `Kraus.tpGauge`: the gauged Kraus family `i ↦ ρ^{1/2} K i ρ^{-1/2}`.
* `Kraus.unitalGauge`: the gauged Kraus family `i ↦ ρ^{-1/2} K i ρ^{1/2}`.
* `Kraus.spectralUnitalGauge`: the unital gauge with spectral-radius normalization.
* `Kraus.tpGauge_isTP_of_map_conjTranspose_eigenvector`: TP normalization from a positive
  adjoint-map eigenvector.
* `Kraus.spectralUnitalGauge_isUnital_of_map_eigenvector`: unital normalization from a positive
  Kraus-map eigenvector.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Gauge-transformed Kraus family `B i = ρ^{1/2} K i ρ^{-1/2}`.

We implement `ρ^{1/2}` as `CFC.sqrt ρ`.
(For `ρ` positive definite, this is invertible.) -/
noncomputable def tpGauge (K : Fin d → Mat) (ρ : Mat) : Fin d → Mat :=
  fun i => (CFC.sqrt ρ) * K i * (CFC.sqrt ρ)⁻¹

/-- **TP normalisation from an adjoint fixed point.**

Assume `ρ` is positive definite and fixed by the conjugate-transposed Kraus map
`X ↦ ∑ i, (K i)ᴴ * X * K i`. Then the gauged family `tpGauge K ρ` is trace
preserving: `∑ i, (B i)ᴴ * B i = I`.

This is the standard "left-canonical" gauge construction, the specialization
`S = ρ^{1/2}` of `gauged_isTP_of_map_conjTranspose_fixedPoint`. -/
theorem tpGauge_isTP_of_map_conjTranspose_fixedPoint
    (K : Fin d → Mat) (ρ : Mat)
    (hρ : ρ.PosDef)
    (hfix : mapLM (fun i => (K i)ᴴ) ρ = ρ) :
    IsTP (tpGauge K ρ) := by
  have hS_herm : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := Matrix.conjTranspose_cfc_sqrt (ρ := ρ)
  have hStS : (CFC.sqrt ρ)ᴴ * CFC.sqrt ρ = ρ := by
    rw [hS_herm]
    simpa using CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg
  exact gauged_isTP_of_map_conjTranspose_fixedPoint K (CFC.sqrt ρ) ρ
    hρ.isUnit_det_cfc_sqrt hStS (by simpa only [mapLM_apply] using hfix)

/-- **TP normalization from a positive adjoint-map eigenvector.**

If `ρ` is positive definite and the conjugate-transposed Kraus map sends `ρ` to
`r • ρ` for a positive real number `r`, then applying `tpGauge` after scaling the
family by the inverse square root of `r` gives a trace-preserving family. -/
theorem tpGauge_isTP_of_map_conjTranspose_eigenvector
    (K : Fin d → Mat) (ρ : Mat) (r : ℝ)
    (hρ : ρ.PosDef) (hr : 0 < r)
    (heig : mapLM (fun i => (K i)ᴴ) ρ = (r : ℂ) • ρ) :
    IsTP (tpGauge (fun j => (↑((Real.sqrt r)⁻¹) : ℂ) • K j) ρ) := by
  let c : ℝ := (Real.sqrt r)⁻¹
  let K' : Fin d → Matrix (Fin D) (Fin D) ℂ := fun i => (↑c : ℂ) • K i
  have hstar_c : star (↑c : ℂ) = (↑c : ℂ) := by
    rw [RCLike.star_def, Complex.conj_ofReal]
  have hcc : c * c = r⁻¹ := by
    rw [show c = (Real.sqrt r)⁻¹ from rfl, ← sq, inv_pow, Real.sq_sqrt hr.le]
  have hc_sq : (↑c : ℂ) * (↑c : ℂ) = (↑r : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, hcc, Complex.ofReal_inv]
  have hfix : mapLM (fun i => (K' i)ᴴ) ρ = ρ := by
    simp only [K', mapLM_apply, map_apply, Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_star]
    simp_rw [hstar_c, hc_sq]
    rw [← Finset.smul_sum]
    have hsum : ∑ i : Fin d, (K i)ᴴ * ρ * ((K i)ᴴ)ᴴ =
        mapLM (fun i => (K i)ᴴ) ρ := by
      simp [mapLM_apply]
    rw [hsum, heig, smul_smul, inv_mul_cancel₀, one_smul]
    exact_mod_cast hr.ne'
  exact tpGauge_isTP_of_map_conjTranspose_fixedPoint K' ρ hρ hfix

/-- Gauge-transformed Kraus family `B i = (sqrt ρ)⁻¹ K i (sqrt ρ)`. -/
noncomputable def unitalGauge (K : Fin d → Mat) (ρ : Mat) : Fin d → Mat :=
  fun i => (CFC.sqrt ρ)⁻¹ * K i * CFC.sqrt ρ

/-- Rescaled right-canonical gauge obtained by multiplying `unitalGauge K ρ` by the
inverse square root of `r`. -/
noncomputable def spectralUnitalGauge
    (K : Fin d → Mat) (r : ℝ) (ρ : Mat) : Fin d → Mat :=
  fun i => (↑((Real.sqrt r)⁻¹) : ℂ) • unitalGauge K ρ i

/-- **Unital normalization from a positive Kraus-map eigenvector.**

If `ρ` is positive definite and `mapLM K ρ = r • ρ` for a positive real number
`r`, then `spectralUnitalGauge K r ρ` is unital. -/
theorem spectralUnitalGauge_isUnital_of_map_eigenvector
    (K : Fin d → Mat) (ρ : Mat) (r : ℝ)
    (hρ : ρ.PosDef) (hr : 0 < r)
    (hfix : mapLM K ρ = (r : ℂ) • ρ) :
    IsUnital (spectralUnitalGauge K r ρ) := by
  classical
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt ρ
  let c : ℂ := (↑((Real.sqrt r)⁻¹) : ℂ)
  have hc_star : star c = c := by
    rw [show c = (↑((Real.sqrt r)⁻¹) : ℂ) from rfl, RCLike.star_def,
      Complex.conj_ofReal]
  have hc_sq : c * c = (r : ℂ)⁻¹ := by
    have hcc : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ = r⁻¹ := by
      rw [← sq, inv_pow, Real.sq_sqrt hr.le]
    rw [show c = (↑((Real.sqrt r)⁻¹) : ℂ) from rfl, ← Complex.ofReal_mul, hcc,
      Complex.ofReal_inv]
  have hS_mul : S * S = ρ := by
    simpa [S] using CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg
  have hS_herm : Sᴴ = S := by
    simpa [S] using Matrix.conjTranspose_cfc_sqrt ρ
  have hSS : S * Sᴴ = ρ := by
    simpa [hS_herm] using hS_mul
  have hdet : IsUnit S.det := by
    simpa [S] using Matrix.PosDef.isUnit_det_cfc_sqrt hρ
  have hSinv_mul : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hdet
  have hdetT : IsUnit (Sᴴ.det) := by
    simpa [Matrix.det_conjTranspose] using (IsUnit.star hdet)
  have hStmul_inv : Sᴴ * (Sᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv Sᴴ hdetT
  have h_term : ∀ i : Fin d,
      (c • (S⁻¹ * K i * S)) * (c • (S⁻¹ * K i * S))ᴴ =
        (r : ℂ)⁻¹ • (S⁻¹ * (K i * ρ * (K i)ᴴ) * (Sᴴ)⁻¹) := by
    intro i
    rw [Matrix.conjTranspose_smul, hc_star]
    calc
      (c • (S⁻¹ * K i * S)) * (c • (S⁻¹ * K i * S)ᴴ)
          = (c * c) • ((S⁻¹ * K i * S) * (S⁻¹ * K i * S)ᴴ) := by
              simp [smul_smul]
      _ = (r : ℂ)⁻¹ • ((S⁻¹ * K i * S) * (S⁻¹ * K i * S)ᴴ) := by
              rw [hc_sq]
      _ = (r : ℂ)⁻¹ • (S⁻¹ * (K i * ρ * (K i)ᴴ) * (Sᴴ)⁻¹) := by
              congr 1
              rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
                Matrix.conjTranspose_nonsing_inv]
              simp [Matrix.mul_assoc, ← hSS]
  have h_sum_eq : ∑ i : Fin d, K i * ρ * (K i)ᴴ = (r : ℂ) • ρ := by
    simpa [mapLM_apply, Matrix.mul_assoc] using hfix
  change
    (∑ i : Fin d, (c • (S⁻¹ * K i * S)) * (c • (S⁻¹ * K i * S))ᴴ) = 1
  simp_rw [h_term]
  rw [← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum, h_sum_eq]
  have hr_ne : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  change (r : ℂ)⁻¹ • (S⁻¹ * ((r : ℂ) • ρ) * (Sᴴ)⁻¹) = 1
  calc
    (r : ℂ)⁻¹ • (S⁻¹ * ((r : ℂ) • ρ) * (Sᴴ)⁻¹)
        = (r : ℂ)⁻¹ • ((r : ℂ) • (S⁻¹ * ρ * (Sᴴ)⁻¹)) := by
            simp [Matrix.mul_assoc]
    _ = ((r : ℂ)⁻¹ * (r : ℂ)) • (S⁻¹ * ρ * (Sᴴ)⁻¹) := by
            rw [smul_smul]
    _ = S⁻¹ * ρ * (Sᴴ)⁻¹ := by
            rw [inv_mul_cancel₀ hr_ne, one_smul]
    _ = 1 := by
            rw [← hSS]
            simp [Matrix.mul_assoc, hSinv_mul, hStmul_inv]

/-- **Unital normalization from a positive Kraus-map fixed point.**

If `ρ` is positive definite and fixed by `mapLM K`, then `unitalGauge K ρ` is
unital. -/
theorem unitalGauge_isUnital_of_map_fixedPoint
    (K : Fin d → Mat) (ρ : Mat)
    (hρ : ρ.PosDef) (hfix : mapLM K ρ = ρ) :
    IsUnital (unitalGauge K ρ) := by
  classical
  have hfix_one : mapLM K ρ = (1 : ℂ) • ρ := by
    simpa using hfix
  have h :=
    spectralUnitalGauge_isUnital_of_map_eigenvector
      (d := d) (D := D) K ρ 1 hρ zero_lt_one hfix_one
  change ∑ i : Fin d, unitalGauge K ρ i * (unitalGauge K ρ i)ᴴ = 1
  change ∑ i : Fin d,
    spectralUnitalGauge K 1 ρ i * (spectralUnitalGauge K 1 ρ i)ᴴ = 1 at h
  simpa [spectralUnitalGauge] using h

end Kraus
