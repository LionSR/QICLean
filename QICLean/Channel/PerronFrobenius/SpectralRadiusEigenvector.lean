/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixCongruence
import QICLean.Channel.Irreducible.CollatzWielandt
import QICLean.Channel.Irreducible.Similarity
import QICLean.Channel.MaximallyMixed
import QICLean.Channel.Peripheral.SpectralRadius
import QICLean.Channel.PerronFrobenius.Existence
import QICLean.Channel.SupportCompletion

/-!
# Spectral-radius eigenvectors of positive matrix maps

This module proves Wolf Theorem 6.5 for an arbitrary positive map on a
nonzero full matrix algebra.  The theorem is stated, without a proof, at
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 743--747.

The proof supplied here regularizes the map by a positive trace-and-prepare
term.  The regularized maps have positive-definite density eigenvectors by
the density-matrix fixed-point theorem.  Compactness gives a limiting density
eigenvector for the original map.  An upper Collatz--Wielandt bound, obtained
from positive congruence similarity and the Russo--Dye estimate, identifies
the limiting eigenvalue with the spectral radius.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal ENNReal
open Matrix

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-! ## The upper Collatz--Wielandt spectral bound -/

/-- A positive map satisfying `T X ≤ a X` at a positive-definite density
matrix has spectral radius at most `a`.

This is a reusable upper Collatz--Wielandt bound in the terminology of Wolf
Equation (6.30).  Conjugating by `X¹⁄²` makes the comparison vector the
identity.  The positive-similarity invariance of the spectrum and the
Russo--Dye estimate of Wolf Proposition 6.1 then give the result. -/
theorem spectralRadius_le_of_upperCollatzWielandtFeasible_of_posDef [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T)
    {X : Mat} {a : ℝ} (hX : X.PosDef)
    (hUpper : UpperCollatzWielandtFeasible T X a) :
    spectralRadius ℂ (Module.End.toContinuousLinearMap Mat T) ≤ ENNReal.ofReal a := by
  let S : Mat := CFC.sqrt X
  have hS_herm : Sᴴ = S := by
    simpa [S] using Matrix.conjTranspose_cfc_sqrt (ρ := X)
  have hS_det : S.det ≠ 0 := by
    simpa [S] using hX.isUnit_det_cfc_sqrt.ne_zero
  have hS_inv_mul : S⁻¹ * S = 1 :=
    Matrix.nonsing_inv_mul S (Ne.isUnit hS_det)
  have hS_mul_inv : S * S⁻¹ = 1 :=
    Matrix.mul_nonsing_inv S (Ne.isUnit hS_det)
  have hS_sq : S * S = X := by
    change CFC.sqrt X * CFC.sqrt X = X
    exact CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg
  have hSinv_X_Sinv : S⁻¹ * X * S⁻¹ = 1 := by
    calc
      S⁻¹ * X * S⁻¹ = S⁻¹ * (S * S) * S⁻¹ := by rw [hS_sq]
      _ = (S⁻¹ * S) * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hS_inv_mul, hS_mul_inv, Matrix.one_mul]
  let U : Mat →ₗ[ℂ] Mat := similarityMap (D := D) S T
  have hU : IsPositiveMap U := hT.similarityMap S
  have ha : 0 ≤ a := upperCollatzWielandtFeasible_nonneg T hT hUpper
  have hgap : (((a : ℂ) • (1 : Mat)) - U 1).PosSemidef := by
    have hcongr := hUpper.2.mul_mul_conjTranspose_same S⁻¹
    have hSinv_herm : (S⁻¹)ᴴ = S⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, hS_herm]
    rw [hSinv_herm] at hcongr
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      hSinv_X_Sinv] at hcongr
    have hUone : U 1 = S⁻¹ * T X * S⁻¹ := by
      simp [U, similarityMap, hS_herm, hS_sq]
    simpa only [hUone] using hcongr
  have hUone_nonneg : 0 ≤ U 1 := (hU 1 Matrix.PosSemidef.one).nonneg
  have hUone_le : U 1 ≤ (a : ℂ) • (1 : Mat) := by
    rw [Matrix.le_iff]
    exact hgap
  have hnorm : ‖U 1‖ ≤ a := by
    have hmono : ‖U 1‖ ≤ ‖(a : ℂ) • (1 : Mat)‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le (A := Mat) hUone_nonneg hUone_le
    simpa [norm_smul, abs_of_nonneg ha] using hmono
  have hsim_alg :
      U = (Matrix.congruenceLinearEquiv S hS_det).symm.conjAlgEquiv ℂ T := by
    apply LinearMap.ext
    intro A
    ext i j
    simp [U, similarityMap, LinearEquiv.conjAlgEquiv_apply, Matrix.mul_assoc]
  have hspec : spectrum ℂ U = spectrum ℂ T := by
    rw [hsim_alg]
    exact AlgEquiv.spectrum_eq
      ((Matrix.congruenceLinearEquiv S hS_det).symm.conjAlgEquiv ℂ) T
  let aNN : ℝ≥0 := ⟨a, ha⟩
  have hrad := spectralRadius_le_of_forall_eigenvalue_nnnorm_le
    T aNN (fun μ hμ ↦ by
      have hμU : Module.End.HasEigenvalue U μ := by
        rw [Module.End.hasEigenvalue_iff_mem_spectrum, hspec]
        exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hμ
      have hμnorm : ‖μ‖ ≤ a :=
        (hU.eigenvalue_norm_le_norm_map_one μ hμU).trans hnorm
      exact_mod_cast hμnorm)
  calc
    spectralRadius ℂ (Module.End.toContinuousLinearMap Mat T) ≤
        (aNN : ℝ≥0∞) := hrad
    _ = ENNReal.ofReal a := by rw [ENNReal.coe_nnreal_eq]; rfl

/-! ## Positive trace regularization -/

/-- Add a positive trace-and-prepare term to a positive map. -/
private noncomputable def positiveTraceRegularization
    (T : Mat →ₗ[ℂ] Mat) (ε : ℝ) : Mat →ₗ[ℂ] Mat :=
  T + (ε : ℂ) • Matrix.tracePrepareMap (Matrix.maximallyMixedOn (dA := D))

private theorem positiveTraceRegularization_apply_density
    (T : Mat →ₗ[ℂ] Mat) (ε : ℝ) {X : Mat} (hX : X ∈ densityMatrices D) :
    positiveTraceRegularization T ε X =
      T X + (ε : ℂ) • Matrix.maximallyMixedOn := by
  simp [positiveTraceRegularization, Matrix.tracePrepareMap_apply, hX.2]

private theorem positiveTraceRegularization_isPositive
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T)
    {ε : ℝ} (hε : 0 ≤ ε) :
    IsPositiveMap (positiveTraceRegularization T ε) := by
  have hprepare : IsPositiveMap
      (Matrix.tracePrepareMap (Matrix.maximallyMixedOn (dA := D)) : Mat →ₗ[ℂ] Mat) :=
    (Matrix.tracePrepareMap_isKrausCP
      Matrix.maximallyMixedOn Matrix.maximallyMixedOn_posSemidef).isPositiveMap
  intro X hX
  exact (hT X hX).add ((hprepare X hX).smul (by exact_mod_cast hε))

/-- The regularized map has a positive-definite density eigenvector.  Its
eigenvalue is an upper Collatz--Wielandt feasible value for the original map
and is given by the trace formula used in the limiting argument. -/
private theorem exists_positiveTraceRegularization_eigenpair [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X ∈ densityMatrices D, ∃ r : ℝ,
      0 < r ∧ X.PosDef ∧
        positiveTraceRegularization T ε X = (r : ℂ) • X ∧
        UpperCollatzWielandtFeasible T X r ∧
        r = (Matrix.trace (T X)).re + ε := by
  have hregPos : IsPositiveMap (positiveTraceRegularization T ε) :=
    positiveTraceRegularization_isPositive T hT hε.le
  have hεmixed :
      ((ε : ℂ) • Matrix.maximallyMixedOn (dA := D)).PosDef := by
    simpa only [Complex.coe_smul] using
      (Matrix.maximallyMixedOn_posDef (dA := D)).smul hε
  have hregPd : ∀ X ∈ densityMatrices D,
      (positiveTraceRegularization T ε X).PosDef := by
    intro X hX
    rw [positiveTraceRegularization_apply_density T ε hX]
    exact Matrix.PosDef.posSemidef_add (hT X hX.1) hεmixed
  have hregNe : ∀ X ∈ densityMatrices D,
      positiveTraceRegularization T ε X ≠ 0 := by
    intro X hX
    exact (Matrix.PosDef.isUnit (hregPd X hX)).ne_zero
  obtain ⟨X, hX, r, hr, hEig⟩ :=
    exists_density_eigenvector_of_positive_of_nonvanishing
      (positiveTraceRegularization T ε) hregPos hregNe
  have hXpd : X.PosDef := by
    have hscaled := (hregPd X hX).smul (inv_pos.mpr hr)
    simpa [hEig, smul_smul, hr.ne'] using hscaled
  refine ⟨X, hX, r, hr, hXpd, hEig, ?_, ?_⟩
  · refine ⟨hX, ?_⟩
    rw [← hEig, positiveTraceRegularization_apply_density T ε hX]
    simpa only [add_sub_cancel_left] using hεmixed.posSemidef
  · sorry
