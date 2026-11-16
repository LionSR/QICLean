/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixCFCIntegral
import QICLean.Channel.Schwarz.OperatorJensenAux
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integral assembly for operator Jensen inequalities

The integral step in Wolf Theorem 5.12 applies to any measurable parameter space,
not just the measures representing real powers. Integrability is required at both
matrices; no finiteness assumption on the measure is imposed. This is a prerequisite
for the general theorem, not a characterization of operator-convex functions.
-/

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra

namespace Matrix

variable {n m : Type} {α : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable [MeasurableSpace α] {μ : Measure α}

/-- Integrating almost-everywhere matrix inequalities commutes with a linear map.
This is the ordered integral step in Wolf Theorem 5.12, allowing different input
and output dimensions and arbitrary measures. Positivity of the map is needed to
establish the pointwise inequality, not to integrate it. -/
theorem integral_le_map_integral
    (T : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    {F : α → Matrix n n ℂ} {G : α → Matrix m m ℂ}
    (hF : Integrable F μ) (hG : Integrable G μ)
    (h : ∀ᵐ t ∂μ, G t ≤ T (F t)) :
    (∫ t, G t ∂μ) ≤ T (∫ t, F t ∂μ) := by
  have hTF : Integrable (fun t => T (F t)) μ := by
    simpa [LinearMap.coe_toContinuousLinearMap'] using
      (LinearMap.toContinuousLinearMap T).integrable_comp hF
  have hcomm : (∫ t, T (F t) ∂μ) = T (∫ t, F t ∂μ) := by
    simpa [LinearMap.coe_toContinuousLinearMap'] using
      (LinearMap.toContinuousLinearMap T).integral_comp_comm hF
  rw [← hcomm]
  exact integral_mono_ae hG hTF h

/-- Jensen passes from an almost-everywhere family of scalar functional-calculus
kernels to a represented function. The representation is required only at the
input and its image. This is the integral assembly in Wolf Theorem 5.12; it does
not assert the integral characterization in Theorem 5.8. -/
theorem cfc_jensen_of_integral_representation
    (T : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (A : Matrix n n ℂ) (f : ℝ → ℝ) (k : α → ℝ → ℝ)
    (hA : Integrable (fun t => cfc (k t) A) μ)
    (hTA : Integrable (fun t => cfc (k t) (T A)) μ)
    (hfA : cfc f A = ∫ t, cfc (k t) A ∂μ)
    (hfTA : cfc f (T A) = ∫ t, cfc (k t) (T A) ∂μ)
    (hk : ∀ᵐ t ∂μ, cfc (k t) (T A) ≤ T (cfc (k t) A)) :
    cfc f (T A) ≤ T (cfc f A) := by
  rw [hfA, hfTA]
  exact integral_le_map_integral T hA hTA hk

/-- Any integrable positive mixture of resolvent kernels satisfies subunital
Jensen. This supplies the measure assembly needed in Wolf Theorem 5.12 without
assuming a finite representing measure or restricting the mixture to powers.
The kernel exponent is an arbitrary fixed number in `(1,2)`. -/
theorem cfc_jensen_of_resolvent_representation
    {D : ℕ}
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ} (hT : IsPositiveMap T)
    (hSub : T 1 ≤ (1 : Matrix (Fin D) (Fin D) ℂ))
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.PosSemidef)
    (f : ℝ → ℝ) {p : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2)
    (t : α → ℝ) (ht : ∀ᵐ i ∂μ, 0 < t i)
    (hAint : Integrable (fun i => cfc (Real.rpowIntegrand₁₂ p (t i)) A) μ)
    (hTAint : Integrable (fun i => cfc (Real.rpowIntegrand₁₂ p (t i)) (T A)) μ)
    (hfA : cfc f A = ∫ i, cfc (Real.rpowIntegrand₁₂ p (t i)) A ∂μ)
    (hfTA : cfc f (T A) = ∫ i, cfc (Real.rpowIntegrand₁₂ p (t i)) (T A) ∂μ) :
    cfc f (T A) ≤ T (cfc f A) := by
  apply cfc_jensen_of_integral_representation T A f
    (fun i => Real.rpowIntegrand₁₂ p (t i)) hAint hTAint hfA hfTA
  filter_upwards [ht] with i hi
  exact TNLean.OperatorJensen.positiveMap_rpowIntegrand₁₂_jensen hT hSub hA hp hi

/-- Scalar spectral representations suffice for integral Jensen. Unlike the
operator-valued assembly theorem, all integrability assumptions here concern
real functions at finitely many eigenvalues. No continuity is required. -/
theorem cfc_jensen_of_scalar_integral
    (T : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hTA : (T A).IsHermitian)
    (k : α → ℝ → ℝ)
    (hkA : ∀ i, Integrable (fun t => k t (hA.eigenvalues i)) μ)
    (hkTA : ∀ i, Integrable (fun t => k t (hTA.eigenvalues i)) μ)
    (hk : ∀ᵐ t ∂μ, cfc (k t) (T A) ≤ T (cfc (k t) A)) :
    cfc (fun x => ∫ t, k t x ∂μ) (T A) ≤
      T (cfc (fun x => ∫ t, k t x ∂μ) A) := by
  exact cfc_jensen_of_integral_representation T A _ k
    (hA.integrable_cfc_of_eigenvalues k hkA)
    (hTA.integrable_cfc_of_eigenvalues k hkTA)
    (hA.cfc_integral_of_eigenvalues k hkA)
    (hTA.cfc_integral_of_eigenvalues k hkTA) hk

end Matrix
