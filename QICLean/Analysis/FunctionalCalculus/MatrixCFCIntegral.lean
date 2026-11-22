/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Integrating functional calculus on a finite spectrum

The scalar-to-operator integral step needed for Wolf Theorem 5.12 requires
only integrability at each eigenvalue. No continuity in the scalar variable,
uniform bound, or finiteness of the measure is necessary in finite dimensions.
-/

open MeasureTheory Matrix Unitary
open scoped Matrix

noncomputable section

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra

namespace Matrix.IsHermitian

variable {n α : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace α]
variable {μ : Measure α} {A : Matrix n n ℂ}

private def spectralLinearMap (hA : A.IsHermitian) : (n → ℝ) →ₗ[ℝ] Matrix n n ℂ where
  toFun v := conjStarAlgAut ℂ _ hA.eigenvectorUnitary
    (diagonal (fun i => (v i : ℂ)))
  map_add' v w := by
    have hd : diagonal (fun i => ((v + w) i : ℂ)) =
        diagonal (fun i => (v i : ℂ)) + diagonal (fun i => (w i : ℂ)) := by
      rw [diagonal_add]
      congr 1
      ext i
      simp
    rw [hd]
    simp only [conjStarAlgAut_apply, mul_add, add_mul]
  map_smul' c v := by
    rw [show (fun i => ((c • v) i : ℂ)) =
      c • (fun i => (v i : ℂ)) by ext; simp]
    simp only [diagonal_smul, conjStarAlgAut_apply, Matrix.mul_smul, Matrix.smul_mul,
      RingHom.id_apply]

/-- Integrability at the finitely many eigenvalues suffices for integrability
of matrix functional calculus, the finite-dimensional step in Wolf Theorem 5.12. -/
theorem integrable_cfc_of_eigenvalues (hA : A.IsHermitian) (k : α → ℝ → ℝ)
    (hk : ∀ i, Integrable (fun t => k t (hA.eigenvalues i)) μ) :
    Integrable (fun t => cfc (k t) A) μ := by
  have h := (LinearMap.toContinuousLinearMap (spectralLinearMap hA)).integrable_comp
    (Integrable.of_eval hk)
  simpa [LinearMap.coe_toContinuousLinearMap', spectralLinearMap, hA.cfc_eq,
    IsHermitian.cfc, Function.comp_def] using h

/-- Scalar functional calculus commutes with integration under only spectral
integrability. This supplies the interchange in Wolf Theorem 5.12 without
assuming an operator-valued representation as a hypothesis. -/
theorem cfc_integral_of_eigenvalues (hA : A.IsHermitian) (k : α → ℝ → ℝ)
    (hk : ∀ i, Integrable (fun t => k t (hA.eigenvalues i)) μ) :
    cfc (fun x => ∫ t, k t x ∂μ) A = ∫ t, cfc (k t) A ∂μ := by
  have h := (LinearMap.toContinuousLinearMap (spectralLinearMap hA)).integral_comp_comm
    (Integrable.of_eval hk)
  have heq : (∫ t, (fun i => k t (hA.eigenvalues i)) ∂μ) =
      fun i => ∫ t, k t (hA.eigenvalues i) ∂μ := by
    funext i
    exact eval_integral hk i
  rw [heq] at h
  simpa [LinearMap.coe_toContinuousLinearMap', spectralLinearMap, hA.cfc_eq,
    IsHermitian.cfc, Function.comp_def] using h.symm

end Matrix.IsHermitian
