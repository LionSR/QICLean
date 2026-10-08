/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralKronecker
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Complex spectral functions of Hermitian matrices are basis independent

For a Hermitian matrix `A` with eigenvector unitary `U` and eigenvalues `λ`, a complex
function `g` of `A` is `spectralFun U (g ∘ λ)`.  Splitting `g` into real and imaginary
parts expresses it through the real continuous functional calculus, so it depends only
on `A`.  In particular, for every real `h`, the function `g` of `cfc h A`, taken in the
eigenbasis of `cfc h A`, is `spectralFun U (g ∘ h ∘ λ)` in the eigenbasis of `A`.

## Main results

* `Matrix.IsHermitian.cfc_eq_spectralFun`.
* `Matrix.IsHermitian.spectralFun_eq_cfc_re_add_im`.
* `Matrix.IsHermitian.spectralFun_cfc_comp`.
* `Matrix.IsHermitian.cfc_affine`.
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

theorem IsHermitian.cfc_eq_spectralFun (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = spectralFun hA.eigenvectorUnitary (fun k => ((f (hA.eigenvalues k) : ℝ) : ℂ)) := by
  rw [hA.cfc_eq]
  rfl

theorem IsHermitian.spectralFun_eq_cfc_re_add_im (hA : A.IsHermitian) (g : ℝ → ℂ) :
    spectralFun hA.eigenvectorUnitary (fun k => g (hA.eigenvalues k)) =
      cfc (fun t => (g t).re) A + Complex.I • cfc (fun t => (g t).im) A := by
  rw [hA.cfc_eq_spectralFun, hA.cfc_eq_spectralFun, ← spectralFun_smul, ← spectralFun_add]
  congr 1
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]
  exact (Complex.re_add_im _).symm

/-- A complex function of `cfc h A`, in the eigenbasis of `cfc h A`, equals the composite
function of `A` in the eigenbasis of `A`. -/
theorem IsHermitian.spectralFun_cfc_comp (hA : A.IsHermitian) (h : ℝ → ℝ)
    (hB : (cfc h A).IsHermitian) (g : ℝ → ℂ) :
    spectralFun hB.eigenvectorUnitary (fun k => g (hB.eigenvalues k)) =
      spectralFun hA.eigenvectorUnitary (fun k => g (h (hA.eigenvalues k))) := by
  have hfin : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f =>
    (finite_real_spectrum (A := A)).continuousOn f
  have hfin' : ∀ f : ℝ → ℝ, ContinuousOn f (h '' spectrum ℝ A) := fun f =>
    ((finite_real_spectrum (A := A)).image h).continuousOn f
  rw [hB.spectralFun_eq_cfc_re_add_im, ← cfc_comp (fun t => (g t).re) h A hA.isSelfAdjoint
    (hfin' _) (hfin _), ← cfc_comp (fun t => (g t).im) h A hA.isSelfAdjoint (hfin' _) (hfin _)]
  exact (hA.spectralFun_eq_cfc_re_add_im (g ∘ h)).symm

/-- The affine function `t ↦ a t + b` of a Hermitian matrix. -/
theorem IsHermitian.cfc_affine (hA : A.IsHermitian) (a b : ℝ) :
    cfc (fun t : ℝ => a * t + b) A = a • A + b • (1 : Matrix n n ℂ) := by
  have hfin : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f =>
    (finite_real_spectrum (A := A)).continuousOn f
  rw [cfc_add (a := A) (fun t : ℝ => a * t) (fun _ => b) (hfin _) (hfin _),
    cfc_const_mul a (fun t : ℝ => t) A (hfin _), cfc_id' ℝ A hA.isSelfAdjoint,
    cfc_const b A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]

end Matrix

end
