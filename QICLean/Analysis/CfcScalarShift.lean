/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Order

/-!
# Functional calculus after a scalar energy shift

A scalar energy shift can be composed with any function on a finite real spectrum.
This auxiliary supports the centered hard and soft truncations in ALVV,
arXiv:1602.08828v2, Definitions `def:hard-trunc` and `def:soft-trunc`,
lines 873–886 and 1178–1185.
-/

open scoped MatrixOrder ComplexOrder

namespace Matrix

/-- Functional calculus of an energy-centered Hermitian matrix is composition with the
scalar translation. Every function on the finite spectrum is continuous there.
Auxiliary to ALVV, arXiv:1602.08828v2, `def:hard-trunc` and `def:soft-trunc`,
lines 873–886 and 1178–1185. -/
theorem IsHermitian.cfc_sub_smul_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (g : ℝ → ℝ) (e : ℝ) :
    cfc g (A - (e : ℂ) • 1) = cfc (fun x : ℝ ↦ g (x - e)) A := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  have hshift : cfc (fun x : ℝ ↦ x - e) A = A - (e : ℂ) • 1 := by
    rw [cfc_sub _ _ A (hc _) (hc _), cfc_id' ℝ A hA.isSelfAdjoint,
      cfc_const e A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one,
      ← Complex.coe_smul]
  rw [← hshift, ← cfc_comp' g (fun x : ℝ ↦ x - e) A
    ((A.finite_real_spectrum.image (fun x : ℝ ↦ x - e)).continuousOn g)
    (hc _) hA.isSelfAdjoint]

end Matrix
