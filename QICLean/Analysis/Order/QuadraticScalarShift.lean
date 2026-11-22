/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Real scalar shifts of quadratic forms

Subtracting a real scalar multiple of the identity subtracts that scalar
times the squared norm from the real quadratic form. This identity
is used when changing between an actual Hamiltonian and its centered
regional operator in ALVV, arXiv:1602.08828v2, Definition `def:soft-trunc`,
lines 1178–1185, and the energy estimate at line 1807.
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A real shift changes the quadratic form by the scalar times the
squared norm. Auxiliary to ALVV, arXiv:1602.08828v2,
Definition `def:soft-trunc`, lines 1178–1185. -/
theorem re_inner_sub_real_smul_one (H : E →L[𝕜] E) (a : ℝ) (x : E) :
    RCLike.re ⟪(H - (a : 𝕜) • 1) x, x⟫_𝕜 =
      RCLike.re ⟪H x, x⟫_𝕜 - a * ‖x‖ ^ 2 := by
  rw [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, inner_smul_left]
  simp only [RCLike.conj_ofReal, map_sub, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

/-- The corresponding real scalar addition identity. Auxiliary to the
centered regional energy in ALVV, arXiv:1602.08828v2, line 1807. -/
theorem re_inner_add_real_smul_one (H : E →L[𝕜] E) (a : ℝ) (x : E) :
    RCLike.re ⟪(H + (a : 𝕜) • 1) x, x⟫_𝕜 =
      RCLike.re ⟪H x, x⟫_𝕜 + a * ‖x‖ ^ 2 := by
  simpa only [RCLike.ofReal_neg, neg_smul, sub_neg_eq_add, neg_mul] using
    H.re_inner_sub_real_smul_one (-a) x

end ContinuousLinearMap

namespace Matrix

open scoped Matrix.Norms.L2Operator

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- The real quadratic form of a scalar-shifted native matrix.
Auxiliary to ALVV, arXiv:1602.08828v2, the energy estimate at line 1807. -/
theorem re_inner_toEuclideanCLM_sub_real_smul_one (A : Matrix ι ι 𝕜)
    (a : ℝ) (x : EuclideanSpace 𝕜 ι) :
    RCLike.re ⟪toEuclideanCLM (𝕜 := 𝕜) (n := ι) (A - (a : 𝕜) • 1) x, x⟫_𝕜 =
      RCLike.re ⟪toEuclideanCLM (𝕜 := 𝕜) (n := ι) A x, x⟫_𝕜 - a * ‖x‖ ^ 2 := by
  simpa only [map_sub, map_smul, map_one] using
    (toEuclideanCLM (𝕜 := 𝕜) (n := ι) A).re_inner_sub_real_smul_one a x

/-- The corresponding real quadratic form for scalar addition.
Auxiliary to ALVV, arXiv:1602.08828v2, the energy estimate at line 1807. -/
theorem re_inner_toEuclideanCLM_add_real_smul_one (A : Matrix ι ι 𝕜)
    (a : ℝ) (x : EuclideanSpace 𝕜 ι) :
    RCLike.re ⟪toEuclideanCLM (𝕜 := 𝕜) (n := ι) (A + (a : 𝕜) • 1) x, x⟫_𝕜 =
      RCLike.re ⟪toEuclideanCLM (𝕜 := 𝕜) (n := ι) A x, x⟫_𝕜 + a * ‖x‖ ^ 2 := by
  simpa only [map_add, map_smul, map_one] using
    (toEuclideanCLM (𝕜 := 𝕜) (n := ι) A).re_inner_add_real_smul_one a x

end Matrix

namespace Matrix

/-- The complex matrix form of the real scalar-shift identity, with the
ordinary real-to-complex coefficient and complex real part. This supports
ALVV, arXiv:1602.08828v2, Definition `def:soft-trunc`, lines 1178–1185,
and the regional energy estimate at line 1807. -/
theorem re_inner_toEuclideanCLM_sub_ofReal_smul_one {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (a : ℝ) (x : EuclideanSpace ℂ ι) :
    (inner ℂ (toEuclideanCLM (𝕜 := ℂ) (n := ι) (A - (a : ℂ) • 1) x) x).re =
      (inner ℂ (toEuclideanCLM (𝕜 := ℂ) (n := ι) A x) x).re - a * ‖x‖ ^ 2 := by
  simpa only [RCLike.ofReal, Algebra.cast, Complex.coe_algebraMap,
    RCLike.re_to_complex] using
      re_inner_toEuclideanCLM_sub_real_smul_one (𝕜 := ℂ) A a x

end Matrix
