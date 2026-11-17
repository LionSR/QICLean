/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LiebConvexity

/-!
# Joint operator convexity and concavity of tensor powers

Wolf Corollary 5.5(1,3), following Theorem 5.14, follows from the trace
Ando--Lieb inequalities by testing against every vector. The vectorization
identity is Wolf Equation (5.48). The concave region allows positive semidefinite
inputs; in the convex region the second input is positive definite because its
exponent can be negative. The domain convention is recorded in
`docs/paper-gaps/wolf_ch5_lieb_convexity_domain.tex`.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace Matrix

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Wolf Equation (5.48), for arbitrary matrices before applying real powers.
The transpose on the second factor is essential for complex matrices. -/
theorem vec_transpose_kronecker_quadratic (A B K : Mat) :
    star (vec Kᵀ) ⬝ᵥ ((A ⊗ₖ B) *ᵥ vec Kᵀ) = (Kᴴ * A * K * Bᵀ).trace := by
  rw [kronecker_mulVec_vec B Kᵀ A, star_vec_dotProduct_vec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, transpose_conjTranspose K,
    ← trace_transpose (Kᴴ * A * K * Bᵀ)]
  simp only [transpose_mul, transpose_transpose, conjTranspose_transpose, Matrix.mul_assoc]
  rw [trace_mul_comm (K.map star)]
  simp only [Matrix.mul_assoc]

private theorem le_of_re_vec_transpose_quadratic_le
    {M N : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (h : ∀ K : Mat, (star (vec Kᵀ) ⬝ᵥ (M *ᵥ vec Kᵀ)).re ≤
      (star (vec Kᵀ) ⬝ᵥ (N *ᵥ vec Kᵀ)).re) : M ≤ N := by
  apply le_iff.mpr
  refine PosSemidef.of_dotProduct_mulVec_nonneg (hN.sub hM) fun v => ?_
  refine Complex.le_def.mpr ⟨?_, ?_⟩
  · have hv := h (fun i j => v (i, j))
    change (star v ⬝ᵥ (M *ᵥ v)).re ≤ (star v ⬝ᵥ (N *ᵥ v)).re at hv
    simpa only [sub_mulVec, dotProduct_sub,
      Complex.sub_re, Complex.zero_re, sub_nonneg] using hv
  · exact ((hN.sub hM).im_star_dotProduct_mulVec_self v).symm

private theorem tensor_rpow_isHermitian (A B : Mat) (x y : ℝ) :
    ((A ^ x) ⊗ₖ (B ^ y)).IsHermitian :=
  ((nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := A) (y := x))).kronecker
    (nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := B) (y := y)))).isHermitian

/-- Wolf Corollary 5.5(1): joint operator concavity of two tensor powers
on positive semidefinite pairs for `x, y ≥ 0` and `x + y ≤ 1`. -/
theorem rpow_kronecker_rpow_concave {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ 1) {A₁ A₂ B₁ B₂ : Mat}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • ((A₁ ^ x) ⊗ₖ (B₁ ^ y)) + (1 - t) • ((A₂ ^ x) ⊗ₖ (B₂ ^ y)) ≤
      ((t • A₁ + (1 - t) • A₂) ^ x) ⊗ₖ ((t • B₁ + (1 - t) • B₂) ^ y) := by
  apply le_of_re_vec_transpose_quadratic_le
    (((tensor_rpow_isHermitian A₁ B₁ x y).smul (IsSelfAdjoint.all t)).add
      ((tensor_rpow_isHermitian A₂ B₂ x y).smul (IsSelfAdjoint.all (1 - t))))
    (tensor_rpow_isHermitian _ _ x y)
  intro K
  have h := lieb_concavity_subboundary hx hy hxy hA₁ hA₂ hB₁.transpose hB₂.transpose
    (K := K) ht
  have hB := (hB₁.smul ht.1).add (hB₂.smul (sub_nonneg.mpr ht.2))
  simpa only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul, vec_transpose_kronecker_quadratic,
    ← transpose_smul, ← transpose_add, hB₁.rpow_transpose, hB₂.rpow_transpose,
    hB.rpow_transpose] using h

/-- Wolf Corollary 5.5(3), in the equivalent full convex exponent region.
The first input may be singular; the second must be positive definite.

**Local fix (inverse domain):** See
`docs/paper-gaps/wolf_ch5_lieb_convexity_domain.tex`. -/
theorem rpow_kronecker_rpow_convex {x y : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2)
    (hy : y ∈ Set.Icc (1 - x) 0) {A₁ A₂ B₁ B₂ : Mat}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((t • A₁ + (1 - t) • A₂) ^ x) ⊗ₖ ((t • B₁ + (1 - t) • B₂) ^ y) ≤
      t • ((A₁ ^ x) ⊗ₖ (B₁ ^ y)) + (1 - t) • ((A₂ ^ x) ⊗ₖ (B₂ ^ y)) := by
  apply le_of_re_vec_transpose_quadratic_le (tensor_rpow_isHermitian _ _ x y)
    (((tensor_rpow_isHermitian A₁ B₁ x y).smul (IsSelfAdjoint.all t)).add
      ((tensor_rpow_isHermitian A₂ B₂ x y).smul (IsSelfAdjoint.all (1 - t))))
  intro K
  have h := lieb_convexity_posSemidef_posDef hx hy hA₁ hA₂ hB₁.transpose hB₂.transpose
    (K := K) ht
  have hB := (hB₁.posSemidef.smul ht.1).add (hB₂.posSemidef.smul (sub_nonneg.mpr ht.2))
  simpa only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul, vec_transpose_kronecker_quadratic,
    ← transpose_smul, ← transpose_add, hB₁.posSemidef.rpow_transpose,
    hB₂.posSemidef.rpow_transpose, hB.rpow_transpose] using h

end Matrix
