/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Weighted differences of pure-state densities

For unit vectors ψ and φ and a nonnegative real coefficient t, the trace of
`| |ψ⟩⟨ψ| - t |φ⟩⟨φ| |` is the square root of
`(1 - t)² + 4t(1 - |⟨ψ, φ⟩|²)`. The two rank-one projections satisfy a cubic
identity. A positive quadratic polynomial in their difference is a scalar
multiple of its absolute value. The case of a zero discriminant is included.

This calculation underlies the optimized pure-state trace-norm error in
Schuch, Wolf, Verstraete and Cirac, *Entropy Scaling and Simulability by
Matrix Product States*, arXiv:0705.0292v2, lines 139 and 160–173.
-/

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace

namespace Matrix

variable {n : Type*} [Fintype n]

private theorem weighted_projection_polynomial_nonneg (P Q : Matrix n n ℂ)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPh : P.IsHermitian) (hQh : Q.IsHermitian) (hQpos : 0 ≤ Q)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (2 : ℝ) • ((P - t • Q) * (P - t • Q)) - (1 - t) • (P - t • Q) := by
  have hid :
      (1 + t) • ((2 : ℝ) • ((P - t • Q) * (P - t • Q)) -
        (1 - t) • (P - t • Q)) =
        ((1 + t) • P - (2 * t) • Q) * ((1 + t) • P - (2 * t) • Q) +
          (t * (1 - t) ^ 2) • Q := by
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP, hQ]
    module
  refine nonneg_of_smul_nonneg_of_pos_left (a := 1 + t) ?_ (by positivity)
  rw [hid]
  refine add_nonneg ?_ (smul_nonneg (mul_nonneg ht (sq_nonneg _)) hQpos)
  have hR : ((1 + t) • P - (2 * t) • Q).IsHermitian :=
    (hPh.smul (by rfl)).sub (hQh.smul (by rfl))
  simpa only [hR.eq] using
    (posSemidef_conjTranspose_mul_self ((1 + t) • P - (2 * t) • Q)).nonneg

private theorem weighted_projection_cubic (P Q : Matrix n n ℂ)
    (hP : P * P = P) (hQ : Q * Q = Q) (f t : ℝ)
    (hPQP : P * Q * P = f • P) (hQPQ : Q * P * Q = f • Q) :
    (P - t • Q) * (P - t • Q) * (P - t • Q) =
      (1 - t) • ((P - t • Q) * (P - t • Q)) +
        (t * (1 - f)) • (P - t • Q) := by
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hP, hQ, hPQP, hQPQ, Matrix.mul_assoc P Q Q, Matrix.mul_assoc Q P P]
  module

private theorem weighted_polynomial_square (X : Matrix n n ℂ) (b c : ℝ)
    (h3 : X * X * X = b • (X * X) + c • X) :
    ((2 : ℝ) • (X * X) - b • X) * ((2 : ℝ) • (X * X) - b • X) =
      (b ^ 2 + 4 * c) • (X * X) := by
  have h4 : (X * X) * (X * X) = b • (X * X * X) + c • (X * X) := by
    simpa only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc] using
      congrArg (fun Y : Matrix n n ℂ ↦ Y * X) h3
  have hexp :
      ((2 : ℝ) • (X * X) - b • X) * ((2 : ℝ) • (X * X) - b • X) =
        (4 : ℝ) • ((X * X) * (X * X)) - (4 * b) • (X * X * X) +
          b ^ 2 • (X * X) := by
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.mul_assoc]
    module
  rw [hexp, h4]
  module

open Classical in
private theorem abs_eq_inv_sqrt_smul_weighted_polynomial
    (X : Matrix n n ℂ) (hX : X.IsHermitian) (b c : ℝ)
    (hd : 0 < b ^ 2 + 4 * c)
    (h3 : X * X * X = b • (X * X) + c • X)
    (hN : 0 ≤ (2 : ℝ) • (X * X) - b • X) :
    CFC.abs X = (Real.sqrt (b ^ 2 + 4 * c))⁻¹ •
      ((2 : ℝ) • (X * X) - b • X) := by
  have habs : CFC.abs X = CFC.sqrt (X * X) := by
    rw [CFC.abs, Matrix.star_eq_conjTranspose, hX.eq]
  refine habs.trans (CFC.sqrt_unique ?_
    (smul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hN))
  have hr :
      (Real.sqrt (b ^ 2 + 4 * c))⁻¹ * (Real.sqrt (b ^ 2 + 4 * c))⁻¹ *
        (b ^ 2 + 4 * c) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hd.le, inv_mul_cancel₀ hd.ne']
  rw [smul_mul_smul_comm, weighted_polynomial_square X b c h3, smul_smul, hr, one_smul]

open Classical in
private theorem re_trace_abs_sub_smul_of_pos_discriminant
    (P Q : Matrix n n ℂ) (hP : P * P = P) (hQ : Q * Q = Q)
    (hPh : P.IsHermitian) (hQh : Q.IsHermitian) (hQpos : 0 ≤ Q)
    (hPtr : P.trace.re = 1) (hQtr : Q.trace.re = 1) (f t : ℝ) (ht : 0 ≤ t)
    (hPQP : P * Q * P = f • P) (hQPQ : Q * P * Q = f • Q)
    (hd : 0 < (1 - t) ^ 2 + 4 * (t * (1 - f))) :
    (CFC.abs (P - t • Q)).trace.re =
      Real.sqrt ((1 - t) ^ 2 + 4 * (t * (1 - f))) := by
  have htrPQ : (P * Q).trace.re = f := by
    have hh := congrArg (fun M : Matrix n n ℂ ↦ M.trace.re) hPQP
    rw [Matrix.trace_mul_comm (P * Q) P, ← Matrix.mul_assoc, hP] at hh
    simpa only [trace_smul, Complex.smul_re, smul_eq_mul, hPtr, mul_one] using hh
  have htrQP : (Q * P).trace.re = f := by
    rw [Matrix.trace_mul_comm Q P, htrPQ]
  have htr2 : ((P - t • Q) * (P - t • Q)).trace.re = 1 + t ^ 2 - 2 * t * f := by
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hP, hQ, trace_sub, trace_smul, Complex.sub_re, Complex.smul_re,
      smul_eq_mul, hPtr, hQtr, htrPQ, htrQP]
    ring
  have habs := abs_eq_inv_sqrt_smul_weighted_polynomial
    (P - t • Q) (hPh.sub (hQh.smul (by rfl))) (1 - t) (t * (1 - f)) hd
    (weighted_projection_cubic P Q hP hQ f t hPQP hQPQ)
    (weighted_projection_polynomial_nonneg P Q hP hQ hPh hQh hQpos t ht)
  simp only [habs, trace_smul, trace_sub, Complex.smul_re, Complex.sub_re,
    smul_eq_mul, htr2, hPtr, hQtr]
  rw [show 2 * (1 + t ^ 2 - 2 * t * f) - (1 - t) * (1 - t * 1) =
    (1 - t) ^ 2 + 4 * (t * (1 - f)) by ring]
  exact (congrArg (fun x : ℝ ↦ (Real.sqrt _)⁻¹ * x)
    (Real.mul_self_sqrt hd.le).symm).trans
      (inv_mul_cancel_left₀ (Real.sqrt_pos.mpr hd).ne' _)

open Classical in
private theorem re_trace_abs_sub_smul
    (P Q : Matrix n n ℂ) (hP : P * P = P) (hQ : Q * Q = Q)
    (hPh : P.IsHermitian) (hQh : Q.IsHermitian) (hQpos : 0 ≤ Q)
    (hPtr : P.trace.re = 1) (hQtr : Q.trace.re = 1) (f t : ℝ)
    (hf : f ≤ 1) (ht : 0 ≤ t)
    (hPQP : P * Q * P = f • P) (hQPQ : Q * P * Q = f • Q) :
    (CFC.abs (P - t • Q)).trace.re =
      Real.sqrt ((1 - t) ^ 2 + 4 * (t * (1 - f))) := by
  have hd0 : 0 ≤ (1 - t) ^ 2 + 4 * (t * (1 - f)) :=
    add_nonneg (sq_nonneg _) (mul_nonneg (by positivity)
      (mul_nonneg ht (sub_nonneg.mpr hf)))
  rcases hd0.eq_or_lt with hdzero | hdpos
  · have hs : (1 - t) ^ 2 = 0 ∧ 4 * (t * (1 - f)) = 0 :=
      (add_eq_zero_iff_of_nonneg (sq_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg ht (sub_nonneg.mpr hf)))).mp hdzero.symm
    have ht1 : t = 1 := (sub_eq_zero.mp (sq_eq_zero_iff.mp hs.1)).symm
    have hf0 : 1 - f = 0 := (mul_eq_zero.mp
      (show (4 : ℝ) * (1 - f) = 0 by simpa only [ht1, one_mul] using hs.2)).resolve_left
        (by positivity)
    have hf1 : f = 1 := (sub_eq_zero.mp hf0).symm
    subst t f
    have h3zero : (P - Q) * (P - Q) * (P - Q) = 0 := by
      simpa only [one_smul, sub_self, one_mul, zero_smul, add_zero] using
        weighted_projection_cubic P Q hP hQ 1 1 hPQP hQPQ
    have hX : IsSelfAdjoint (P - Q) := (hPh.sub hQh).isSelfAdjoint
    have h4zero : star ((P - Q) * (P - Q)) * ((P - Q) * (P - Q)) = 0 := by
      simpa only [star_mul, hX.star_eq, Matrix.mul_assoc, zero_mul] using
        congrArg (fun Y : Matrix n n ℂ ↦ Y * (P - Q)) h3zero
    have h2zero : (P - Q) * (P - Q) = 0 :=
      (conjTranspose_mul_self_eq_zero (A := (P - Q) * (P - Q))).mp
        (by simpa only [← star_eq_conjTranspose] using h4zero)
    have hXzero : P - Q = 0 :=
      (conjTranspose_mul_self_eq_zero (A := P - Q)).mp
        (by simpa only [← star_eq_conjTranspose, hX.star_eq] using h2zero)
    simp [hXzero]
  · exact re_trace_abs_sub_smul_of_pos_discriminant P Q hP hQ hPh hQh hQpos
      hPtr hQtr f t ht hPQP hQPQ hdpos

open Classical in
/-- The full trace norm of a weighted difference of unit pure-state densities,
expressed as the trace of the absolute value. This is the calculation underlying
Schuch--Wolf--Verstraete--Cirac, arXiv:0705.0292v2, lines 139 and 160–173. -/
theorem re_trace_abs_vecMulVec_sub_smul_eq
    (ψ φ : EuclideanSpace ℂ n) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (CFC.abs (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)) -
      t • vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).trace.re =
        Real.sqrt ((1 - t) ^ 2 + 4 * (t * (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2))) := by
  set u := WithLp.ofLp ψ
  set v := WithLp.ofLp φ
  set P := vecMulVec u (star u)
  set Q := vecMulVec v (star v)
  set a : ℂ := star u ⬝ᵥ v with ha
  have hunit : ∀ x : EuclideanSpace ℂ n, ‖x‖ = 1 →
      star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x = 1 := by
    intro x hx
    have h : ⟪x, x⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; simp
    rwa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  have huu := hunit ψ hψ
  have hvv := hunit φ hφ
  have hainner : ⟪ψ, φ⟫_ℂ = a := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hvu : star v ⬝ᵥ u = star a := by
    rw [ha, ← Matrix.star_dotProduct_star, star_star, dotProduct_comm]
  have hvmv : ∀ (x y z w : n → ℂ),
      vecMulVec x y * vecMulVec z w = (y ⬝ᵥ z) • vecMulVec x w := by
    intro x y z w
    rw [vecMulVec_mul_vecMulVec]
    ext i j
    simp [vecMulVec_apply, mul_left_comm]
  have hP : P * P = P := by rw [hvmv, huu, one_smul]
  have hQ : Q * Q = Q := by rw [hvmv, hvv, one_smul]
  set s : ℂ := a * star a with hs
  have hPQP : P * Q * P = s • P := by
    rw [hvmv, smul_mul, hvmv, hvu, smul_smul, ← ha]
  have hQPQ : Q * P * Q = s • Q := by
    rw [hvmv, smul_mul, hvmv, ← ha, hvu, smul_smul, mul_comm]
  have hsre : s = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [hs, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hPpsd : P.PosSemidef := posSemidef_vecMulVec_self_star u
  have hQpsd : Q.PosSemidef := posSemidef_vecMulVec_self_star v
  have hPtr : P.trace.re = 1 := by
    simpa only [P, trace_vecMulVec, dotProduct_comm u (star u), Complex.one_re] using
      congrArg Complex.re huu
  have hQtr : Q.trace.re = 1 := by
    simpa only [Q, trace_vecMulVec, dotProduct_comm v (star v), Complex.one_re] using
      congrArg Complex.re hvv
  have hle : ‖a‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (by
    simpa only [hψ, hφ, hainner, one_mul] using norm_inner_le_norm (𝕜 := ℂ) ψ φ)
  have hPQP' : P * Q * P = (‖a‖ ^ 2 : ℝ) • P := by
    simpa only [hsre, Complex.coe_smul] using hPQP
  have hQPQ' : Q * P * Q = (‖a‖ ^ 2 : ℝ) • Q := by
    simpa only [hsre, Complex.coe_smul] using hQPQ
  simpa only [hainner] using
    re_trace_abs_sub_smul P Q hP hQ hPpsd.isHermitian hQpsd.isHermitian hQpsd.nonneg
      hPtr hQtr (‖a‖ ^ 2) t hle ht hPQP' hQPQ'

end Matrix
