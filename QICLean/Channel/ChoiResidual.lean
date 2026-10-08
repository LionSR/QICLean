/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.RectangularChoi
import QICLean.Analysis.MatrixTraceInequalities
import QICLean.Channel.ChoiDoeblin

/-!
# Rectangular Choi residual estimates

Subtracting a trace-prepare contribution from a Choi-minorized channel leaves a completely
positive map with a known trace scale. A rectangular residual with trace scale `t` has
Hilbert--Schmidt induced norm at most its input dimension times `t`. The bound follows from
Choi positivity and the existing Frobenius Parseval identity, without padding either space.

## References

* Wolf, *Quantum Channels & Operations*, Proposition 2.1 and Theorem 8.17, Eq. (8.86).
-/

open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace Matrix

variable {a b : ℕ}

/-- Equality-based relabeling of actual input and output dimensions preserves the
Hilbert--Schmidt induced error from a trace-prepare reference. -/
theorem norm_linearMapMatrix_sub_tracePrepareMap_finCast {d a' b' : ℕ}
    (ha : a = a') (hb : b = b')
    (A : Fin d → Matrix (Fin a') (Fin b') ℂ) (σ : Matrix (Fin a') (Fin a') ℂ) :
    ‖linearMapMatrix (rectangularKrausMap
        (fun i => (A i).submatrix (Fin.cast ha) (Fin.cast hb)) -
      tracePrepareMap (α := Fin b) (σ.submatrix (Fin.cast ha) (Fin.cast ha)))‖ =
    ‖linearMapMatrix (rectangularKrausMap A - tracePrepareMap (α := Fin b') σ)‖ := by
  subst a'
  subst b'
  rfl

/-- The input-first unnormalized Choi matrix is the input dimension times the normalized,
output-first Choi matrix with its tensor factors interchanged. -/
theorem rectangularChoi_eq_smul_choiMatrix_swap [NeZero b]
    (T : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ) :
    rectangularChoi T = (b : ℂ) •
      (ChoiRectangular.choiMatrix T).submatrix Prod.swap Prod.swap := by
  ext ⟨i, x⟩ ⟨j, y⟩
  rw [rectangularChoi_apply, Matrix.smul_apply, Matrix.submatrix_apply]
  rw [ChoiRectangular.choiMatrix_apply, MaximallyEntangled.omegaSlice_eq_single,
    MaximallyEntangled.omegaCoeff_eq_inv (Nat.pos_of_ne_zero (NeZero.ne b))]
  change T (Matrix.single i j 1) x y =
    (b : ℂ) • T (Matrix.single i j (1 / (b : ℂ))) x y
  rw [show Matrix.single i j (1 / (b : ℂ)) =
    (1 / (b : ℂ)) • Matrix.single i j 1 by simp, map_smul, Matrix.smul_apply]
  simp only [smul_eq_mul]
  field_simp [NeZero.ne b]

/-- Rectangular complete positivity also makes the unnormalized Choi matrix positive. -/
theorem rectangularChoi_posSemidef [NeZero b]
    {T : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ}
    (hT : IsKrausCP T) : (rectangularChoi T).PosSemidef := by
  rw [rectangularChoi_eq_smul_choiMatrix_swap]
  exact (((ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef T).1 hT).submatrix
    Prod.swap).smul (by positivity)

/-- The trace of the unnormalized Choi matrix records the input dimension and trace scale. -/
theorem trace_rectangularChoi_of_scaledTrace
    (T : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ) (t : ℝ)
    (htr : ∀ X, (T X).trace = (t : ℂ) * X.trace) :
    (rectangularChoi T).trace = (b : ℂ) * t := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, rectangularChoi_apply]
  change (∑ i : Fin b, (T (Matrix.single i i 1)).trace) = _
  simp [htr, mul_comm]

/-- A completely positive rectangular map of nonnegative trace scale `t` has
Hilbert--Schmidt induced operator norm at most `b * t`, where `b` is its input dimension.
The norm is the L2 operator norm of its coefficient matrix in the matrix-unit bases. -/
theorem norm_linearMapMatrix_le_of_isKrausCP_scaledTrace [NeZero b]
    (T : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (hT : IsKrausCP T) (t : ℝ) (ht : 0 ≤ t)
    (htr : ∀ X, (T X).trace = (t : ℂ) * X.trace) :
    ‖linearMapMatrix T‖ ≤ b * t := by
  have hC := rectangularChoi_posSemidef hT
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg b) ht)).mp
  calc ‖linearMapMatrix T‖ ^ 2
      ≤ ((linearMapMatrix T)ᴴ * linearMapMatrix T).trace.re :=
        l2_opNorm_sq_le_trace_conjTranspose_mul_self_re _
    _ = ((rectangularChoi T)ᴴ * rectangularChoi T).trace.re :=
      (rectangularChoi_frobenius_parseval T).symm
    _ = ((rectangularChoi T) ^ 2).trace.re := by rw [hC.isHermitian.eq, pow_two]
    _ ≤ (rectangularChoi T).trace.re ^ 2 := hC.trace_sq_re_le_trace_re_sq
    _ = (b * t) ^ 2 := by rw [trace_rectangularChoi_of_scaledTrace T t htr]; simp

/-- A local Choi minorization leaves a completely positive rectangular residual.
The normalized Choi denominator is the actual input dimension. -/
theorem isKrausCP_sub_smul_tracePrepareMap_of_choi_domination [NeZero b]
    (T : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (τ : Matrix (Fin a) (Fin a) ℂ) (η : ℝ)
    (hchoi : ChoiRectangular.choiMatrix T ≥
      ((η : ℂ) / b) • (τ ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))) :
    IsKrausCP (T - (η : ℂ) • tracePrepareMap (α := Fin b) τ) := by
  apply (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef _).2
  have hC : ChoiRectangular.choiMatrix
        (T - (η : ℂ) • tracePrepareMap (α := Fin b) τ) =
      ChoiRectangular.choiMatrix T -
        ((η : ℂ) / b) • (τ ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) := by
    change ChoiRectangular.choiMatrixLinearMap
      (T - (η : ℂ) • tracePrepareMap (α := Fin b) τ) = _
    rw [map_sub, map_smul]
    change _ - (η : ℂ) • ChoiRectangular.choiMatrix
      (tracePrepareMap (α := Fin b) τ) = _
    rw [choiMatrix_tracePrepareMap, smul_smul]
    congr 2
    ring
  rw [hC]
  exact Matrix.le_iff.mp hchoi

/-- Subtracting a trace-one reset of strength `η` from a trace-preserving map leaves
trace scale `1 - η`, including the endpoint `η = 1`. -/
theorem trace_sub_smul_tracePrepareMap
    (T : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (hT : ∀ X, (T X).trace = X.trace)
    (τ : Matrix (Fin a) (Fin a) ℂ) (hτ : τ.trace = 1) (η : ℝ)
    (X : Matrix (Fin b) (Fin b) ℂ) :
    ((T - (η : ℂ) • tracePrepareMap (α := Fin b) τ) X).trace =
      ((1 - η : ℝ) : ℂ) * X.trace := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul, hT X, tracePrepareMap_trace, hτ, mul_one]
  push_cast
  ring

/-- A positive Choi minorization of a trace-preserving map has strength at most one
when its input space is nonzero and its minorizer has trace one. -/
theorem le_one_of_choi_domination [NeZero b]
    (T : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (hT : ∀ X, (T X).trace = X.trace)
    (τ : Matrix (Fin a) (Fin a) ℂ) (hτ : τ.trace = 1) (η : ℝ)
    (hchoi : ChoiRectangular.choiMatrix T ≥
      ((η : ℂ) / b) • (τ ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))) : η ≤ 1 := by
  have hR := isKrausCP_sub_smul_tracePrepareMap_of_choi_domination T τ η hchoi
  have hp := (hR.map_posSemidef ((faithfulDensity_posDef (Fin b)).posSemidef)).trace_nonneg
  rw [trace_sub_smul_tracePrepareMap T hT τ hτ η,
    faithfulDensity_trace, mul_one] at hp
  have h := (Complex.nonneg_iff.mp hp).1
  simpa using (sub_nonneg.mp h)

/-- A completely positive scaled-trace residual agreeing with `F` on traceless inputs
bounds the distance of `F` from the density reset obtained by transporting any input density.
The reference can be singular. No stationary reference is assumed. -/
theorem norm_linearMapMatrix_sub_tracePrepareMap_le_of_residual [NeZero b]
    (F Q : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (hQ : IsKrausCP Q) (t : ℝ) (ht : 0 ≤ t)
    (htr : ∀ X, (Q X).trace = (t : ℂ) * X.trace)
    (hzero : ∀ X, X.trace = 0 → Q X = F X)
    (ρ : Matrix (Fin b) (Fin b) ℂ) (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1) :
    ‖linearMapMatrix (F - tracePrepareMap (α := Fin b) (F ρ))‖ ≤ 2 * b * t := by
  have hmaps : F - tracePrepareMap (α := Fin b) (F ρ) =
      Q - tracePrepareMap (α := Fin b) (Q ρ) := by
    ext X : 1
    have h := hzero (X - X.trace • ρ) (by simp [hρtr])
    simpa only [map_sub, map_smul, LinearMap.sub_apply, tracePrepareMap_apply] using h.symm
  have hP : IsKrausCP (tracePrepareMap (α := Fin b) (Q ρ)) :=
    tracePrepareMap_isKrausCP _ (hQ.map_posSemidef hρ)
  have hPtr (X : Matrix (Fin b) (Fin b) ℂ) :
      (tracePrepareMap (α := Fin b) (Q ρ) X).trace = (t : ℂ) * X.trace := by
    simp [htr, hρtr, mul_comm]
  rw [hmaps, linearMapMatrix_sub]
  have hQnorm := norm_linearMapMatrix_le_of_isKrausCP_scaledTrace Q hQ t ht htr
  have hPnorm := norm_linearMapMatrix_le_of_isKrausCP_scaledTrace _ hP t ht hPtr
  exact (norm_sub_le _ _).trans (by linarith)

end Matrix
