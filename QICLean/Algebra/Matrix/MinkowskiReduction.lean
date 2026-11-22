/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Matrix.MinkowskiCanonicalPair

/-!
# Change of basis and Gram factor recovery for the Minkowski reduction

These are algebraic implications used in the proof of VDDM Theorem 3,
arXiv:quant-ph/0011111v1. The input canonical pair, metric normalization, and square root
are explicit hypotheses. No canonical-pair existence or inertia classification is asserted.
The exact GLR Theorem 5.3 source gate remains open; see
`docs/paper-gaps/qiclean_minkowski_canonical_pair_dependency.tex`.

The Gram factor recovery below assumes an invertible square factor. It does not supply the
Witt extension needed for singular factors, nor properness or time orientation.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Transposing a selfadjoint matrix preserves selfadjointness for an involutory metric.
This is the transpose step in the convention translation preceding VDDM Theorem 3. -/
theorem IsSelfAdjointFor.transpose_of_mul_self {H A : Matrix n n ℝ}
    (h : IsSelfAdjointFor H A) (hH : H * H = 1) : IsSelfAdjointFor H A.transpose := by
  have he := congrArg (fun B => H * B * H) h
  simpa only [IsSelfAdjointFor, transpose_transpose, mul_assoc, hH, mul_one,
    ← mul_assoc H H, hH, one_mul] using he.symm

/-- The Gram product is selfadjoint for any symmetric involutory real metric. -/
theorem isSelfAdjointFor_mul_self_mul_transpose {H : Matrix n n ℝ}
    (hHt : H.transpose = H) (hH : H * H = 1) (A : Matrix n n ℝ) :
    IsSelfAdjointFor H (H * A * H * A.transpose) := by
  simp only [IsSelfAdjointFor, transpose_mul, transpose_transpose, hHt, mul_assoc,
    mul_one, ← mul_assoc H H, hH, one_mul]

/-- The matrix `M R M Rᵀ` in VDDM Theorem 3 is Minkowski-selfadjoint, without any
positivity or rank assumption on `R`. -/
theorem isMinkowskiSelfAdjoint_mul_gram (R : Matrix (Fin 4) (Fin 4) ℝ) :
    IsMinkowskiSelfAdjoint (minkowskiMetric * R * minkowskiMetric * R.transpose) :=
  isSelfAdjointFor_mul_self_mul_transpose minkowskiMetric_transpose minkowskiMetric_mul_self R

/-- Transpose and inverse translation of a *given* simultaneous similarity and congruence.
The conclusion uses `S⁻ᵀ` and the transposed Jordan matrix; it asserts no existence theorem. -/
theorem transpose_canonical_pair {C H J P S : Matrix n n ℝ} (hS : IsUnit S)
    (hC : C.transpose = S⁻¹ * J * S) (hH : H = S.transpose * P * S) :
    C = S.transpose * J.transpose * S⁻¹.transpose ∧
      S⁻¹.transpose * H * S⁻¹ = P := by
  have hSS : S * S⁻¹ = 1 := mul_nonsing_inv S ((isUnit_iff_isUnit_det S).mp hS)
  constructor
  · simpa only [transpose_mul, transpose_transpose, mul_assoc] using
      congrArg Matrix.transpose hC
  · rw [hH]
    have ht : S⁻¹.transpose * S.transpose = 1 := by
      simpa only [transpose_mul, transpose_one] using congrArg Matrix.transpose hSS
    calc
      S⁻¹.transpose * (S.transpose * P * S) * S⁻¹ =
          (S⁻¹.transpose * S.transpose) * P * (S * S⁻¹) := by simp only [mul_assoc]
      _ = P := by rw [ht, hSS, one_mul, mul_one]

/-- Block reversal restores the upper-Jordan orientation while preserving the metric.
All reversal identities are hypotheses, so this does not fix the unverified GLR signature. -/
theorem reverse_transpose_canonical_pair {C H J P S W : Matrix n n ℝ}
    (hS : IsUnit S) (hC : C.transpose = S⁻¹ * J * S)
    (hH : H = S.transpose * P * S) (hW : W * W = 1)
    (hJ : W * J.transpose * W = J) (hP : W * P * W.transpose = P) :
    IsUnit (W * S⁻¹.transpose) ∧
      C = (W * S⁻¹.transpose)⁻¹ * J * (W * S⁻¹.transpose) ∧
      (W * S⁻¹.transpose) * H * (W * S⁻¹.transpose).transpose = P := by
  obtain ⟨hCt, hHt⟩ := transpose_canonical_pair hS hC hH
  have hWu : IsUnit W := IsUnit.of_mul_eq_one W hW
  have hX : IsUnit (W * S⁻¹.transpose) :=
    hWu.mul ((isUnit_transpose _).mpr (isUnit_nonsing_inv_iff.mpr hS))
  refine ⟨hX, ?_, ?_⟩
  · have hXC : (W * S⁻¹.transpose) * C = J * (W * S⁻¹.transpose) := by
      have ht : S⁻¹.transpose * S.transpose = 1 := by
        simpa only [transpose_mul, transpose_one] using
          congrArg Matrix.transpose (mul_nonsing_inv S ((isUnit_iff_isUnit_det S).mp hS))
      calc
        (W * S⁻¹.transpose) * C = W * J.transpose * S⁻¹.transpose := by
          rw [hCt]
          simp only [mul_assoc, ← mul_assoc S⁻¹.transpose S.transpose, ht, one_mul]
        _ = (W * J.transpose * W) * (W * S⁻¹.transpose) := by
          simp only [mul_assoc, ← mul_assoc W W, hW, one_mul]
        _ = J * (W * S⁻¹.transpose) := by rw [hJ]
    have he := congrArg (fun B => (W * S⁻¹.transpose)⁻¹ * B) hXC
    rw [nonsing_inv_mul_cancel_left _ _
      ((isUnit_iff_isUnit_det (W * S⁻¹.transpose)).mp hX)] at he
    simpa only [mul_assoc] using he
  · simpa only [transpose_mul, transpose_transpose, mul_assoc] using
      (calc
        W * (S⁻¹.transpose * H * S⁻¹) * W.transpose = W * P * W.transpose := by rw [hHt]
        _ = P := hP)

/-- An invertible square Gram factor determines a right isometry explicitly.
**Scope restriction (VDDM Theorem 3):** this is the invertible-factor case only; the
singular nondegenerate-row-space extension remains open, as recorded in
`docs/paper-gaps/qiclean_minkowski_canonical_pair_dependency.tex`. -/
theorem exists_right_isometry_of_gram_eq_of_isUnit {A B H : Matrix n n ℝ}
    (hB : IsUnit B) (hGram : A * H * A.transpose = B * H * B.transpose) :
    ∃ L : Matrix n n ℝ, L.transpose * H * L = H ∧ A = B * L.transpose := by
  have hBdet : IsUnit B.det := (isUnit_iff_isUnit_det B).mp hB
  refine ⟨(B⁻¹ * A).transpose, ?_, ?_⟩
  · simp only [transpose_transpose, transpose_mul]
    calc
      B⁻¹ * A * H * (A.transpose * B⁻¹.transpose) =
          B⁻¹ * (A * H * A.transpose) * B⁻¹.transpose := by simp only [mul_assoc]
      _ = B⁻¹ * (B * H * B.transpose) * B⁻¹.transpose := by rw [hGram]
      _ = H := by
        have ht : B.transpose * B⁻¹.transpose = 1 := by
          simpa only [transpose_mul, transpose_one] using
            congrArg Matrix.transpose (nonsing_inv_mul B hBdet)
        simp only [← mul_assoc, nonsing_inv_mul B hBdet, one_mul]
        rw [mul_assoc, ht, mul_one]
  · simp only [transpose_transpose, ← mul_assoc,
      mul_nonsing_inv B hBdet, one_mul]

/-- For an involutory metric the two orientations of the isometry equation agree.
In particular this converts the recovered factor to the row convention of VDDM. -/
theorem transpose_isometry_iff {H L : Matrix n n ℝ} (hH : H * H = 1) :
    L.transpose * H * L = H ↔ L * H * L.transpose = H := by
  have forward : ∀ K : Matrix n n ℝ, K.transpose * H * K = H →
      K * H * K.transpose = H := by
    intro K hK
    have hi : (H * K.transpose * H) * K = 1 := by
      simpa only [mul_assoc, hH] using congrArg (H * ·) hK
    have hr := mul_eq_one_comm.mp hi
    have he := congrArg (· * H) hr
    simpa only [mul_assoc, hH, mul_one, one_mul] using he
  constructor
  · exact forward L
  · intro h
    simpa only [transpose_transpose] using forward L.transpose (by simpa using h)

/-- Normalize a given canonical metric and transport the similarity equation.
Here `O` is orthogonal in the Euclidean sense; the resulting `Y = O X` is an
isometry for `H`. This is an algebraic implication, not metric-normalization existence. -/
theorem normalize_canonical_pair {C H J N X O : Matrix n n ℝ}
    (hX : IsUnit X) (hC : C = X⁻¹ * J * X) (hN : X * H * X.transpose = N)
    (hO : O.transpose * O = 1) (hON : O * N * O.transpose = H) :
    (O * X) * H * (O * X).transpose = H ∧
      (O * X) * C = (O * J * O.transpose) * (O * X) := by
  constructor
  · simpa only [transpose_mul, mul_assoc] using
      (calc
        O * (X * H * X.transpose) * O.transpose = O * N * O.transpose := by rw [hN]
        _ = H := hON)
  · rw [hC]
    calc
      O * X * (X⁻¹ * J * X) = O * J * X := by
        simp only [mul_assoc, mul_nonsing_inv_cancel_left X _
          ((isUnit_iff_isUnit_det X).mp hX)]
      _ = (O * J * O.transpose) * (O * X) := by
        simp only [mul_assoc, ← mul_assoc O.transpose O, hO, one_mul]

/-- A normalized similarity and a chosen indefinite square root give the row Gram identity.
The square root is supplied, not constructed. This is the algebra in the proof of VDDM
Theorem 3 before the recovery of the right Lorentz factor. -/
theorem gram_eq_of_normalized_similarity {H R D Y sigma : Matrix n n ℝ}
    (hH : H * H = 1) (hY : IsUnit Y) (hIso : Y * H * Y.transpose = H)
    (hSim : Y * (H * R * H * R.transpose) = D * Y)
    (hRoot : H * D = sigma * H * sigma.transpose) :
    R * H * R.transpose = Y.transpose * (sigma * H * sigma.transpose) * Y := by
  have hHu : IsUnit H := IsUnit.of_mul_eq_one H hH
  apply (hY.mul hHu).mul_left_cancel
  calc
    (Y * H) * (R * H * R.transpose) = D * Y := by
      simpa only [mul_assoc] using hSim
    _ = (Y * H) * (Y.transpose * (sigma * H * sigma.transpose) * Y) := by
      rw [← hRoot]
      calc
        D * Y = H * (H * D) * Y := by rw [← mul_assoc H H, hH, one_mul]
        _ = (Y * H * Y.transpose) * (H * D) * Y := by rw [hIso]
        _ = _ := by simp only [mul_assoc]

/-- Conditional decomposition from a given canonical pair, metric normalization and invertible
square root. Both factors preserve the involutory metric. No sign, time orientation, positivity,
block classification or existence of the input data is asserted.

**Scope restriction (VDDM Theorem 3):** the invertible-square-root hypothesis excludes singular
normal forms. See `docs/paper-gaps/qiclean_minkowski_canonical_pair_dependency.tex`. -/
theorem exists_decomposition_of_canonical_pair_of_isUnit
    {H R J N X O sigma : Matrix n n ℝ}
    (hH : H * H = 1) (hX : IsUnit X)
    (hC : H * R * H * R.transpose = X⁻¹ * J * X)
    (hN : X * H * X.transpose = N) (hO : O.transpose * O = 1)
    (hON : O * N * O.transpose = H)
    (hRoot : H * (O * J * O.transpose) = sigma * H * sigma.transpose)
    (hsigma : IsUnit sigma) :
    ∃ L₁ L₂ : Matrix n n ℝ,
      L₁ * H * L₁.transpose = H ∧ L₂ * H * L₂.transpose = H ∧
      R = L₁ * sigma * L₂.transpose := by
  obtain ⟨hIso, hSim⟩ := normalize_canonical_pair hX hC hN hO hON
  have hOu : IsUnit O := IsUnit.of_mul_eq_one_right O.transpose hO
  have hY := hOu.mul hX
  have hGram := gram_eq_of_normalized_similarity hH hY hIso hSim hRoot
  have hFactor : IsUnit ((O * X).transpose * sigma) :=
    ((isUnit_transpose _).mpr hY).mul hsigma
  obtain ⟨L₂, hL₂, hR⟩ := exists_right_isometry_of_gram_eq_of_isUnit hFactor
    (by simpa only [transpose_mul, transpose_transpose, mul_assoc] using hGram)
  refine ⟨(O * X).transpose, L₂, ?_, (transpose_isometry_iff hH).mp hL₂, hR⟩
  exact (transpose_isometry_iff hH).mpr hIso

end Matrix
