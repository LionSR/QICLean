/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceDistance
import QICLean.Analysis.WeightedPureStateTraceNorm

/-!
# Trace distance of two pure states

For unit vectors `ψ, φ`, the trace distance of the pure states `|ψ⟩⟨ψ|` and `|φ⟩⟨φ|` is
`√(1 - |⟨ψ, φ⟩|²)`. Writing `P, Q` for the two projections and `s = |⟨ψ, φ⟩|²`, the
identities `P Q P = s P` and `Q P Q = s Q` give `(P - Q)³ = (1 - s) (P - Q)`, so
`|P - Q| = (P - Q)² / √(1 - s)`, whose trace is `2 √(1 - s)`.

## Main results

* `Matrix.abs_eq_inv_sqrt_smul_mul_self`: `|X| = c^{-1/2} X²` for Hermitian `X` with
  `X³ = c X`, `c > 0`.
* `Matrix.traceDistance_vecMulVec_eq`: the pure-state trace-distance formula.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 4.5 (`prop:truncation`), section file `03-quasilocal.tex`,
  lines 500–502: "The trace distance of two pure states equals the square root of one
  minus their squared overlap." The proof here is written from the paper.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Classical

variable {m : Type*} [Fintype m]

open scoped Classical in
/-- If `X` is Hermitian and `X³ = c X` with `c > 0`, then `|X| = c^{-1/2} X²`. -/
theorem abs_eq_inv_sqrt_smul_mul_self {X : Matrix m m ℂ} (hX : X.IsHermitian) {c : ℝ}
    (hc : 0 < c) (h3 : X * X * X = (c : ℂ) • X) :
    CFC.abs X = (Real.sqrt c)⁻¹ • (X * X) := by
  have hXX : 0 ≤ X * X := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa [hX.eq] using Matrix.posSemidef_conjTranspose_mul_self X
  have habs : CFC.abs X = CFC.sqrt (X * X) := by
    rw [CFC.abs, Matrix.star_eq_conjTranspose, hX.eq]
  rw [habs]
  refine CFC.sqrt_unique ?_ (smul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg c)) hXX)
  have h4 : X * X * (X * X) = (c : ℂ) • (X * X) := by
    rw [← Matrix.mul_assoc, h3, Matrix.smul_mul]
  have hr : (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ * c = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  rw [smul_mul_smul_comm, h4, ← Complex.coe_smul, smul_smul, ← Complex.ofReal_mul, hr,
    Complex.ofReal_one, one_smul]

end Classical

omit [DecidableEq n] in
/-- `(P - Q)³ = (1 - s) (P - Q)` for idempotents with `P Q P = s P`, `Q P Q = s Q`. -/
theorem sub_mul_sub_mul_sub_of_idempotent {P Q : Matrix n n ℂ} {s : ℂ} (hP : P * P = P)
    (hQ : Q * Q = Q) (hPQP : P * Q * P = s • P) (hQPQ : Q * P * Q = s • Q) :
    (P - Q) * (P - Q) * (P - Q) = (1 - s) • (P - Q) := by
  have hexp : (P - Q) * (P - Q) * (P - Q) =
      P * P * P - P * P * Q - P * Q * P + P * Q * Q - Q * P * P + Q * P * Q + Q * Q * P -
        Q * Q * Q := by noncomm_ring
  rw [hexp, hPQP, hQPQ, hP, hQ, Matrix.mul_assoc P Q Q, Matrix.mul_assoc Q P P, hP, hQ]
  simp only [sub_smul, one_smul, smul_sub]
  abel

/-- **Trace distance of pure states** (`03-quasilocal.tex`, lines 500–502): for unit vectors
`ψ, φ`, `δ(|ψ⟩⟨ψ|, |φ⟩⟨φ|) = √(1 - |⟨ψ, φ⟩|²)`. -/
theorem traceDistance_vecMulVec_eq {ψ φ : EuclideanSpace ℂ n} (hψ : ‖ψ‖ = 1)
    (hφ : ‖φ‖ = 1) :
    traceDistance (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)))
        (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) =
      Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2) := by
  have h := re_trace_abs_vecMulVec_sub_smul_eq ψ φ hψ hφ 1 zero_le_one
  simp only [one_smul, sub_self, zero_pow two_ne_zero, zero_add, one_mul] at h
  rw [traceDistance, h, Real.sqrt_mul (by positivity : 0 ≤ (4 : ℝ)),
    show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by positivity)]
  exact mul_div_cancel_left₀ _ (by positivity : (2 : ℝ) ≠ 0)

end Matrix
