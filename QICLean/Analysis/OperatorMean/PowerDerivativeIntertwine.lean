/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Bilinear
import QICLean.Algebra.MatrixSandwichIntertwine
import QICLean.Analysis.OperatorMean.MeanDerivative

/-!
# Intertwining the derivative of a matrix power

For positive definite matrices satisfying `A * J = J * B`, the derivative
of a real power transports the direction `J * H * Jᴴ` to the same sandwich
of the derivative at `B`. The proof intertwines the shifted resolvents
and then integrates their sandwiches. No isometry premise is required.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, Lemma 7.2, display `transport:power-derivative`,
  `06-transport.tex`, lines 158–164, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Set MeasureTheory

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Rectangular intertwining of the power derivative. Auxiliary to OpenAI's
area-law manuscript, Lemma 7.2, `transport:power-derivative`,
`06-transport.tex`, lines 158–164, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The direction `H` may be arbitrary; the intertwiner need not be an isometry. -/
theorem rpowDeriv_intertwine
    {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosDef) (hB : B.PosDef)
    (J : Matrix n m ℂ) (hAJ : A * J = J * B)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (H : Matrix m m ℂ) :
    rpowDeriv p A (J * H * Jᴴ) = J * rpowDeriv p B H * Jᴴ := by
  unfold rpowDeriv
  split_ifs with h0 h1
  · simp only [_root_.zero_apply, Matrix.mul_zero, Matrix.zero_mul]
  · rfl
  · have hp' : p ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hp.1 (Ne.symm h0), lt_of_le_of_ne hp.2 h1⟩
    rw [rpowFDeriv_apply hA hp', rpowFDeriv_apply hB hp']
    have hshift (t : ℝ) :
        (t • (1 : Matrix n n ℂ) + A) * J = J * (t • (1 : Matrix m m ℂ) + B) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, hAJ]
    have hres (t : ℝ) (ht : 0 < t) :
        Ring.inverse (t • (1 : Matrix n n ℂ) + A) * J =
          J * Ring.inverse (t • (1 : Matrix m m ℂ) + B) := by
      have hAt : (t • (1 : Matrix n n ℂ) + A).PosDef := (PosDef.one.smul ht).add hA
      have hBt : (t • (1 : Matrix m m ℂ) + B).PosDef := (PosDef.one.smul ht).add hB
      let := hAt.isUnit.invertible
      let := hBt.isUnit.invertible
      rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse]
      apply (Matrix.inv_mul_eq_iff_eq_mul_of_invertible _ _ _).2
      rw [← Matrix.mul_assoc, hshift, Matrix.mul_inv_cancel_right_of_invertible]
    let L : Matrix m m ℂ →L[ℂ] Matrix n n ℂ :=
      LinearMap.toContinuousLinearMap
        ((mulRightLinearMap n ℂ Jᴴ).comp (mulLeftLinearMap m ℂ J))
    have hint : IntegrableOn (fun t ↦ rpowFDerivIntegrand p B t H) (Ioi 0) :=
      (integrableOn_rpowFDerivIntegrand hB hp').apply_continuousLinearMap H
    have hcomm (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
        t ^ p • (Ring.inverse (t • (1 : Matrix n n ℂ) + A) * (J * H * Jᴴ) *
          Ring.inverse (t • (1 : Matrix n n ℂ) + A)) =
        L (rpowFDerivIntegrand p B t H) := by
      rw [rpowFDerivIntegrand_apply]
      change t ^ p • (Ring.inverse (t • (1 : Matrix n n ℂ) + A) * (J * H * Jᴴ) *
        Ring.inverse (t • (1 : Matrix n n ℂ) + A)) =
        J * (t ^ p • (Ring.inverse (t • (1 : Matrix m m ℂ) + B) * H *
          Ring.inverse (t • (1 : Matrix m m ℂ) + B))) * Jᴴ
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      simpa only [← Matrix.nonsing_inv_eq_ringInverse] using
        (((PosDef.one.smul ht).add hA).isHermitian.inv.sandwich_intertwine
          ((PosDef.one.smul ht).add hB).isHermitian.inv J
          (by simpa only [← Matrix.nonsing_inv_eq_ringInverse] using hres t ht) H)
    rw [setIntegral_congr_fun measurableSet_Ioi hcomm,
      ContinuousLinearMap.integral_comp_comm L hint]
    change rpowConst p • (J * (∫ t in Ioi (0 : ℝ), t ^ p •
      (Ring.inverse (t • (1 : Matrix m m ℂ) + B) * H *
        Ring.inverse (t • (1 : Matrix m m ℂ) + B))) * Jᴴ) = _
    rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Compression of the complex-linear power derivative on an arbitrary
direction. Auxiliary to OpenAI's area-law manuscript, Lemma 7.2,
`06-transport.tex`, lines 158–164, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The intertwiner may be rectangular and need not be an isometry. -/
theorem rpowDeriv_compress
    {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosDef) (hB : B.PosDef)
    (J : Matrix n m ℂ) (hAJ : A * J = J * B)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (X : Matrix n n ℂ) :
    Jᴴ * rpowDeriv p A X * J = rpowDeriv p B (Jᴴ * X * J) := by
  have hstar := hA.isHermitian.conjTranspose_intertwine hB.isHermitian J hAJ
  simpa only [Matrix.conjTranspose_conjTranspose] using
    (rpowDeriv_intertwine hB hA Jᴴ hstar hp X).symm

end Matrix
