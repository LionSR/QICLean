/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.RealPowerIntertwine
import QICLean.Analysis.OperatorMean.WeightedGeometricMean

/-!
# Rectangular intertwining of geometric means

The formula for the weighted geometric mean transports along a common
rectangular intertwiner of two positive definite inputs. The identity holds
at every real exponent and does not require the intertwiner to be an isometry.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, `06-transport.tex`, transport:mean-def, lines 17–22, and
  Lemma 7.2, `transport:cp`, lines 136–172, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

This is an auxiliary identity for the binary geometric mean used in the
manuscript's transport estimate.
-/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Auxiliary to the geometric-mean formula in OpenAI's area-law manuscript,
`06-transport.tex`, lines 17–22, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This formula identity holds at every real exponent. -/
theorem geomMean_intertwine
    {A₁ B₁ : Matrix n n ℂ} {A₂ B₂ : Matrix m m ℂ}
    (hA₁ : A₁.PosDef) (hB₁ : B₁.PosDef)
    (hA₂ : A₂.PosDef) (hB₂ : B₂.PosDef)
    (J : Matrix n m ℂ) (hAJ : A₁ * J = J * A₂) (hBJ : B₁ * J = J * B₂)
    (p : ℝ) :
    geomMean p A₁ B₁ * J = J * geomMean p A₂ B₂ := by
  unfold geomMean
  have hpow (s : ℝ) : A₁ ^ s * J = J * A₂ ^ s :=
    hA₁.posSemidef.rpow_intertwine hA₂.posSemidef J hAJ s
  have hwhite :
      (A₁ ^ (-(1 / 2) : ℝ) * B₁ * A₁ ^ (-(1 / 2) : ℝ)) * J =
        J * (A₂ ^ (-(1 / 2) : ℝ) * B₂ * A₂ ^ (-(1 / 2) : ℝ)) := by
    rw [Matrix.mul_assoc (A₁ ^ (-(1 / 2) : ℝ) * B₁) (A₁ ^ (-(1 / 2) : ℝ)) J,
      hpow, ← Matrix.mul_assoc (A₁ ^ (-(1 / 2) : ℝ) * B₁) J (A₂ ^ (-(1 / 2) : ℝ)),
      Matrix.mul_assoc (A₁ ^ (-(1 / 2) : ℝ)) B₁ J, hBJ,
      ← Matrix.mul_assoc (A₁ ^ (-(1 / 2) : ℝ)) J B₂, hpow,
      Matrix.mul_assoc J (A₂ ^ (-(1 / 2) : ℝ)) B₂,
      Matrix.mul_assoc J (A₂ ^ (-(1 / 2) : ℝ) * B₂) (A₂ ^ (-(1 / 2) : ℝ))]
  have hcPow :
      (A₁ ^ (-(1 / 2) : ℝ) * B₁ * A₁ ^ (-(1 / 2) : ℝ)) ^ p * J =
        J * (A₂ ^ (-(1 / 2) : ℝ) * B₂ * A₂ ^ (-(1 / 2) : ℝ)) ^ p := by
    exact (hA₁.whiten hB₁).posSemidef.rpow_intertwine
      (hA₂.whiten hB₂).posSemidef J hwhite p
  simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_assoc] at hcPow
  rw [hpow (1 / 2 : ℝ),
    ← Matrix.mul_assoc
      ((A₁ ^ (-(1 / 2) : ℝ) * (B₁ * A₁ ^ (-(1 / 2) : ℝ))) ^ p) J
      (A₂ ^ (1 / 2 : ℝ)), hcPow,
    Matrix.mul_assoc J
      ((A₂ ^ (-(1 / 2) : ℝ) * (B₂ * A₂ ^ (-(1 / 2) : ℝ))) ^ p)
      (A₂ ^ (1 / 2 : ℝ)),
    ← Matrix.mul_assoc (A₁ ^ (1 / 2 : ℝ)) J
      (((A₂ ^ (-(1 / 2) : ℝ) * (B₂ * A₂ ^ (-(1 / 2) : ℝ))) ^ p) *
        A₂ ^ (1 / 2 : ℝ)), hpow (1 / 2 : ℝ),
    Matrix.mul_assoc J (A₂ ^ (1 / 2 : ℝ))
      (((A₂ ^ (-(1 / 2) : ℝ) * (B₂ * A₂ ^ (-(1 / 2) : ℝ))) ^ p) *
        A₂ ^ (1 / 2 : ℝ))]

end Matrix
