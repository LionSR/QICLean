/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixSandwichIntertwine
import QICLean.Analysis.OperatorMean.PowerDerivativeIntertwine
import QICLean.Analysis.OperatorMean.RealPowerIntertwine

/-!
# Rectangular intertwining of a geometric-mean derivative

These are rectangular intertwining and compression identities for the
derivative formula in OpenAI's two-dimensional area-law manuscript, Lemma 7.2,
`06-transport.tex`, lines 157–172, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The common intertwiner may be rectangular. The identity concerns the complex
linear extension of the derivative, so its direction need not be Hermitian.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Set

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The derivative in the second argument transports along a common
intertwiner. Auxiliary to OpenAI's area-law manuscript, Lemma 7.2,
`06-transport.tex`, lines 157–172, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The direction is arbitrary and no isometry premise is imposed. -/
theorem geomMeanDerivRight_intertwine
    {A₁ B₁ : Matrix n n ℂ} {A₂ B₂ : Matrix m m ℂ}
    (hA₁ : A₁.PosDef) (hB₁ : B₁.PosDef)
    (hA₂ : A₂.PosDef) (hB₂ : B₂.PosDef)
    (J : Matrix n m ℂ) (hAJ : A₁ * J = J * A₂) (hBJ : B₁ * J = J * B₂)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (H : Matrix m m ℂ) :
    geomMeanDerivRight p A₁ B₁ (J * H * Jᴴ) =
      J * geomMeanDerivRight p A₂ B₂ H * Jᴴ := by
  unfold geomMeanDerivRight
  have hpow (s : ℝ) : A₁ ^ s * J = J * A₂ ^ s :=
    hA₁.posSemidef.rpow_intertwine hA₂.posSemidef J hAJ s
  simp only [ContinuousLinearMap.comp_apply, sandwichL_apply]
  have hwhite :
      (A₁ ^ (-(1 / 2) : ℝ) * B₁ * A₁ ^ (-(1 / 2) : ℝ)) * J =
        J * (A₂ ^ (-(1 / 2) : ℝ) * B₂ * A₂ ^ (-(1 / 2) : ℝ)) := by
    rw [Matrix.mul_assoc (A₁ ^ (-(1 / 2) : ℝ) * B₁) (A₁ ^ (-(1 / 2) : ℝ)) J,
      hpow, ← Matrix.mul_assoc (A₁ ^ (-(1 / 2) : ℝ) * B₁) J (A₂ ^ (-(1 / 2) : ℝ)),
      Matrix.mul_assoc (A₁ ^ (-(1 / 2) : ℝ)) B₁ J, hBJ,
      ← Matrix.mul_assoc (A₁ ^ (-(1 / 2) : ℝ)) J B₂, hpow,
      Matrix.mul_assoc J (A₂ ^ (-(1 / 2) : ℝ)) B₂,
      Matrix.mul_assoc J (A₂ ^ (-(1 / 2) : ℝ) * B₂) (A₂ ^ (-(1 / 2) : ℝ))]
  have hsandwich (s : ℝ) (X : Matrix m m ℂ) :
      A₁ ^ s * (J * X * Jᴴ) * A₁ ^ s = J * (A₂ ^ s * X * A₂ ^ s) * Jᴴ :=
    (hA₁.rpow_isHermitian s).sandwich_intertwine (hA₂.rpow_isHermitian s) J (hpow s) X
  rw [hsandwich,
    rpowDeriv_intertwine (hA₁.whiten hB₁) (hA₂.whiten hB₂) J hwhite hp, hsandwich]

/-- Rectangular intertwining of the derivative in the first argument.
Auxiliary to OpenAI's area-law manuscript, Lemma 7.2,
`06-transport.tex`, lines 157–172, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem geomMeanDerivLeft_intertwine
    {A₁ B₁ : Matrix n n ℂ} {A₂ B₂ : Matrix m m ℂ}
    (hA₁ : A₁.PosDef) (hB₁ : B₁.PosDef)
    (hA₂ : A₂.PosDef) (hB₂ : B₂.PosDef)
    (J : Matrix n m ℂ) (hAJ : A₁ * J = J * A₂) (hBJ : B₁ * J = J * B₂)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (H : Matrix m m ℂ) :
    geomMeanDerivLeft p A₁ B₁ (J * H * Jᴴ) =
      J * geomMeanDerivLeft p A₂ B₂ H * Jᴴ := by
  simpa only [geomMeanDerivLeft] using
    geomMeanDerivRight_intertwine hB₁ hA₁ hB₂ hA₂ J hBJ hAJ
      ⟨by linarith [hp.2], by linarith [hp.1]⟩ H

/-- Compression of the derivative in the second argument on an arbitrary
direction. Auxiliary to OpenAI's area-law manuscript, Lemma 7.2,
`06-transport.tex`, lines 157–172, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The common intertwiner need not be an isometry. -/
theorem geomMeanDerivRight_compress
    {A₁ B₁ : Matrix n n ℂ} {A₂ B₂ : Matrix m m ℂ}
    (hA₁ : A₁.PosDef) (hB₁ : B₁.PosDef)
    (hA₂ : A₂.PosDef) (hB₂ : B₂.PosDef)
    (J : Matrix n m ℂ) (hAJ : A₁ * J = J * A₂) (hBJ : B₁ * J = J * B₂)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (X : Matrix n n ℂ) :
    Jᴴ * geomMeanDerivRight p A₁ B₁ X * J =
      geomMeanDerivRight p A₂ B₂ (Jᴴ * X * J) := by
  have hAstar := hA₁.isHermitian.conjTranspose_intertwine hA₂.isHermitian J hAJ
  have hBstar := hB₁.isHermitian.conjTranspose_intertwine hB₂.isHermitian J hBJ
  simpa only [conjTranspose_conjTranspose] using
    (geomMeanDerivRight_intertwine hA₂ hB₂ hA₁ hB₁ Jᴴ hAstar hBstar hp X).symm

/-- Compression of the derivative in the first argument on an arbitrary
direction. Auxiliary to OpenAI's area-law manuscript, Lemma 7.2,
`06-transport.tex`, lines 157–172, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem geomMeanDerivLeft_compress
    {A₁ B₁ : Matrix n n ℂ} {A₂ B₂ : Matrix m m ℂ}
    (hA₁ : A₁.PosDef) (hB₁ : B₁.PosDef)
    (hA₂ : A₂.PosDef) (hB₂ : B₂.PosDef)
    (J : Matrix n m ℂ) (hAJ : A₁ * J = J * A₂) (hBJ : B₁ * J = J * B₂)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (X : Matrix n n ℂ) :
    Jᴴ * geomMeanDerivLeft p A₁ B₁ X * J =
      geomMeanDerivLeft p A₂ B₂ (Jᴴ * X * J) := by
  simpa only [geomMeanDerivLeft] using
    geomMeanDerivRight_compress hB₁ hA₁ hB₂ hA₂ J hBJ hAJ
      ⟨by linarith [hp.2], by linarith [hp.1]⟩ X

end Matrix
