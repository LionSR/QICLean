/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixGramUnitary
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Gram conjugation identities for complex matrices

This file collects algebraic identities relating dressed matrix conjugations,
Gram matrices, relative Gram ratios, and unitary normalization.  The results
are stated for arbitrary finite complex matrix algebras.
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If conjugation by an invertible gauge carries `B` to the dressing of an
abstract target `C`, then conjugation by the Gram matrix carries `B` to `C`.

This is a conditional algebraic route to the relative Gram identity in
arXiv:1606.00608, proof of Proposition 4.13, lines 1909--1919.  The source's
reflected marked-chain argument does not identify such a target separately
for each sector. -/
theorem gram_conj_eq_of_dressed_target
    {X B C : Matrix n n ℂ} (hX : IsUnit X.det)
    (hdress : X * B * X⁻¹ = X⁻¹ᴴ * C * Xᴴ) :
    Xᴴ * X * B * (Xᴴ * X)⁻¹ = C := by
  have hXH : IsUnit (Xᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hX.star
  have h1 : Xᴴ * (X * B * X⁻¹) * X⁻¹ᴴ = Xᴴ * X * B * (Xᴴ * X)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.conjTranspose_nonsing_inv]
    simp only [Matrix.mul_assoc]
  have h2 : Xᴴ * (X⁻¹ᴴ * C * Xᴴ) * X⁻¹ᴴ = C := by
    rw [Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hXH, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hXH, Matrix.mul_one]
  rw [← h1, hdress, h2]

/-- **From the first displayed diagram to the second** (arXiv:1606.00608,
proof of Proposition 4.13, lines 1909--1919): if a letter dressed by an
invertible gauge equals its adjoint dressing,
$XBX^{-1} = (X^{-1})^\dagger B^\dagger X^\dagger$, then conjugation by the
Gram matrix $X^\dagger X$ carries the letter to its adjoint. -/
theorem gram_conj_eq_conjTranspose_of_dressed_adjoint
    {X B : Matrix n n ℂ} (hX : IsUnit X.det)
    (hdress : X * B * X⁻¹ = X⁻¹ᴴ * Bᴴ * Xᴴ) :
    Xᴴ * X * B * (Xᴴ * X)⁻¹ = Bᴴ :=
  gram_conj_eq_of_dressed_target hX hdress

/-- **The second displayed diagram** (arXiv:1606.00608, proof of Proposition
4.13, lines 1914--1919): two gauges whose dressings carry the same letter `B`
to the same target `C` have equal Gram conjugations. -/
theorem gram_conj_eq_gram_conj_of_common_dressed_target
    {X Y B C : Matrix n n ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (hdX : X * B * X⁻¹ = X⁻¹ᴴ * C * Xᴴ)
    (hdY : Y * B * Y⁻¹ = Y⁻¹ᴴ * C * Yᴴ) :
    Xᴴ * X * B * (Xᴴ * X)⁻¹ = Yᴴ * Y * B * (Yᴴ * Y)⁻¹ := by
  rw [gram_conj_eq_of_dressed_target hX hdX,
    gram_conj_eq_of_dressed_target hY hdY]

/-- **The second displayed diagram** (arXiv:1606.00608, proof of Proposition
4.13, lines 1914--1919): two gauges whose dressings both equal the adjoint
dressing have equal Gram conjugations,
$X^\dagger X\,B\,(X^\dagger X)^{-1} = Y^\dagger Y\,B\,(Y^\dagger Y)^{-1}$. -/
theorem gram_conj_eq_gram_conj_of_dressed_adjoint
    {X Y B : Matrix n n ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (hdX : X * B * X⁻¹ = X⁻¹ᴴ * Bᴴ * Xᴴ)
    (hdY : Y * B * Y⁻¹ = Y⁻¹ᴴ * Bᴴ * Yᴴ) :
    Xᴴ * X * B * (Xᴴ * X)⁻¹ = Yᴴ * Y * B * (Yᴴ * Y)⁻¹ :=
  gram_conj_eq_gram_conj_of_common_dressed_target hX hY hdX hdY

/-- **The relative commutant in the second displayed diagram**
(arXiv:1606.00608, proof of Proposition 4.13, lines 1914--1921): if two
invertible matrices have the same Gram conjugation of a matrix, then the
ratio of their Gram matrices commutes with that matrix. -/
theorem commute_gram_ratio_of_gram_conj_eq
    {X Y B : Matrix n n ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (h : Xᴴ * X * B * (Xᴴ * X)⁻¹ = Yᴴ * Y * B * (Yᴴ * Y)⁻¹) :
    (Yᴴ * Y)⁻¹ * (Xᴴ * X) * B =
      B * ((Yᴴ * Y)⁻¹ * (Xᴴ * X)) := by
  have hGX : IsUnit (Xᴴ * X).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact hX.star.mul hX
  have hGY : IsUnit (Yᴴ * Y).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact hY.star.mul hY
  have hGYinv : (Yᴴ * Y)⁻¹ * (Yᴴ * Y) = 1 :=
    Matrix.nonsing_inv_mul _ hGY
  calc
    (Yᴴ * Y)⁻¹ * (Xᴴ * X) * B =
        (Yᴴ * Y)⁻¹ * (Xᴴ * X) * B * ((Xᴴ * X)⁻¹ * (Xᴴ * X)) := by
          rw [Matrix.nonsing_inv_mul _ hGX, Matrix.mul_one]
    _ = (Yᴴ * Y)⁻¹ *
        (Xᴴ * X * B * (Xᴴ * X)⁻¹) * (Xᴴ * X) := by
          simp only [Matrix.mul_assoc]
    _ = (Yᴴ * Y)⁻¹ *
        (Yᴴ * Y * B * (Yᴴ * Y)⁻¹) * (Xᴴ * X) := by rw [h]
    _ = ((Yᴴ * Y)⁻¹ * (Yᴴ * Y)) * B *
        ((Yᴴ * Y)⁻¹ * (Xᴴ * X)) := by noncomm_ring
    _ = B * ((Yᴴ * Y)⁻¹ * (Xᴴ * X)) := by rw [hGYinv, Matrix.one_mul]

/-- For a self-adjoint matrix, equality with its dressing by the inverse
conjugate transpose makes the Gram matrix $X^\dagger X$ commute with it.

This is a purely algebraic same-letter specialization.  The vertical-sector
identity in arXiv:1606.00608, proof of Proposition 4.13, lines 1909--1919,
instead exchanges the two oriented horizontal bond indices. -/
theorem commute_gram_of_dressed_adjoint_of_conjTranspose_eq
    {X B : Matrix n n ℂ} (hX : IsUnit X.det)
    (hdress : X * B * X⁻¹ = X⁻¹ᴴ * Bᴴ * Xᴴ) (hB : Bᴴ = B) :
    Xᴴ * X * B = B * (Xᴴ * X) := by
  have hG : IsUnit (Xᴴ * X).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact hX.star.mul hX
  have h := gram_conj_eq_conjTranspose_of_dressed_adjoint hX hdress
  rw [hB] at h
  calc
    Xᴴ * X * B = Xᴴ * X * B * ((Xᴴ * X)⁻¹ * (Xᴴ * X)) := by
      rw [Matrix.nonsing_inv_mul _ hG, Matrix.mul_one]
    _ = Xᴴ * X * B * (Xᴴ * X)⁻¹ * (Xᴴ * X) := by
      simp only [Matrix.mul_assoc]
    _ = B * (Xᴴ * X) := by rw [h]

/-- A relative Gram identity gives the unitary normalization of the relative
gauge.  This is the two-gauge form of the normalization used in
arXiv:1606.00608, proof of Proposition 4.13, lines 1904--1908. -/
theorem smul_mul_nonsing_inv_mem_unitaryGroup_of_gram_eq_smul
    {X Y : Matrix n n ℂ} (hY : IsUnit Y.det) {ω : ℝ} (hω : 0 < ω)
    (hgram : Xᴴ * X = (ω : ℂ) • (Yᴴ * Y)) :
    ((Real.sqrt ω : ℂ))⁻¹ • (X * Y⁻¹) ∈ Matrix.unitaryGroup n ℂ := by
  apply smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one hω
  have hYH : IsUnit (Yᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hY.star
  have hleft : Y⁻¹ᴴ * Yᴴ = 1 := by
    rw [Matrix.conjTranspose_nonsing_inv]
    exact Matrix.nonsing_inv_mul _ hYH
  have hright : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv _ hY
  calc
    (X * Y⁻¹)ᴴ * (X * Y⁻¹) = Y⁻¹ᴴ * (Xᴴ * X) * Y⁻¹ := by
      rw [Matrix.conjTranspose_mul]
      noncomm_ring
    _ = Y⁻¹ᴴ * ((ω : ℂ) • (Yᴴ * Y)) * Y⁻¹ := by rw [hgram]
    _ = (ω : ℂ) • ((Y⁻¹ᴴ * Yᴴ) * (Y * Y⁻¹)) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      noncomm_ring
    _ = (ω : ℂ) • 1 := by rw [hleft, hright, Matrix.one_mul]

end Matrix
