/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixGramConjugation
import QICLean.Algebra.ScalarCommutant
import QICLean.Kraus.Injectivity
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Commutant rigidity for normal finite Kraus families

A normal finite Kraus family spans the full matrix algebra after blocking, so
a matrix commuting with every family member is scalar.  Applying this to Gram
matrices yields positive scalar comparison and unitary normalization results.

The theorem docstrings retain source notes for applications to gauge rigidity.
-/

open scoped Matrix ComplexOrder

namespace Kraus

variable {d D : ℕ}

/-- A matrix commuting with every matrix of a normal finite Kraus family is a
scalar multiple of the identity. Commutation extends from the matrices to all
word evaluations, and after blocking these span the full matrix algebra.

This is the commutant triviality behind the step "since $M_\alpha$ is a NT in
the vertical direction" in the proof of Proposition 4.13 of arXiv:1606.00608,
line 1921. -/
theorem IsNormal.eq_smul_one_of_commute
    {A : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsNormal A)
    {S : Matrix (Fin D) (Fin D) ℂ} (hS : ∀ i, S * A i = A i * S) :
    ∃ c : ℂ, S = c • 1 := by
  obtain ⟨N, _hNpos, hN⟩ := hA
  have hwords : ∀ M ∈ Set.range fun σ : Fin N → Fin d => Kraus.evalWord A (List.ofFn σ),
      S * M = M * S := by
    rintro _ ⟨σ, rfl⟩
    exact Kraus.commutes_evalWord_of_commutes_letters S A hS (List.ofFn σ)
  obtain ⟨c, hc⟩ := Matrix.isScalar_of_commute_span_eq_top S hN hwords
  refine ⟨c, ?_⟩
  rw [hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

/-- **Relative equation eq3:proof.IV.12.** If two invertible Gram matrices
induce the same conjugation on every letter of a normal finite Kraus family,
then one Gram matrix is a positive real multiple of the other:
$X^\dagger X=\omega Y^\dagger Y$ with $\omega>0$.

This is the conclusion drawn from the second displayed diagram in the proof
of Proposition 4.13 of arXiv:1606.00608, lines 1914--1921.  It compares the
sector $k$ directly with the distinguished sector $1$ and does not assume that
the matrices of the representative family are self-adjoint. -/
theorem IsNormal.gram_eq_pos_smul_gram_of_gram_conj_eq
    {A : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsNormal A)
    {X Y : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (hgram : ∀ i,
      Xᴴ * X * A i * (Xᴴ * X)⁻¹ = Yᴴ * Y * A i * (Yᴴ * Y)⁻¹) :
    ∃ ω : ℝ, 0 < ω ∧ Xᴴ * X = (ω : ℂ) • (Yᴴ * Y) := by
  have hGY : IsUnit (Yᴴ * Y).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact hY.star.mul hY
  have hcomm : ∀ i, (Yᴴ * Y)⁻¹ * (Xᴴ * X) * A i =
      A i * ((Yᴴ * Y)⁻¹ * (Xᴴ * X)) := fun i =>
    Matrix.commute_gram_ratio_of_gram_conj_eq hX hY (hgram i)
  obtain ⟨c, hc⟩ := hA.eq_smul_one_of_commute hcomm
  have hcGram : Xᴴ * X = c • (Yᴴ * Y) := by
    calc
      Xᴴ * X = (Yᴴ * Y) * ((Yᴴ * Y)⁻¹ * (Xᴴ * X)) := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGY, Matrix.one_mul]
      _ = (Yᴴ * Y) * (c • 1) := by rw [hc]
      _ = c • (Yᴴ * Y) := by
        rw [Matrix.mul_smul, Matrix.mul_one]
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst D
    refine ⟨1, by positivity, ?_⟩
    ext i
    exact i.elim0
  · let i : Fin D := ⟨0, hD⟩
    have hGXpd : (Xᴴ * X).PosDef :=
      Matrix.PosDef.conjTranspose_mul_self X
        (Matrix.mulVec_injective_of_det_ne_zero hX.ne_zero)
    have hGYpd : (Yᴴ * Y).PosDef :=
      Matrix.PosDef.conjTranspose_mul_self Y
        (Matrix.mulVec_injective_of_det_ne_zero hY.ne_zero)
    have hcEntry : (Xᴴ * X) i i = c * (Yᴴ * Y) i i := by
      simpa [Matrix.smul_apply] using congr_fun (congr_fun hcGram i) i
    have hcPos : (0 : ℂ) < c := by
      apply pos_of_mul_pos_left
      · rw [← hcEntry]
        exact hGXpd.diag_pos
      · exact hGYpd.diag_pos.le
    obtain ⟨hcRe, hcIm⟩ := Complex.pos_iff.mp hcPos
    refine ⟨c.re, hcRe, ?_⟩
    rw [hcGram]
    congr 1
    exact (Complex.ext (Complex.ofReal_re c.re)
      (by rw [Complex.ofReal_im]; exact hcIm)).symm

/-- **Equation eq3 with the distinguished gauge fixed to the identity.**
If an invertible gauge's Gram conjugation fixes every member of a normal finite
Kraus family, then its Gram matrix is a positive real multiple of the identity.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem IsNormal.gram_eq_pos_smul_one_of_gram_conj_eq
    {A : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det)
    (hgram : ∀ i, Xᴴ * X * A i * (Xᴴ * X)⁻¹ = A i) :
    ∃ ω : ℝ, 0 < ω ∧ Xᴴ * X = (ω : ℂ) • 1 := by
  have hOne : IsUnit (1 : Matrix (Fin D) (Fin D) ℂ).det := by
    simp
  obtain ⟨ω, hω, hGram⟩ :=
    hA.gram_eq_pos_smul_gram_of_gram_conj_eq hX hOne (fun i => by
      simpa using hgram i)
  exact ⟨ω, hω, by simpa using hGram⟩

/-- An invertible gauge whose Gram conjugation fixes a normal finite Kraus
family becomes unitary after division by the square root of its positive Gram
scalar.

Source: arXiv:1606.00608, proof of Proposition 4.13, lines 1903--1921. -/
theorem IsNormal.exists_unitary_normalization_of_gram_conj_eq
    {A : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det)
    (hgram : ∀ i, Xᴴ * X * A i * (Xᴴ * X)⁻¹ = A i) :
    ∃ ω : ℝ, 0 < ω ∧
      ((Real.sqrt ω : ℂ))⁻¹ • X ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  obtain ⟨ω, hω, hGram⟩ :=
    hA.gram_eq_pos_smul_one_of_gram_conj_eq hX hgram
  have hOne : IsUnit (1 : Matrix (Fin D) (Fin D) ℂ).det := by
    simp
  have hUnit := Matrix.smul_mul_nonsing_inv_mem_unitaryGroup_of_gram_eq_smul
    (X := X) (Y := (1 : Matrix (Fin D) (Fin D) ℂ)) hOne hω
    (by simpa using hGram)
  exact ⟨ω, hω, by simpa using hUnit⟩

/-- **Conditional relative equation eq3 from a common dressed target.** If two
invertible gauges dress every member of a normal finite Kraus family to the
same target, then their Gram matrices differ by a positive real scalar. The
target may depend on the letter.

This is an algebraic consequence of the Figure 8 equality in
arXiv:1606.00608, proof of Proposition 4.13, lines 1909--1921.  It is not the
source-facing reflected marked-chain statement. -/
theorem IsNormal.gram_eq_pos_smul_gram_of_common_dressed_target
    {A C : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsNormal A)
    {X Y : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (hdX : ∀ i, X * A i * X⁻¹ = X⁻¹ᴴ * C i * Xᴴ)
    (hdY : ∀ i, Y * A i * Y⁻¹ = Y⁻¹ᴴ * C i * Yᴴ) :
    ∃ ω : ℝ, 0 < ω ∧ Xᴴ * X = (ω : ℂ) • (Yᴴ * Y) :=
  hA.gram_eq_pos_smul_gram_of_gram_conj_eq hX hY fun i =>
    Matrix.gram_conj_eq_gram_conj_of_common_dressed_target
      hX hY (hdX i) (hdY i)

/-- The relative gauge of the preceding theorem becomes unitary after
division by the square root of its positive Gram scalar.  In the normalization
$Y=\Id$, this is $\omega^{-1/2}X$ from arXiv:1606.00608, lines 1904--1908. -/
theorem IsNormal.smul_mul_nonsing_inv_mem_unitaryGroup_of_common_dressed_target
    {A C : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsNormal A)
    {X Y : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (hdX : ∀ i, X * A i * X⁻¹ = X⁻¹ᴴ * C i * Xᴴ)
    (hdY : ∀ i, Y * A i * Y⁻¹ = Y⁻¹ᴴ * C i * Yᴴ) :
    ∃ ω : ℝ, 0 < ω ∧
      ((Real.sqrt ω : ℂ))⁻¹ • (X * Y⁻¹) ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  obtain ⟨ω, hω, hgram⟩ :=
    hA.gram_eq_pos_smul_gram_of_common_dressed_target hX hY hdX hdY
  exact ⟨ω, hω,
    Matrix.smul_mul_nonsing_inv_mem_unitaryGroup_of_gram_eq_smul hY hω hgram⟩

/-- **Equation eq3:proof.IV.12 in the normalization $X_{\alpha,1} = \Id$.**
If $X \ne 0$ and the Gram matrix $X^\dagger X$ commutes with every matrix of
a normal finite Kraus family, then $X^\dagger X = \omega\,\Id$ for a
necessarily positive constant $\omega$ (arXiv:1606.00608, proof of Proposition
4.13, lines 1904--1908 and 1921). The source's gauges $X_{\alpha,k}$ are
invertible; only $X \ne 0$ is needed here, and invertibility of $X$ follows from the
conclusion. -/
theorem IsNormal.conjTranspose_mul_self_eq_smul_one_of_commute
    {A : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ≠ 0)
    (hcomm : ∀ i, Xᴴ * X * A i = A i * (Xᴴ * X)) :
    ∃ ω : ℝ, 0 < ω ∧ Xᴴ * X = (ω : ℂ) • 1 := by
  obtain ⟨c, hc⟩ := hA.eq_smul_one_of_commute hcomm
  have hW_psd : (Xᴴ * X).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self X
  have hW_ne : Xᴴ * X ≠ 0 := fun h0 =>
    hX (Matrix.conjTranspose_mul_self_eq_zero.mp h0)
  have hc_ne : c ≠ 0 := fun h0 => hW_ne (by rw [hc, h0, zero_smul])
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · exact absurd (by subst h0; exact Matrix.ext fun i => i.elim0) hX
    · exact h0
  have hc_nonneg : (0 : ℂ) ≤ c := by
    have hd := hW_psd.diag_nonneg (i := (⟨0, hD⟩ : Fin D))
    have hWii : (Xᴴ * X) (⟨0, hD⟩ : Fin D) (⟨0, hD⟩ : Fin D) = c := by
      rw [hc]
      simp [Matrix.smul_apply, Matrix.one_apply_eq]
    rwa [hWii] at hd
  obtain ⟨-, hc_im⟩ := Complex.nonneg_iff.mp hc_nonneg
  have hc_pos : (0 : ℂ) < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc_ne)
  obtain ⟨hc_re_pos, -⟩ := Complex.pos_iff.mp hc_pos
  refine ⟨c.re, hc_re_pos, ?_⟩
  rw [hc]
  congr 1
  exact (Complex.ext (Complex.ofReal_re c.re)
    (by rw [Complex.ofReal_im]; exact hc_im)).symm

/-- **The isometric normalization $U_{\alpha,k} =
\omega_{\alpha,k}^{-1/2}X_{\alpha,k}$** (arXiv:1606.00608, proof of
Proposition 4.13, lines 1906--1908): a nonzero $X$ whose Gram matrix commutes
with every matrix of a normal finite Kraus family becomes unitary after
division by the square root of the positive constant from eq3:proof.IV.12. -/
theorem IsNormal.smul_mem_unitaryGroup_of_commute
    {A : Fin d → Matrix (Fin D) (Fin D) ℂ} (hA : Kraus.IsNormal A)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ≠ 0)
    (hcomm : ∀ i, Xᴴ * X * A i = A i * (Xᴴ * X)) :
    ∃ ω : ℝ, 0 < ω ∧
      ((Real.sqrt ω : ℂ))⁻¹ • X ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  obtain ⟨ω, hω, hXX⟩ := hA.conjTranspose_mul_self_eq_smul_one_of_commute hX hcomm
  exact ⟨ω, hω,
    Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one hω hXX⟩

end Kraus
