/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import QICLean.Analysis.TraceNorm.TraceNormContractivity

/-!
# A trace-norm lower bound by the ordinary Petz overlap

Wolf, *Quantum Channels & Operations*, Section 8.5, the lemma containing
Equations (8.54)–(8.55), `Notes/WolfNoteTexSource/ch08_distance_measures.tex`,
lines 660–670. For positive-semidefinite `A, B` and `s ∈ [0, 1]`,
Equation (8.54) reads
`‖A - B‖₁ ≥ tr[A + B] - 2 tr[Aˢ B¹⁻ˢ]`.

Wolf gives no argument for Equation (8.54). The proof here is the operator
monotonicity argument for the equivalent inequality
`tr A - tr[Aˢ B¹⁻ˢ] ≤ tr (A - B)₊`
(`Matrix.re_trace_sub_re_trace_rpow_mul_rpow_le_posPart`). Put
`M = B + (A - B)₊`, so that `A ≤ M` and `B ≤ M`. Monotonicity of
`X ↦ Xᵗ` for `t ∈ [0, 1]` (`CFC.rpow_le_rpow`) and positivity of trace
pairings give
`tr A = tr[Aˢ A¹⁻ˢ] ≤ tr[Aˢ M¹⁻ˢ]`,
`tr[Aˢ (M¹⁻ˢ - B¹⁻ˢ)] ≤ tr[Mˢ (M¹⁻ˢ - B¹⁻ˢ)] = tr M - tr[Mˢ B¹⁻ˢ]`, and
`tr B = tr[Bˢ B¹⁻ˢ] ≤ tr[Mˢ B¹⁻ˢ]`.
Adding them yields the bound by `tr M - tr B = tr (A - B)₊`.

Powers use the continuous functional calculus with `X ^ (0 : ℝ) = 1`, so no
support or invertibility condition enters; singular `A` and `B` and the
endpoints `s = 0, 1` are included. The overlap `Re tr[Aˢ B¹⁻ˢ]` is the
ordinary Petz overlap `Matrix.petzOverlap s A B`.

Equation (8.55), whose right side involves the negative power `B⁻ˢ`, is not
treated here.

## Main results

* `Matrix.PosSemidef.rpow_mul_rpow_one_sub`: `τˢ τ¹⁻ˢ = τ` for `s ∈ [0, 1]`.
* `Matrix.re_trace_sub_re_trace_rpow_mul_rpow_le_posPart`.
* `Matrix.re_trace_add_sub_two_mul_re_trace_rpow_mul_rpow_le`: Equation (8.54)
  with `Re tr |A - B|`.
* `Matrix.re_trace_add_sub_two_mul_re_trace_rpow_mul_rpow_le_traceNorm`:
  Equation (8.54) with `Matrix.traceNorm` on `Fin D`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complementary nonnegative powers of a positive-semidefinite matrix
multiply to the matrix, including when it is singular:
`τ ^ s * τ ^ (1 - s) = τ` for `s ∈ [0, 1]`. -/
theorem PosSemidef.rpow_mul_rpow_one_sub {τ : Matrix n n ℂ} (hτ : τ.PosSemidef)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : τ ^ s * τ ^ (1 - s) = τ := by
  rw [CFC.rpow_eq_cfc_real hτ.nonneg, CFC.rpow_eq_cfc_real hτ.nonneg,
    ← cfc_mul _ _ τ (τ.finite_real_spectrum.continuousOn _)
      (τ.finite_real_spectrum.continuousOn _)]
  calc
    cfc (fun x : ℝ => x ^ s * x ^ (1 - s)) τ = cfc (fun x : ℝ => x) τ := by
      apply cfc_congr
      intro x hx
      change x ^ s * x ^ (1 - s) = x
      rw [← Real.rpow_add_of_nonneg (spectrum_nonneg_of_nonneg hτ.nonneg hx)
        hs.1 (sub_nonneg.mpr hs.2), add_sub_cancel, Real.rpow_one]
    _ = τ := cfc_id ℝ τ hτ.isHermitian

omit [DecidableEq n] in
/-- Pairing with a positive-semidefinite matrix on the left is monotone in
the Loewner order. -/
private lemma re_trace_mul_le_mul_left {Z X Y : Matrix n n ℂ} (hZ : Z.PosSemidef)
    (hXY : X ≤ Y) : (Z * X).trace.re ≤ (Z * Y).trace.re := by
  have h := hZ.re_trace_mul_nonneg (Matrix.le_iff.mp hXY)
  rw [Matrix.mul_sub, trace_sub, Complex.sub_re] at h
  linarith

omit [DecidableEq n] in
/-- Pairing with a positive-semidefinite matrix on the right is monotone in
the Loewner order. -/
private lemma re_trace_mul_le_mul_right {Z X Y : Matrix n n ℂ} (hZ : Z.PosSemidef)
    (hXY : X ≤ Y) : (X * Z).trace.re ≤ (Y * Z).trace.re := by
  rw [trace_mul_comm X, trace_mul_comm Y]
  exact re_trace_mul_le_mul_left hZ hXY

/-- **Positive-part bound for the ordinary overlap.** For positive-semidefinite
`A, B` and `s ∈ [0, 1]`,
`tr A - tr[Aˢ B¹⁻ˢ] ≤ tr (A - B)₊`.

This is the form of Wolf, Equation (8.54), `ch08_distance_measures.tex`,
lines 663–665, that the operator monotonicity argument proves. -/
theorem re_trace_sub_re_trace_rpow_mul_rpow_le_posPart {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    A.trace.re - (A ^ s * B ^ (1 - s)).trace.re ≤ ((A - B)⁺).trace.re := by
  have hs' : 1 - s ∈ Set.Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr hs.2, by linarith [hs.1]⟩
  have hsa : IsSelfAdjoint (A - B) := isSelfAdjoint_iff.mpr (hA.isHermitian.sub hB.isHermitian)
  have hdecomp := CFC.posPart_sub_negPart (A - B) hsa
  have hNpsd : ((A - B)⁻).PosSemidef := nonneg_iff_posSemidef.mp (CFC.negPart_nonneg _)
  have hCpsd : ((A - B)⁺).PosSemidef := nonneg_iff_posSemidef.mp (CFC.posPart_nonneg _)
  generalize (A - B)⁺ = C at hdecomp hCpsd ⊢
  generalize (A - B)⁻ = N at hdecomp hNpsd
  set M := B + C with hM
  have hMpsd : M.PosSemidef := hB.add hCpsd
  have hAM : A ≤ M := by
    rw [Matrix.le_iff]
    have : M - A = N := by
      rw [hM, show B + C - A = C - (A - B) by abel, ← hdecomp]
      abel
    rw [this]
    exact hNpsd
  have hBM : B ≤ M := by
    rw [Matrix.le_iff, hM, add_sub_cancel_left]
    exact hCpsd
  have hApow : (A ^ s).PosSemidef := nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hBpow : (B ^ (1 - s)).PosSemidef := nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hAs : A ^ s ≤ M ^ s := CFC.rpow_le_rpow hs hAM
  have hBs : B ^ s ≤ M ^ s := CFC.rpow_le_rpow hs hBM
  have hA1s : A ^ (1 - s) ≤ M ^ (1 - s) := CFC.rpow_le_rpow hs' hAM
  have hB1s : B ^ (1 - s) ≤ M ^ (1 - s) := CFC.rpow_le_rpow hs' hBM
  -- `tr A ≤ tr[Aˢ M¹⁻ˢ]`.
  have h₁ : A.trace.re ≤ (A ^ s * M ^ (1 - s)).trace.re := by
    have h := re_trace_mul_le_mul_left hApow hA1s
    rwa [hA.rpow_mul_rpow_one_sub hs] at h
  -- `tr[Aˢ (M¹⁻ˢ - B¹⁻ˢ)] ≤ tr[Mˢ (M¹⁻ˢ - B¹⁻ˢ)]`.
  have h₂ := re_trace_mul_le_mul_right (Matrix.le_iff.mp hB1s) hAs
  rw [Matrix.mul_sub, Matrix.mul_sub, trace_sub, trace_sub, Complex.sub_re,
    Complex.sub_re, hMpsd.rpow_mul_rpow_one_sub hs] at h₂
  -- `tr B ≤ tr[Mˢ B¹⁻ˢ]`.
  have h₃ := re_trace_mul_le_mul_right hBpow hBs
  rw [hB.rpow_mul_rpow_one_sub hs] at h₃
  have hMtr : M.trace.re = B.trace.re + C.trace.re := by
    rw [hM, trace_add, Complex.add_re]
  linarith

/-- **Wolf, Equation (8.54).** For positive-semidefinite `A, B` and
`s ∈ [0, 1]`,
`‖A - B‖₁ ≥ tr[A + B] - 2 tr[Aˢ B¹⁻ˢ]`, with `‖X‖₁ = Re tr |X|`.

Wolf, Lemma in Section 8.5, Equation (8.54), `ch08_distance_measures.tex`,
lines 660–665. -/
theorem re_trace_add_sub_two_mul_re_trace_rpow_mul_rpow_le {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (A + B).trace.re - 2 * (A ^ s * B ^ (1 - s)).trace.re ≤
      (CFC.abs (A - B)).trace.re := by
  have hsa : IsSelfAdjoint (A - B) := isSelfAdjoint_iff.mpr (hA.isHermitian.sub hB.isHermitian)
  have h := re_trace_sub_re_trace_rpow_mul_rpow_le_posPart hA hB hs
  have habs : (CFC.abs (A - B)).trace.re = ((A - B)⁺).trace.re + ((A - B)⁻).trace.re := by
    rw [← CFC.posPart_add_negPart (A - B) hsa, trace_add, Complex.add_re]
  have hdiff := congrArg (fun X : Matrix n n ℂ ↦ X.trace.re)
    (CFC.posPart_sub_negPart (A - B) hsa)
  simp only [trace_sub, Complex.sub_re] at hdiff
  rw [habs, trace_add, Complex.add_re]
  linarith

/-- **Wolf, Equation (8.54)** with the trace norm `Matrix.traceNorm` on `Fin D`.

Wolf, Lemma in Section 8.5, Equation (8.54), `ch08_distance_measures.tex`,
lines 660–665. -/
theorem re_trace_add_sub_two_mul_re_trace_rpow_mul_rpow_le_traceNorm {D : ℕ}
    {A B : Matrix (Fin D) (Fin D) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (A + B).trace.re - 2 * (A ^ s * B ^ (1 - s)).trace.re ≤ traceNorm (A - B) := by
  rw [traceNorm_eq_re_trace_abs]
  exact re_trace_add_sub_two_mul_re_trace_rpow_mul_rpow_le hA hB hs

end Matrix
