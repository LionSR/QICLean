/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.TracePurity
import QICLean.Channel.Schwarz.AbstractMultiplicativeDomain

/-!
# Trace-preserving Schwarz maps are unital

A positive trace-preserving endomorphism of a nonzero complex matrix algebra
that satisfies the Schwarz inequality fixes the identity. This supplies one
scalar-normalization prerequisite for Wolf's use of Schwarz maps at the end
of the proof of Theorem 6.16.

The proof uses no complete-positivity hypothesis.  Schwarz at the identity
bounds the trace of `T(1) ^ 2` above by the dimension, while the Hermitian
trace-square inequality bounds it below by the same value.  Its equality case
then forces `T(1)` to be the identity.
-/

open scoped Matrix ComplexOrder MatrixOrder

variable {D : ℕ}

local notation "MatD" => Matrix (Fin D) (Fin D) ℂ

/-- A positive trace-preserving Schwarz endomorphism of a nonzero complex
matrix algebra is unital.

This auxiliary fact supports the omitted scalar step in Wolf Theorem 6.16 and
is not separately stated there. Source:
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1660--1663. -/
theorem IsPositiveMap.map_one_eq_one_of_tracePreserving_of_isSchwarzMap
    [NeZero D] {T : MatD →ₗ[ℂ] MatD}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap T) : T 1 = 1 := by
  let B : MatD := T 1
  have hB : B.PosSemidef := hPos 1 Matrix.PosSemidef.one
  have hDef : (B - B ^ 2).PosSemidef := by
    simpa only [B, Matrix.conjTranspose_one, Matrix.one_mul, pow_two] using
      hSchwarz (1 : MatD)
  have hTraceB : B.trace = D := by
    simpa only [B, Matrix.trace_one, Fintype.card_fin] using hTP (1 : MatD)
  have hDefTrace : 0 ≤ (B - B ^ 2).trace.re :=
    (Complex.nonneg_iff.mp hDef.trace_nonneg).1
  have hTraceSqLe : (B ^ 2).trace.re ≤ D := by
    simpa only [Matrix.trace_sub, Complex.sub_re, hTraceB, Complex.natCast_re,
      sub_nonneg] using hDefTrace
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hPurity := hB.isHermitian.trace_re_sq_le_card_mul_trace_sq_re
  have hTraceSqGe : (D : ℝ) ≤ (B ^ 2).trace.re := by
    rw [hTraceB, Complex.natCast_re] at hPurity
    nlinarith
  have hTraceSq : (B ^ 2).trace.re = D := le_antisymm hTraceSqLe hTraceSqGe
  have hPurityEq : B.trace.re ^ 2 = D * (B ^ 2).trace.re := by
    rw [hTraceB, Complex.natCast_re, hTraceSq]
    rw [pow_two]
  obtain ⟨r, hBr⟩ :=
    hB.isHermitian.trace_re_sq_eq_card_mul_trace_sq_re_iff.mp hPurityEq
  have hTraceScalar := hTraceB
  rw [hBr, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin] at hTraceScalar
  have hTraceScalarRe := congrArg Complex.re hTraceScalar
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, mul_zero,
    sub_zero] at hTraceScalarRe
  have hr : r = 1 := by
    nlinarith
  change B = 1
  simp only [hBr, hr, Complex.ofReal_one, one_smul]
