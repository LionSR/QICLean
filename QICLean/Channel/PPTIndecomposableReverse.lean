/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.PPTIndecomposable
import QICLean.Channel.DecomposableWitness
import QICLean.Channel.Schwarz.PositiveMapProperties

/-!
# Indecomposable positive maps yield PPT entangled states

This module proves the separating-hyperplane direction of Wolf, Chapter 3,
Proposition 3.5.  The proof follows Lewenstein--Kraus--Cirac--Horodecki,
Theorem 3, on the trace-one compact base of decomposable witnesses

`a P + (1-a) Q^{T₁}`,

where `P,Q` are density operators.  The partial transpose is always on Wolf's
first tensor factor.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace Matrix

variable {d d' : ℕ}

private theorem IsNormalizedDecomposableWitness.isHermitian
    {W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hW : IsNormalizedDecomposableWitness W) : W.IsHermitian := by
  obtain ⟨a, P, Q, _ha, hP, _hPtr, hQ, _hQtr, rfl⟩ := hW
  exact (hP.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))).add
    ((hQ.isHermitian.partialTransposeLeft).smul
      (isSelfAdjoint_iff.mpr (by simp)))

private theorem posSemidef_and_isPPT_of_nonneg_on_normalized_decomposable
    [NeZero d] [NeZero d']
    {R : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hR : R.IsHermitian)
    (hRnonneg : ∀ X, IsNormalizedDecomposableWitness X →
      0 ≤ (X * R).trace.re) :
    R.PosSemidef ∧ IsPPT R := by
  classical
  let x₀ : Fin d × Fin d' := (0, 0)
  refine ⟨?_, ?_⟩
  · apply PosSemidef.of_forall_trace_mul_nonneg hR
    intro B hB
    let B₀ := normalizePosSemidef x₀ B
    have hB₀ : B₀.PosSemidef := normalizePosSemidef_posSemidef x₀ hB
    have hB₀tr : B₀.trace = 1 := normalizePosSemidef_trace x₀ hB
    have hB₀mem : IsNormalizedDecomposableWitness B₀ := by
      refine ⟨1, B₀, B₀, by simp, hB₀, hB₀tr, hB₀, hB₀tr, ?_⟩
      simp
    have hB₀nonneg : 0 ≤ (R * B₀).trace.re := by
      have h := hRnonneg B₀ hB₀mem
      rw [trace_mul_comm] at h
      exact h
    have hB₀im : (R * B₀).trace.im = 0 := by
      have hreal : (R * B₀).trace = star ((R * B₀).trace) := by
        rw [← trace_conjTranspose, conjTranspose_mul, hB₀.isHermitian.eq, hR.eq,
          trace_mul_comm]
      have him := congrArg Complex.im hreal
      simp only [Complex.star_def, Complex.conj_im] at him
      linarith
    have hB₀pair : (0 : ℂ) ≤ (R * B₀).trace :=
      Complex.nonneg_iff.mpr ⟨hB₀nonneg, hB₀im.symm⟩
    have htrace_nonneg : (0 : ℂ) ≤ (B.trace.re : ℂ) := by
      exact_mod_cast (Complex.nonneg_iff.mp hB.trace_nonneg).1
    rw [← trace_re_smul_normalizePosSemidef x₀ hB, Matrix.mul_smul, trace_smul,
      smul_eq_mul]
    exact mul_nonneg htrace_nonneg hB₀pair
  · apply PosSemidef.of_forall_trace_mul_nonneg hR.partialTransposeLeft
    intro B hB
    let B₀ := normalizePosSemidef x₀ B
    have hB₀ : B₀.PosSemidef := normalizePosSemidef_posSemidef x₀ hB
    have hB₀tr : B₀.trace = 1 := normalizePosSemidef_trace x₀ hB
    have hB₀mem :
        IsNormalizedDecomposableWitness (partialTransposeLeft B₀) := by
      refine ⟨0, B₀, B₀, by simp, hB₀, hB₀tr, hB₀, hB₀tr, ?_⟩
      simp
    have hB₀nonneg : 0 ≤ (partialTransposeLeft R * B₀).trace.re := by
      have h := hRnonneg (partialTransposeLeft B₀) hB₀mem
      rw [trace_partialTransposeLeft_mul_re, trace_mul_comm] at h
      exact h
    have hB₀im : (partialTransposeLeft R * B₀).trace.im = 0 := by
      have hreal : (partialTransposeLeft R * B₀).trace =
          star ((partialTransposeLeft R * B₀).trace) := by
        rw [← trace_conjTranspose, conjTranspose_mul, hB₀.isHermitian.eq,
          hR.partialTransposeLeft.eq, trace_mul_comm]
      have him := congrArg Complex.im hreal
      simp only [Complex.star_def, Complex.conj_im] at him
      linarith
    have hB₀pair : (0 : ℂ) ≤ (partialTransposeLeft R * B₀).trace :=
      Complex.nonneg_iff.mpr ⟨hB₀nonneg, hB₀im.symm⟩
    have htrace_nonneg : (0 : ℂ) ≤ (B.trace.re : ℂ) := by
      exact_mod_cast (Complex.nonneg_iff.mp hB.trace_nonneg).1
    rw [← trace_re_smul_normalizePosSemidef x₀ hB, Matrix.mul_smul, trace_smul,
      smul_eq_mul]
    exact mul_nonneg htrace_nonneg hB₀pair

end Matrix
