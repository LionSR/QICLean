/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.ComplexGaussian.ProductSourceTransport

/-!
# Rank-one expansion of source transport

Transporting an arbitrary rectangular source matrix through four endpoint frames
is the sum of its entries times the corresponding rank-one ambient matrices.
The endpoint frames need not be orthonormal or span their ambient spaces.
-/

noncomputable section
open scoped Matrix ComplexConjugate Kronecker
namespace QICLean.ComplexGaussian

/-- Expand an ambient source transport in the actual endpoint frame vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 294–338. -/
/-
Provenance-ID: p09-qic-source-transport-expansion
Downstream declaration: QICLean.ComplexGaussian.sourceTransport_eq_sum_rankOne
Source: September 24, 2026.
Label: eq:compression-random-source
Independently formalized; no upstream Lean proof text reused.
-/
theorem sourceTransport_eq_sum_rankOne {A C W X Y Z : Type}
    [Fintype A] [Fintype C]
    (E : Matrix W A ℂ) (F : Matrix X A ℂ)
    (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) (M : Matrix (A × A) (C × C) ℂ) :
    sourceTransport E F Et Ft M =
      ∑ z : (A × A) × (C × C), M z.1 z.2 •
        Matrix.vecMulVec (fun p ↦ E p.1 z.1.1 * F p.2 z.1.2)
          (fun q ↦ conj (Et q.1 z.2.1 * Ft q.2 z.2.2)) := by
  classical
  rw [Fintype.sum_prod_type, sourceTransport, Matrix.mul_assoc]
  ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.kroneckerMap_apply, starRingEnd_apply]
  ring

end QICLean.ComplexGaussian
