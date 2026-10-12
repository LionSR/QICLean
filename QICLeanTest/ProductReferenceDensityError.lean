/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProductReferenceDensityError

/-! Regressions for the actual private norm, finite coordinate changes, and
absolute product-reference density error. -/

open scoped Matrix

noncomputable section

-- Independent rectangular coordinate changes need no Hermiticity premise.
example (A : Matrix (Fin 2) (Fin 3) ℂ) (e : Fin 2 ≃ Fin 2) (f : Fin 3 ≃ Fin 3) :
    Matrix.rectangularTraceNorm (Matrix.reindex e f A) = Matrix.rectangularTraceNorm A := by
  exact Matrix.rectangularTraceNorm_reindex e f A

-- Empty row and column spaces remain admissible in the coordinate theorem.
example (A : Matrix (Fin 0) (Fin 3) ℂ) (f : Fin 3 ≃ Fin 3) :
    Matrix.rectangularTraceNorm (Matrix.reindex (Equiv.refl _) f A) =
      Matrix.rectangularTraceNorm A := by
  exact Matrix.rectangularTraceNorm_reindex _ _ _

example (A : Matrix (Fin 2) (Fin 0) ℂ) (e : Fin 2 ≃ Fin 2) :
    Matrix.rectangularTraceNorm (Matrix.reindex e (Equiv.refl _) A) =
      Matrix.rectangularTraceNorm A := by
  exact Matrix.rectangularTraceNorm_reindex _ _ _

-- The Fin trace norm used by the column theorem is literally this same norm.
example {a : Type*} [Fintype a] [DecidableEq a] {n : ℕ} (e : a ≃ Fin n)
    (A : Matrix a a ℂ) :
    Matrix.traceNorm (Matrix.reindex e e A) = Matrix.rectangularTraceNorm A := by
  simpa only [Matrix.rectangularTraceNorm_square] using
    Matrix.rectangularTraceNorm_reindex e e A

-- Empty physical coordinates are allowed by the exact product marginal identity.
example (Ω : EuclideanSpace ℂ (Fin 0)) (Ξ : EuclideanSpace ℂ (Fin 3)) :
    Matrix.partialTraceRight (Matrix.euclideanOuterProduct
      (Matrix.euclideanTensorVector Ω Ξ) (Matrix.euclideanTensorVector Ω Ξ)) =
        (‖Ξ‖ : ℂ) ^ 2 • Matrix.euclideanOuterProduct Ω Ω := by
  exact Matrix.partialTraceRight_tensorVector_eq_smul Ω Ξ

-- A zero private vector contributes full lost mass, without a division by zero.
example (Ω : EuclideanSpace ℂ (Fin 2)) (hΩ : ‖Ω‖ = 1) :
    Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
        (Matrix.euclideanTensorVector Ω (0 : EuclideanSpace ℂ (Fin 3)))
        (Matrix.euclideanTensorVector Ω (0 : EuclideanSpace ℂ (Fin 3)))) -
        Matrix.euclideanOuterProduct Ω Ω) ≤ 1 := by
  simpa using Matrix.rectangularTraceNorm_product_reference_sub_le Ω
    (0 : EuclideanSpace ℂ (Fin 3)) hΩ (by simp)

-- Half-norm private mass has squared-norm loss 3/4, even with a complex physical phase.
example : Matrix.rectangularTraceNorm
    (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
      (Matrix.euclideanTensorVector
        (EuclideanSpace.single (0 : Fin 2) Complex.I)
        (EuclideanSpace.single (0 : Fin 3) (1 / 2 : ℂ)))
      (Matrix.euclideanTensorVector
        (EuclideanSpace.single (0 : Fin 2) Complex.I)
        (EuclideanSpace.single (0 : Fin 3) (1 / 2 : ℂ)))) -
      Matrix.euclideanOuterProduct
        (EuclideanSpace.single (0 : Fin 2) Complex.I)
        (EuclideanSpace.single (0 : Fin 2) Complex.I)) ≤ 3 / 4 := by
  have h := Matrix.rectangularTraceNorm_product_reference_sub_le
    (EuclideanSpace.single (0 : Fin 2) Complex.I)
    (EuclideanSpace.single (0 : Fin 3) (1 / 2 : ℂ)) (by simp) (by norm_num)
  norm_num at h ⊢
  exact h

-- An empty private coordinate space is zero-dimensional, rather than a unit register.
example (Ω : EuclideanSpace ℂ (Fin 2)) (hΩ : ‖Ω‖ = 1) :
    Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
        (0 : EuclideanSpace ℂ (Fin 2 × Fin 0)) 0) -
        Matrix.euclideanOuterProduct Ω Ω) ≤ 1 := by
  have hzero : Matrix.euclideanTensorVector Ω (0 : EuclideanSpace ℂ (Fin 0)) = 0 := by
    ext ⟨i, j⟩
    exact Fin.elim0 j
  simpa only [hzero, sub_self, norm_zero, mul_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, zero_add] using
    Matrix.rectangularTraceNorm_partialTraceRight_sub_product_reference_le
      (0 : EuclideanSpace ℂ (Fin 2 × Fin 0)) Ω 0 (by simp) hΩ (by simp)

-- No delta <= 1 assumption: delta = 2 is an admissible, deliberately loose budget.
example (Ω : EuclideanSpace ℂ (Fin 2)) (hΩ : ‖Ω‖ = 1) :
    Matrix.rectangularTraceNorm
      (Matrix.partialTraceRight (Matrix.euclideanOuterProduct
        (0 : EuclideanSpace ℂ (Fin 2 × Fin 3)) 0) -
        Matrix.euclideanOuterProduct Ω Ω) ≤ 4 := by
  have hzero : Matrix.euclideanTensorVector Ω (0 : EuclideanSpace ℂ (Fin 3)) = 0 := by
    ext ⟨i, j⟩
    simp
  have h := Matrix.rectangularTraceNorm_partialTraceRight_sub_product_reference_le_of_norm_sub_le
    (0 : EuclideanSpace ℂ (Fin 2 × Fin 3)) Ω 0 (by simp) hΩ (by simp)
    (ε := 0) (δ := 2) (by simp [hzero]) (by simp)
  norm_num at h ⊢
  exact h

-- The trace deficit estimate does not assume the actual vector is contractive.
example (Ψ : EuclideanSpace ℂ (Fin 2 × Fin 3)) (Ω : EuclideanSpace ℂ (Fin 2))
    (Ξ : EuclideanSpace ℂ (Fin 3)) (hΩ : ‖Ω‖ = 1) {ε δ : ℝ}
    (herror : ‖Ψ - Matrix.euclideanTensorVector Ω Ξ‖ ≤ ε) (hlower : 1 - δ ≤ ‖Ξ‖) :
    1 - (Matrix.partialTraceRight (Matrix.euclideanOuterProduct Ψ Ψ)).trace.re ≤
      2 * (δ + ε) := by
  exact Matrix.trace_deficit_partialTraceRight_le_of_product_reference Ψ Ω Ξ hΩ herror hlower

-- The compressed operator is arbitrary and need not be positive or Hermitian.
example (σ : Matrix (Fin 2) (Fin 2) ℂ) (Ψ : EuclideanSpace ℂ (Fin 2 × Fin 3))
    (Ω : EuclideanSpace ℂ (Fin 2)) (Ξ : EuclideanSpace ℂ (Fin 3))
    (hΨ : ‖Ψ‖ ≤ 1) (hΩ : ‖Ω‖ = 1) (hΞ : ‖Ξ‖ ≤ 1) {ε δ κ : ℝ}
    (herror : ‖Ψ - Matrix.euclideanTensorVector Ω Ξ‖ ≤ ε) (hlower : 1 - δ ≤ ‖Ξ‖)
    (hcompression : Matrix.traceNorm
      (σ - Matrix.partialTraceRight (Matrix.euclideanOuterProduct Ψ Ψ)) ≤ κ) :
    Matrix.traceNorm (σ - Matrix.euclideanOuterProduct Ω Ω) ≤ κ + 2 * ε + 2 * δ := by
  exact Matrix.rectangularTraceNorm_sub_pure_le_of_product_reference
    σ Ψ Ω Ξ hΨ hΩ hΞ herror hlower hcompression
