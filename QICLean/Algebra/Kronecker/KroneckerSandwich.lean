/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex (GPT-6).
These constructions and proofs are independently written from the manuscript
and Mathlib; no upstream OpenAI Lean proof text is reused in this file.
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# A matrix between two Kronecker products

For matrices `E : W × A`, `F : X × A`, `Et : Y × C`, `Ft : Z × C` and a matrix `M` on
`(A × A) × (C × C)`, the product `(E ⊗ F) M (Et ⊗ Ft)ᴴ` is a matrix on `(W × X) × (Y × Z)`.
It maps Kronecker products to Kronecker products, and it is the sum of the entries of `M`
times the rank-one matrices of the columns of the four matrices. The four matrices need not
have orthonormal columns or span their row spaces.

## Main definitions

* `Matrix.kroneckerSandwich`: the matrix `(E ⊗ F) M (Et ⊗ Ft)ᴴ`.

## Main results

* `Matrix.kroneckerSandwich_kronecker`: the image of a Kronecker product.
* `Matrix.kroneckerSandwich_eq_sum_vecMulVec`: the expansion in rank-one matrices.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Theorem 5.2, `eq:compression-random-source`, `04-compression.tex`,
  lines 294–338.

Moved from TNLean, `TNLean/MPS/MPU/QuasiLocal/AnchoredThreeBlockOperator.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

open scoped BigOperators ComplexConjugate Kronecker

namespace Matrix

noncomputable section

variable {A C W X Y Z : Type*} [Fintype A] [Fintype C]

/-- The matrix `(E ⊗ F) M (Et ⊗ Ft)ᴴ`: a matrix `M` on `(A × A) × (C × C)` read in the columns
of `E`, `F` on the left and of `Et`, `Ft` on the right.
Source: `eq:compression-random-source`, `04-compression.tex:294–309`. -/
def kroneckerSandwich (E : Matrix W A ℂ) (F : Matrix X A ℂ)
    (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (M : Matrix (A × A) (C × C) ℂ) : Matrix (W × X) (Y × Z) ℂ :=
  (E ⊗ₖ F) * M * (Et ⊗ₖ Ft).conjTranspose

/-- The image of a Kronecker product `U ⊗ V` is the Kronecker product of the two images
`E U Etᴴ` and `F V Ftᴴ`. Source: `eq:compression-random-source`,
`04-compression.tex:294–300`. -/
theorem kroneckerSandwich_kronecker (E : Matrix W A ℂ) (F : Matrix X A ℂ)
    (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) (U V : Matrix A C ℂ) :
    kroneckerSandwich E F Et Ft (U ⊗ₖ V) =
      (E * U * Et.conjTranspose) ⊗ₖ (F * V * Ft.conjTranspose) := by
  simp only [kroneckerSandwich, Matrix.mul_kronecker_mul, Matrix.conjTranspose_kronecker]

/-- The matrix `(E ⊗ F) M (Et ⊗ Ft)ᴴ` is the sum over the entries of `M` of the entry times the
rank-one matrix of the corresponding columns.
Source: Theorem 5.2, `04-compression.tex`, lines 294–338. -/
theorem kroneckerSandwich_eq_sum_vecMulVec (E : Matrix W A ℂ) (F : Matrix X A ℂ)
    (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) (M : Matrix (A × A) (C × C) ℂ) :
    kroneckerSandwich E F Et Ft M =
      ∑ z : (A × A) × (C × C), M z.1 z.2 •
        Matrix.vecMulVec (fun p ↦ E p.1 z.1.1 * F p.2 z.1.2)
          (fun q ↦ conj (Et q.1 z.2.1 * Ft q.2 z.2.2)) := by
  classical
  rw [Fintype.sum_prod_type, kroneckerSandwich, Matrix.mul_assoc]
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

end

end Matrix

section

open scoped Matrix

namespace Matrix

/-- If every fixed-exterior slice intertwines an input and output operator,
then the full matrix intertwines their tensor products with the identities
on the exterior factors. -/
theorem intertwiner_of_slices
    {E F X J : Type*}
    [Fintype E] [Fintype F] [Fintype X] [Fintype J]
    [DecidableEq E] [DecidableEq F]
    (U : Matrix (E × X) (F × J) ℂ)
    (A : Matrix J J ℂ) (B : Matrix X X ℂ)
    (h : ∀ e f, (show Matrix X J ℂ from fun x j => U (e, x) (f, j)) * A =
      B * (show Matrix X J ℂ from fun x j => U (e, x) (f, j))) :
    U * Matrix.kronecker (1 : Matrix F F ℂ) A =
      Matrix.kronecker (1 : Matrix E E ℂ) B * U := by
  ext ⟨e, x⟩ ⟨f, j⟩
  have hs := congrArg (fun M : Matrix X J ℂ => M x j) (h e f)
  change (∑ t : J, U (e, x) (f, t) * A t j) =
    ∑ t : X, B x t * U (e, t) (f, j) at hs
  simpa [Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite] using hs

end Matrix

end
