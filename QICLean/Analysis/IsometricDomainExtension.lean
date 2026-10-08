/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex (GPT-6).
-/
import QICLean.Analysis.RectangularTraceNormAlgebra
import QICLean.Algebra.DependentBlockDiagonal
import QICLean.Algebra.MatrixIsometryKronecker

/-!
# Extending rectangular maps to common private sectors

Extending a map `B` from an isometrically embedded domain by the adjoint
projection gives `B * Jᴴ`. It recovers the original action on the embedded
domain, is supported on its range projection, and preserves the exact L2
operator norm. The same embedding preserves actual Euclidean vector norms.

Canonical dependent direct-sum branch inclusions are reused from
`Matrix.sigmaBlockInclusion`. Their private dimensions may be arbitrary;
empty coordinate spaces require no exceptional normalization convention.

Source: common private slot spaces, *Polynomial PEPS approximation of gapped
square-grid ground states*, September 24, 2026, `04-compression.tex:250–268`.
These are original proofs; no upstream OpenAI Lean proof text is reused.
-/

open scoped Kronecker Matrix.Norms.L2Operator

namespace Matrix

noncomputable section

variable {m n p : Type*} [Fintype n]

/-- Extend a rectangular map by projecting onto an isometrically embedded
domain. The definition does not require the embedding to be isometric. -/

def isometricDomainExtension (B : Matrix m n ℂ) (J : Matrix p n ℂ) : Matrix m p ℂ :=
  B * Jᴴ

/-- The extended map agrees with the original map on the embedded domain. -/

theorem isometricDomainExtension_mul [Fintype p] [DecidableEq n]
    (B : Matrix m n ℂ) (J : Matrix p n ℂ) (hJ : Jᴴ * J = 1) :
    isometricDomainExtension B J * J = B := by
  rw [isometricDomainExtension, Matrix.mul_assoc, hJ, Matrix.mul_one]

/-- The extension is supported on the actual range projection of its domain
embedding. -/

theorem isometricDomainExtension_mul_rangeProjection [Fintype p] [DecidableEq n]
    (B : Matrix m n ℂ) (J : Matrix p n ℂ) (hJ : Jᴴ * J = 1) :
    isometricDomainExtension B J * (J * Jᴴ) = isometricDomainExtension B J := by
  rw [← Matrix.mul_assoc, isometricDomainExtension_mul B J hJ, isometricDomainExtension]

/-- Adjoint domain extension preserves the exact L2 operator norm, even
when the original domain or codomain is empty. -/

theorem norm_isometricDomainExtension [Fintype m] [Fintype p] [DecidableEq n] [DecidableEq p]
    (B : Matrix m n ℂ) (J : Matrix p n ℂ) (hJ : Jᴴ * J = 1) :
    ‖isometricDomainExtension B J‖ = ‖B‖ := by
  classical
  have hJn : ‖J‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self J hJ
  have hJhn : ‖Jᴴ‖ ≤ 1 := by simpa only [l2_opNorm_conjTranspose] using hJn
  apply le_antisymm
  · calc
      ‖isometricDomainExtension B J‖ ≤ ‖B‖ * ‖Jᴴ‖ := l2_opNorm_mul B Jᴴ
      _ ≤ ‖B‖ * 1 := mul_le_mul_of_nonneg_left hJhn (norm_nonneg B)
      _ = ‖B‖ := mul_one _
  · calc
      ‖B‖ = ‖isometricDomainExtension B J * J‖ :=
        congrArg norm (isometricDomainExtension_mul B J hJ).symm
      _ ≤ ‖isometricDomainExtension B J‖ * ‖J‖ := l2_opNorm_mul _ _
      _ ≤ ‖isometricDomainExtension B J‖ * 1 :=
        mul_le_mul_of_nonneg_left hJn (norm_nonneg _)
      _ = ‖isometricDomainExtension B J‖ := mul_one _

/-- A local contraction remains a contraction after extension to its common
private ambient sector. -/

theorem norm_isometricDomainExtension_le_one
    [Fintype m] [Fintype p] [DecidableEq n] [DecidableEq p]
    (B : Matrix m n ℂ) (J : Matrix p n ℂ) (hJ : Jᴴ * J = 1) (hB : ‖B‖ ≤ 1) :
    ‖isometricDomainExtension B J‖ ≤ 1 := by
  rwa [norm_isometricDomainExtension B J hJ]

/-- An actual column isometry preserves Euclidean vector norms, without a
nonzero-vector or nonempty-space premise. -/

theorem norm_toLp_mulVec_of_isometry [Fintype p] [DecidableEq n]
    (J : Matrix p n ℂ) (hJ : Jᴴ * J = 1) (ψ : EuclideanSpace ℂ n) :
    ‖WithLp.toLp 2 (J *ᵥ ψ.ofLp)‖ = ‖ψ‖ := by
  classical
  let v : EuclideanSpace ℂ p := WithLp.toLp 2 (J *ᵥ ψ.ofLp)
  have hJn : ‖J‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self J hJ
  have hJhn : ‖Jᴴ‖ ≤ 1 := by simpa only [l2_opNorm_conjTranspose] using hJn
  have hrecover : WithLp.toLp 2 (Jᴴ *ᵥ v.ofLp) = ψ := by
    change WithLp.toLp 2 (Jᴴ *ᵥ (J *ᵥ ψ.ofLp)) = ψ
    rw [mulVec_mulVec, hJ, one_mulVec, WithLp.toLp_ofLp]
  apply le_antisymm
  · calc
      ‖v‖ ≤ ‖J‖ * ‖ψ‖ := l2_opNorm_mulVec J ψ
      _ ≤ 1 * ‖ψ‖ := mul_le_mul_of_nonneg_right hJn (norm_nonneg ψ)
      _ = ‖ψ‖ := one_mul _
  · calc
      ‖ψ‖ = ‖WithLp.toLp 2 (Jᴴ *ᵥ v.ofLp)‖ := congrArg norm hrecover.symm
      _ ≤ ‖Jᴴ‖ * ‖v‖ := l2_opNorm_mulVec Jᴴ v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hJhn (norm_nonneg v)
      _ = ‖v‖ := one_mul _

section Branches

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (dim : ι → Type*) [∀ ξ, Fintype (dim ξ)] [∀ ξ, DecidableEq (dim ξ)]

/-- The canonical branch extension recovers its original rectangular map. -/

theorem isometricDomainExtension_sigmaBlockInclusion_mul (ξ : ι)
    (B : Matrix m (dim ξ) ℂ) :
    isometricDomainExtension B (sigmaBlockInclusion dim ξ) * sigmaBlockInclusion dim ξ = B :=
  isometricDomainExtension_mul B _ (sigmaBlockInclusion_isometry dim ξ)

/-- A branch extension vanishes on every other branch's source sector. -/

theorem isometricDomainExtension_sigmaBlockInclusion_mul_of_ne {ξ ζ : ι} (hξζ : ξ ≠ ζ)
    (B : Matrix m (dim ξ) ℂ) :
    isometricDomainExtension B (sigmaBlockInclusion dim ξ) * sigmaBlockInclusion dim ζ = 0 := by
  rw [isometricDomainExtension, Matrix.mul_assoc,
    sigmaBlockInclusion_conjTranspose_mul_of_ne dim hξζ, Matrix.mul_zero]

/-- Arbitrary finite private branch dimensions do not change the operator
norm of the map extended by the canonical sector projection. -/

theorem norm_isometricDomainExtension_sigmaBlockInclusion [Fintype m] (ξ : ι)
    (B : Matrix m (dim ξ) ℂ) :
    ‖isometricDomainExtension B (sigmaBlockInclusion dim ξ)‖ = ‖B‖ :=
  norm_isometricDomainExtension B _ (sigmaBlockInclusion_isometry dim ξ)

/-- Canonical common-sector insertion preserves the actual norm of a
branch vector, including zero and subnormalized vectors. -/

theorem norm_sigmaBlockInclusion_mulVec (ξ : ι) (ψ : EuclideanSpace ℂ (dim ξ)) :
    ‖WithLp.toLp 2 (sigmaBlockInclusion dim ξ *ᵥ ψ.ofLp)‖ = ‖ψ‖ :=
  norm_toLp_mulVec_of_isometry _ (sigmaBlockInclusion_isometry dim ξ) ψ

/-- Fixed external memory coordinates remain unchanged under private-sector
extension, with exact operator-norm preservation. -/

theorem norm_isometricDomainExtension_sigmaBlockInclusion_kronecker_one
    [Fintype m] {r : Type*} [Fintype r] [DecidableEq r] (ξ : ι)
    (B : Matrix m (dim ξ × r) ℂ) :
    ‖isometricDomainExtension B (sigmaBlockInclusion dim ξ ⊗ₖ (1 : Matrix r r ℂ))‖ = ‖B‖ :=
  norm_isometricDomainExtension B _
    (IsIsometry.kronecker (sigmaBlockInclusion dim ξ) (1 : Matrix r r ℂ)
      (sigmaBlockInclusion_isometry dim ξ) (by simp [IsIsometry]))

/-- Embedding both halves of an actual bipartite source into their common
branch sectors preserves its norm. In particular, normalized sources remain
normalized without bounds on the private dimensions. -/

theorem norm_sigmaBlockInclusion_kronecker_mulVec
    (dimR : ι → Type*) [∀ ξ, Fintype (dimR ξ)] [∀ ξ, DecidableEq (dimR ξ)]
    (ξ : ι) (ψ : EuclideanSpace ℂ (dim ξ × dimR ξ)) :
    ‖WithLp.toLp 2 ((sigmaBlockInclusion dim ξ ⊗ₖ sigmaBlockInclusion dimR ξ) *ᵥ ψ.ofLp)‖ =
      ‖ψ‖ :=
  norm_toLp_mulVec_of_isometry _
    (IsIsometry.kronecker (sigmaBlockInclusion dim ξ) (sigmaBlockInclusion dimR ξ)
      (sigmaBlockInclusion_isometry dim ξ)
      (sigmaBlockInclusion_isometry dimR ξ)) ψ

end Branches

end

end Matrix
