/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex (GPT-6).
-/
import QICLean.Analysis.Isometry.FramePerturbation
import QICLean.Algebra.Matrix.DependentBlockDiagonal
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import QICLean.Algebra.Hermitian.MatrixSandwichIntertwine
import QICLean.Algebra.Combinatorics.FinsetEnumeration

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

It also contains the following results.

* `Matrix.norm_projected_le_of_isometric_intertwine`: a norm comparison through an orthogonal
  projection.

Moved from TNLean, `TNLean/MPS/Preparation/Polar/IsometricExtension.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

section IsometricDomainExtension

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
  have hJn : ‖J‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hJ
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
  have hJn : ‖J‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hJ
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

end IsometricDomainExtension

section ProjectionIntertwiningNorm

/-!
## A norm comparison through an orthogonal projection

Let Z be a rectangular isometry, let A and N be Hermitian matrices, and let
P be an orthogonal projection. If (Z A Zᴴ) P = P N, taking adjoints reverses
the intertwining. Contractivity of P and norm preservation by Z then compare
the action of N on P u with the action of A on Zᴴ u.

Neither A nor N needs to be positive. The coordinate sets may be empty.
For the application to real powers of restricted replica metrics, A and N
are the corresponding positive matrix powers, and P is the actual symmetric
projection after insertion of a unit Bell vector.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 283–308 and 370–381,
  `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A Hermitian intertwining through an orthogonal projection and a rectangular
isometry gives a norm comparison. This is the finite-dimensional norm step for
the restricted powers in the area-law manuscript, `07-comparators.tex`,
lines 283–308 and 370–381. -/
theorem norm_projected_le_of_isometric_intertwine
    {A : Matrix n n ℂ} {N P : Matrix m m ℂ} {Z : Matrix m n ℂ}
    (hA : A.IsHermitian) (hN : N.IsHermitian) (hP : IsStarProjection P)
    (hZ : Zᴴ * Z = 1) (h : (Z * A * Zᴴ) * P = P * N)
    (u : EuclideanSpace ℂ m) :
    ‖toEuclideanLin N (toEuclideanLin P u)‖ ≤
      ‖toEuclideanLin A (toEuclideanLin Zᴴ u)‖ := by
  have hZnorm : ∀ v : EuclideanSpace ℂ n, ‖toEuclideanLin Z v‖ = ‖v‖ :=
    norm_toLp_mulVec_of_isometry Z hZ
  have hPadj : Pᴴ = P := hP.isSelfAdjoint.isHermitian.eq
  have hreverse : N * P = P * (Z * A * Zᴴ) := by
    simpa only [hPadj] using
      (Matrix.isHermitian_mul_mul_conjTranspose Z hA).conjTranspose_intertwine hN P h
  calc
    ‖toEuclideanLin N (toEuclideanLin P u)‖ =
        ‖toEuclideanLin (N * P) u‖ := by
      simp only [toLpLin_mul_same, LinearMap.comp_apply]
    _ = ‖toEuclideanLin P
        (toEuclideanLin Z (toEuclideanLin A (toEuclideanLin Zᴴ u)))‖ := by
      rw [hreverse]
      simp only [toLpLin_mul_same, LinearMap.comp_apply]
    _ ≤ ‖P‖ * ‖toEuclideanLin Z (toEuclideanLin A (toEuclideanLin Zᴴ u))‖ :=
      P.l2_opNorm_mulVec _
    _ ≤ 1 * ‖toEuclideanLin Z (toEuclideanLin A (toEuclideanLin Zᴴ u))‖ :=
      mul_le_mul_of_nonneg_right (IsStarProjection.norm_le P hP) (norm_nonneg _)
    _ = ‖toEuclideanLin A (toEuclideanLin Zᴴ u)‖ := by
      rw [one_mul, hZnorm]

end Matrix

end ProjectionIntertwiningNorm

section

open Matrix


open scoped BigOperators ComplexOrder



namespace Matrix

/-- **An orthonormal basis adapted to an orthogonal projector.** For a Hermitian idempotent `E`
on `ℂ^m` there are `r ≤ m` and a unitary `T` whose first `r` columns span the range of `E` and
whose other columns span its kernel: `E T = T diag(1, …, 1, 0, …, 0)`. -/
theorem exists_unitary_mul_diagonal_of_isHermitian {m : ℕ} {E : Matrix (Fin m) (Fin m) ℂ}
    (hE : E.IsHermitian) (hEE : E * E = E) :
    ∃ (r : ℕ) (T : Matrix (Fin m) (Fin m) ℂ), r ≤ m ∧ T ∈ unitary (Matrix (Fin m) (Fin m) ℂ) ∧
      E * T = T * diagonal fun y => if y.val < r then 1 else 0 := by
  classical
  set U : Matrix (Fin m) (Fin m) ℂ := ↑hE.eigenvectorUnitary with hUdef
  set μ : Fin m → ℂ := fun j => (hE.eigenvalues j : ℂ) with hμ
  have hU : U ∈ unitary (Matrix (Fin m) (Fin m) ℂ) := hE.eigenvectorUnitary.2
  have hEU : E * U = U * diagonal μ := by
    ext i j
    have h := congrFun (hE.mulVec_eigenvectorBasis j) i
    simp only [mulVec, dotProduct, Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_eq_mul] at h
    rw [mul_diagonal, mul_apply]
    simpa [U, μ, mul_comm] using h
  have hμμ : ∀ j, μ j = 0 ∨ μ j = 1 := fun j => by
    have h : U * (diagonal μ * diagonal μ) = U * diagonal μ := by
      rw [← Matrix.mul_assoc, ← hEU, Matrix.mul_assoc, ← hEU, ← Matrix.mul_assoc, hEE]
    have h' := congrArg (star U * ·) h
    simp only [← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU, Matrix.one_mul,
      diagonal_mul_diagonal] at h'
    have := congrFun (congrFun h' j) j
    simp only [diagonal_apply_eq] at this
    rcases mul_eq_zero.mp (show μ j * (μ j - 1) = 0 by rw [mul_sub, this]; ring) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (sub_eq_zero.mp h1)
  set S : Finset (Fin m) := Finset.univ.filter fun j => μ j = 1
  obtain ⟨π, hπ⟩ := Finset.exists_equiv_val_lt_card_iff_mem S
  set ρ : Fin m ≃ Fin m := (finCongr (Fintype.card_fin m).symm).trans π with hρ
  have hρS : ∀ y, ρ y ∈ S ↔ y.val < S.card := fun y => (hπ (finCongr _ y)).symm
  refine ⟨S.card, U.submatrix id ρ, ?_, ?_, ?_⟩
  · simpa using S.card_le_univ
  · refine (Matrix.mem_unitaryGroup_iff' (α := ℂ)).mpr ?_
    calc star (U.submatrix id ρ) * U.submatrix id ρ = (star U * U).submatrix ρ ρ := by
          ext; simp [mul_apply, star_eq_conjTranspose]
      _ = 1 := by rw [Unitary.star_mul_self_of_mem hU, submatrix_one_equiv]
  · ext i y
    have h := congrFun (congrFun hEU i) (ρ y)
    rw [mul_apply, mul_diagonal] at h ⊢
    simp only [submatrix_apply, id] at h ⊢
    rw [h]
    congr 1
    rcases hμμ (ρ y) with h0 | h1
    · have : ¬ y.val < S.card := fun hy => by
        have := (hρS y).mpr hy
        simp [S, h0] at this
      rw [h0, ite_eq_right this]
    · rw [h1, ite_eq_left ((hρS y).mp (by simp [S, h1]))]

end Matrix

end
