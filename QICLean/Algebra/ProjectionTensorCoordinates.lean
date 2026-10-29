/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.ProjectionRangeIsometry
import QICLean.Algebra.MatrixIsometryKronecker

/-!
# Tensor coordinates for a projection contained in two retained factors

Let `P`, `Q` and `R` be orthogonal projections on the finite coordinate spaces
`α × β`, `α` and `β`, with `(Q ⊗ₖ R) * P = P`. Choose isometric coordinates
`U`, `V`, `W` for their ranges. The parent coefficients in the two child
coordinates are `C = (V ⊗ₖ W)ᴴ * U`. This coefficient matrix is an isometry,
and `U = (V ⊗ₖ W) * C`. Its source dimension is at most the product of the
two child dimensions. Zero projections and empty coordinate types are allowed.

This is an auxiliary coordinate construction for the retained-basis expansion
in Hastings, arXiv:cond-mat/0508554v3, Section III, lines 630–685 of
`proj3new.tex`. It is independent of a Hamiltonian or a choice of ground vector.
The source explicitly leaves quantitative intermediate dimension bounds open
at lines 104–109. The product dimension inequality here is purely algebraic.
-/

open Matrix
open scoped Kronecker ComplexOrder

/-- Isometric columns fixed by `A * Aᴴ` have isometric coordinates under `Aᴴ`,
and applying `A` recovers those columns. Auxiliary to the retained-basis
expansion in Hastings, arXiv:cond-mat/0508554v3, Section III, lines 630–685. -/
theorem Matrix.IsIsometry.conjTranspose_mul_of_range_eq
    {m n p : Type*} [Fintype m] [Fintype n] [DecidableEq p]
    {U : Matrix m p ℂ} (hU : U.IsIsometry) (A : Matrix m n ℂ)
    (hAU : A * Aᴴ * U = U) :
    (Aᴴ * U).IsIsometry ∧ U = A * (Aᴴ * U) := by
  refine ⟨?_, hAU.symm.trans (Matrix.mul_assoc A Aᴴ U)⟩
  simpa only [Matrix.IsIsometry, conjTranspose_mul,
    conjTranspose_conjTranspose, Matrix.mul_assoc] using
      (congrArg (fun X : Matrix m p ℂ ↦ Uᴴ * X) hAU).trans hU

/-- Choose actual range coordinates for three projections with the parent range
contained in the tensor product of the child ranges. The coefficient matrix is
the displayed adjoint product, rather than a supplied factorization.

Auxiliary to Hastings, arXiv:cond-mat/0508554v3, Section III, lines 630–685.
No nonzero-rank or nonempty-coordinate assumption is imposed. -/
theorem IsStarProjection.exists_tensor_range_isometries
    {α β : Type*} [Fintype α] [Fintype β]
    {P : Matrix (α × β) (α × β) ℂ} {Q : Matrix α α ℂ} {R : Matrix β β ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hR : IsStarProjection R)
    (hcontain : (Q ⊗ₖ R) * P = P) :
    ∃ (rP rQ rR : ℕ)
      (U : Matrix (α × β) (Fin rP) ℂ)
      (V : Matrix α (Fin rQ) ℂ)
      (W : Matrix β (Fin rR) ℂ),
      U.IsIsometry ∧ U * Uᴴ = P ∧
      V.IsIsometry ∧ V * Vᴴ = Q ∧
      W.IsIsometry ∧ W * Wᴴ = R ∧
      rP = P.rank ∧ rQ = Q.rank ∧ rR = R.rank ∧
      let A := V ⊗ₖ W
      let C := Aᴴ * U
      C.IsIsometry ∧ U = A * C ∧ rP ≤ rQ * rR := by
  classical
  obtain ⟨⟨rP, U, hU, hUP⟩, ⟨rQ, V, hV, hVQ⟩, ⟨rR, W, hW, hWR⟩⟩ :=
    And.intro hP.exists_matrix_range_isometry
      (And.intro hQ.exists_matrix_range_isometry hR.exists_matrix_range_isometry)
  refine ⟨rP, rQ, rR, U, V, W, hU, hUP, hV, hVQ, hW, hWR, ?_, ?_, ?_, ?_⟩
  case refine_4 =>
    let A := V ⊗ₖ W
    have hAA : A * Aᴴ = Q ⊗ₖ R := by
      simp only [A, conjTranspose_kronecker, ← mul_kronecker_mul, hVQ, hWR]
    have hPU : P * U = U := by
      rw [← hUP, Matrix.mul_assoc, hU, Matrix.mul_one]
    have hAU : A * Aᴴ * U = U := by
      rw [hAA, ← hPU, ← Matrix.mul_assoc, hcontain, hPU]
    obtain ⟨hC, hfactor⟩ := Matrix.IsIsometry.conjTranspose_mul_of_range_eq hU A hAU
    refine ⟨hC, hfactor, ?_⟩
    simpa only [Fintype.card_fin, Fintype.card_prod] using
      Matrix.IsIsometry.card_le (Aᴴ * U) hC
  case refine_1 =>
    rw [← hUP, Matrix.rank_self_mul_conjTranspose,
      Matrix.IsIsometry.rank_eq_card U hU, Fintype.card_fin]
  case refine_2 =>
    rw [← hVQ, Matrix.rank_self_mul_conjTranspose,
      Matrix.IsIsometry.rank_eq_card V hV, Fintype.card_fin]
  case refine_3 =>
    rw [← hWR, Matrix.rank_self_mul_conjTranspose,
      Matrix.IsIsometry.rank_eq_card W hW, Fintype.card_fin]
