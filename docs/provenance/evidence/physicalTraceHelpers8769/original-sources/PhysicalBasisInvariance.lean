/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.RectangularTraceNormAlgebra
import QICLean.Channel.PartialTrace
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Physical trace norm in different orthonormal coordinates

Changing the physical and discarded orthonormal bases does not change the
trace norm of the reduced operator. The statement applies to arbitrary finite
linear combinations of mixed vector outer products, with no positivity
assumption. Thus the affected-region coordinates may be chosen separately
for each corrected source set while estimating the same physical operator.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–549.
-/

noncomputable section
open scoped TensorProduct Matrix Kronecker ComplexConjugate

namespace Matrix

open Classical in
/-- Isometric changes of physical and discarded coordinates preserve the
trace norm after the discarded factor is traced out. -/
theorem rectangularTraceNorm_partialTraceRight_isometries
    {X Y d e : Type} [Fintype X] [Fintype Y] [Fintype d] [Fintype e]
    (U : Matrix Y X ℂ) (V : Matrix e d ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (M : Matrix (X × d) (X × d) ℂ) :
    rectangularTraceNorm (partialTraceRight ((U ⊗ₖ V) * M * (U ⊗ₖ V)ᴴ)) =
      rectangularTraceNorm (partialTraceRight M) := by
  rw [partialTraceRight_kronecker_conj_of_right_isometry U V hV]
  exact rectangularTraceNorm_isometry_sandwich _ U U hU hU

end Matrix

namespace OrthonormalBasis

variable {E F X Y d e : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [Fintype X] [Fintype Y] [Fintype d] [Fintype e]
    (bX : OrthonormalBasis X ℂ E) (bY : OrthonormalBasis Y ℂ E)
    (bd : OrthonormalBasis d ℂ F) (be : OrthonormalBasis e ℂ F)

/-- The change between product orthonormal bases is the Kronecker product of
the two actual changes of endpoint coordinates. -/
theorem tensorProduct_basisChange :
    (bY.tensorProduct be).toBasis.toMatrix (bX.tensorProduct bd) =
      bY.toBasis.toMatrix bX ⊗ₖ be.toBasis.toMatrix bd := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.tensorProduct_apply, OrthonormalBasis.tensorProduct_repr_tmul_apply,
    Matrix.kroneckerMap_apply]
  ring

/-- Mixed vector densities transform by the actual product change of coordinates. -/
theorem tensorProduct_rankOne_basisChange (z t : E ⊗[ℂ] F) :
    let K := bY.toBasis.toMatrix bX ⊗ₖ be.toBasis.toMatrix bd
    K * Matrix.vecMulVec ((bX.tensorProduct bd).repr z).ofLp
        (fun j ↦ conj ((bX.tensorProduct bd).repr t j)) * Kᴴ =
      Matrix.vecMulVec ((bY.tensorProduct be).repr z).ofLp
        (fun j ↦ conj ((bY.tensorProduct be).repr t j)) := by
  classical
  intro K
  have hK (u : E ⊗[ℂ] F) : K *ᵥ ((bX.tensorProduct bd).repr u).ofLp =
      ((bY.tensorProduct be).repr u).ofLp := by
    rw [show K = (bY.tensorProduct be).toBasis.toMatrix (bX.tensorProduct bd) from
      (tensorProduct_basisChange bX bY bd be).symm]
    exact (bX.tensorProduct bd).toBasis.toMatrix_mulVec_repr
      (bY.tensorProduct be).toBasis u
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hK]
  change Matrix.vecMulVec _ (star ((bX.tensorProduct bd).repr t).ofLp ᵥ* Kᴴ) = _
  rw [← Matrix.star_mulVec, hK]
  rfl

open Classical in
/-- The physical trace norm of a finite mixed-vector operator is independent
of both its physical and its discarded orthonormal bases. -/
theorem rectangularTraceNorm_partialTrace_sum_rankOne_basis_eq
    {I : Type} [Fintype I] (c : I → ℂ) (z t : I → E ⊗[ℂ] F) :
    Matrix.rectangularTraceNorm (Matrix.partialTraceRight
      (∑ i, c i • Matrix.vecMulVec ((bY.tensorProduct be).repr (z i)).ofLp
        (fun j ↦ conj ((bY.tensorProduct be).repr (t i) j)))) =
      Matrix.rectangularTraceNorm (Matrix.partialTraceRight
        (∑ i, c i • Matrix.vecMulVec ((bX.tensorProduct bd).repr (z i)).ofLp
          (fun j ↦ conj ((bX.tensorProduct bd).repr (t i) j)))) := by
  let U := bY.toBasis.toMatrix bX
  let V := be.toBasis.toMatrix bd
  have h := Matrix.rectangularTraceNorm_partialTraceRight_isometries U V
    (bY.toMatrix_orthonormalBasis_conjTranspose_mul_self bX)
    (be.toMatrix_orthonormalBasis_conjTranspose_mul_self bd)
    (∑ i, c i • Matrix.vecMulVec ((bX.tensorProduct bd).repr (z i)).ofLp
      (fun j ↦ conj ((bX.tensorProduct bd).repr (t i) j)))
  simpa only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    U, V, tensorProduct_rankOne_basisChange] using h

end OrthonormalBasis
