/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Star.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module

/-!
# Exchanging two invariant orthogonal unit vectors

For orthogonal unit vectors `x` and `y`, the matrix `1 - (x - y)(x - y)†` exchanges `x` and `y`,
is unitary, and fixes the vectors orthogonal to both. Every unitary fixing `x` and `y` commutes
with this exchange. Thus two invariant unit vectors can be exchanged without altering the
symmetry. This is the finite-dimensional operation used in Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Theorem 6.17 and equation `eq:anyons:make-chargeless-fluxon`, lines 2320–2340.

Moved from TNLean, `TNLean/Algebra/UnitaryVectorSwap.lean` at commit `49b78ed821`
(Apache-2.0).

## Main definitions

* `Matrix.unitaryVectorSwap`

## Main results

* `Matrix.unitaryVectorSwap_mem_unitaryGroup`
* `Matrix.unitaryVectorSwap_mulVec_left`, `Matrix.unitaryVectorSwap_mulVec_right`
* `Matrix.unitaryVectorSwap_commute`

Moved from TNLean, `TNLean/MPS/MPU/Circuit/Merging/OrthogonalIsometrySwap.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

noncomputable section
open scoped Matrix
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The reflection in the difference of two vectors; for orthogonal unit vectors
it exchanges them and fixes their orthogonal complement. -/
def unitaryVectorSwap (x y : ι → ℂ) : Matrix ι ι ℂ :=
  1 - vecMulVec (x - y) (star (x - y))

omit [DecidableEq ι] in
private theorem diff_dotProduct (x y : ι → ℂ)
    (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1)
    (hxy : star x ⬝ᵥ y = 0) : star (x - y) ⬝ᵥ (x - y) = 2 := by
  have hyx : star y ⬝ᵥ x = 0 := by rw [star_dotProduct, hxy, star_zero]
  simp only [star_sub, sub_dotProduct, dotProduct_sub, hx, hy, hxy, hyx]
  norm_num

/-- The reflection in the difference of two orthogonal unit vectors is unitary. -/
theorem unitaryVectorSwap_mem_unitaryGroup (x y : ι → ℂ)
    (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1)
    (hxy : star x ⬝ᵥ y = 0) : unitaryVectorSwap x y ∈ unitaryGroup ι ℂ := by
  let P := vecMulVec (x - y) (star (x - y))
  have hP : P * P = P + P := by
    dsimp only [P]
    rw [vecMulVec_mul_vecMulVec, diff_dotProduct x y hx hy hxy, two_smul]
    exact vecMulVec_add _ _ _
  have hstar : star P = P := by
    simp only [P, star_eq_conjTranspose, conjTranspose_vecMulVec, star_star]
  rw [mem_unitaryGroup_iff]
  change (1 - P) * star (1 - P) = 1
  simp only [star_sub, star_one, hstar, sub_mul, mul_sub, one_mul, mul_one, hP]
  abel

/-- The reflection carries the first orthogonal unit vector to the second. -/
theorem unitaryVectorSwap_mulVec_left (x y : ι → ℂ)
    (hx : star x ⬝ᵥ x = 1) (hxy : star x ⬝ᵥ y = 0) :
    unitaryVectorSwap x y *ᵥ x = y := by
  have hyx : star y ⬝ᵥ x = 0 := by rw [star_dotProduct, hxy, star_zero]
  simp only [unitaryVectorSwap, sub_mulVec, one_mulVec, vecMulVec_mulVec,
    star_sub, sub_dotProduct, hx, hyx, sub_zero, MulOpposite.op_one, one_smul]
  abel

/-- The reflection carries the second orthogonal unit vector to the first. -/
theorem unitaryVectorSwap_mulVec_right (x y : ι → ℂ)
    (hy : star y ⬝ᵥ y = 1) (hxy : star x ⬝ᵥ y = 0) :
    unitaryVectorSwap x y *ᵥ y = x := by
  simp only [unitaryVectorSwap, sub_mulVec, one_mulVec, vecMulVec_mulVec,
    star_sub, sub_dotProduct, hxy, hy, zero_sub]
  simp only [MulOpposite.op_neg, MulOpposite.op_one, neg_one_smul]
  abel

/-- Every unitary fixing both vectors commutes with their exchange. -/
theorem unitaryVectorSwap_commute (x y : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hx : U *ᵥ x = x) (hy : U *ᵥ y = y) :
    Commute (unitaryVectorSwap x y) U := by
  have hv : U *ᵥ (x - y) = x - y := by rw [mulVec_sub, hx, hy]
  have hstarU : Uᴴ *ᵥ (x - y) = x - y := by
    calc
      _ = Uᴴ *ᵥ (U *ᵥ (x - y)) := by rw [hv]
      _ = _ := by
        rw [mulVec_mulVec, ← star_eq_conjTranspose, mem_unitaryGroup_iff'.mp hU, one_mulVec]
  have hrow : star (x - y) ᵥ* U = star (x - y) := by
    have h := congrArg star hstarU
    simpa only [star_mulVec, conjTranspose_conjTranspose] using h
  change (1 - vecMulVec (x - y) (star (x - y))) * U =
    U * (1 - vecMulVec (x - y) (star (x - y)))
  rw [sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul, mul_vecMulVec, hv, hrow]

/-- The reflection fixes vectors orthogonal to both exchanged vectors. -/
theorem unitaryVectorSwap_mulVec_of_orthogonal (x y z : ι → ℂ)
    (hx : star x ⬝ᵥ z = 0) (hy : star y ⬝ᵥ z = 0) :
    unitaryVectorSwap x y *ᵥ z = z := by
  simp only [unitaryVectorSwap, sub_mulVec, one_mulVec, vecMulVec_mulVec,
    star_sub, sub_dotProduct, hx, hy, sub_self, MulOpposite.op_zero, zero_smul, sub_zero]
end Matrix

section

open scoped Matrix

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [DecidableEq n] in
/-- The difference of orthogonal isometries has input Gram matrix twice the
identity. Source: the completion proof in Section 6 of
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
theorem gram_sub_of_orthogonal_isometries (J V : Matrix n m ℂ)
    (hJ : Jᴴ * J = 1) (hV : Vᴴ * V = 1) (hJV : Jᴴ * V = 0) :
    (V - J)ᴴ * (V - J) = (2 : ℂ) • (1 : Matrix m m ℂ) := by
  have hVJ : Vᴴ * J = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose hJV
  simp only [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, hJ, hV, hJV, hVJ,
    sub_zero, zero_sub]
  module

/-- The reflection exchanging two orthogonal isometric images. Source:
Section 6 of `docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
def orthogonalIsometrySwap (J V : Matrix n m ℂ) : Matrix n n ℂ :=
  1 - (V - J) * (V - J)ᴴ

/-- Orthogonal isometries admit this explicit unitary exchange. Source:
Section 6 of `docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
theorem orthogonalIsometrySwap_mem_unitaryGroup (J V : Matrix n m ℂ)
    (hJ : Jᴴ * J = 1) (hV : Vᴴ * V = 1) (hJV : Jᴴ * V = 0) :
    orthogonalIsometrySwap J V ∈ unitaryGroup n ℂ := by
  let W := V - J
  have hW : Wᴴ * W = (2 : ℂ) • (1 : Matrix m m ℂ) :=
    gram_sub_of_orthogonal_isometries J V hJ hV hJV
  have hWW : (W * Wᴴ) * (W * Wᴴ) = (2 : ℂ) • (W * Wᴴ) := by
    calc
      _ = W * (Wᴴ * W) * Wᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hW]
        simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
  change (1 - W * Wᴴ) * (1 - W * Wᴴ)ᴴ = 1
  simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
    conjTranspose_conjTranspose]
  simp only [mul_sub, sub_mul, mul_one, one_mul, hWW]
  module

/-- The exchange sends the reference isometry to the other isometry.
Only the reference Gram identity is needed for this action.
Source: Section 6 of
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
theorem orthogonalIsometrySwap_mul_left (J V : Matrix n m ℂ)
    (hJ : Jᴴ * J = 1) (hJV : Jᴴ * V = 0) :
    orthogonalIsometrySwap J V * J = V := by
  have hVJ : Vᴴ * J = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose hJV
  simp only [orthogonalIsometrySwap, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    conjTranspose_sub, hVJ, hJ, Matrix.mul_sub, Matrix.mul_zero, Matrix.mul_one]
  module

/-- The exchange sends the second isometry back to the reference.
Only the second Gram identity is needed for this action.
Source: Section 6 of
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
theorem orthogonalIsometrySwap_mul_right (J V : Matrix n m ℂ)
    (hV : Vᴴ * V = 1) (hJV : Jᴴ * V = 0) :
    orthogonalIsometrySwap J V * V = J := by
  simp only [orthogonalIsometrySwap, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    conjTranspose_sub, hJV, hV, Matrix.mul_sub, Matrix.mul_zero, Matrix.mul_one]
  module

end Matrix

end
