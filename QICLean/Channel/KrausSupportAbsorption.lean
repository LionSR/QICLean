/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixFamilySupport
import QICLean.Channel.KrausMap

/-!
# Support absorption for finite Kraus families

The support of the output of a finite Kraus map on the identity absorbs every
Kraus operator on the left. A vanishing output on the complementary support
gives right absorption. Consequently, a trace-factorized Kraus map has each
operator between the supports of its positive input and output matrices.
-/

open scoped Matrix BigOperators ComplexOrder

namespace Kraus

variable {r D : ℕ}

/-- If `P` fixes the output of a finite Kraus map on the identity, it fixes
every Kraus operator on the left. The matrix `P` need not be a projection. -/
theorem left_absorption_of_map_one
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P * map K 1 = map K 1) (i : Fin r) :
    P * K i = K i := by
  have hGram : P * Matrix.familyColumnGram K = Matrix.familyColumnGram K := by
    simpa [Matrix.familyColumnGram_eq_sum, map_apply] using hP
  have hzero : (1 - P) * Matrix.familyColumnGram K = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hGram, sub_self]
  have hColumns : (1 - P) * Matrix.familyColumns K = 0 :=
    (Matrix.mul_self_mul_conjTranspose_eq_zero (Matrix.familyColumns K) (1 - P)).mp hzero
  have hFix : P * Matrix.familyColumns K = Matrix.familyColumns K := by
    simpa only [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, eq_comm] using hColumns
  exact Matrix.ext fun a b ↦ by
    simpa [Matrix.familyColumns, Matrix.mul_apply] using congrFun (congrFun hFix a) (i, b)

/-- If a Kraus map vanishes on the complement of an orthogonal projection,
every Kraus operator is absorbed by that projection on the right. -/
theorem mul_eq_self_of_map_one_sub_eq_zero
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    {P : Matrix (Fin D) (Fin D) ℂ} (hP : IsOrthogonalProjection P)
    (hzero : map K (1 - P) = 0) (i : Fin r) :
    K i * P = K i := by
  have hSquare : (1 - P) * (1 - P)ᴴ = 1 - P := by
    simp [Matrix.conjTranspose_sub, hP.1.eq, Matrix.sub_mul, Matrix.mul_sub, hP.2]
  have hsum : ∑ j, (K j * (1 - P)) * (K j * (1 - P))ᴴ = 0 := by
    simpa only [map_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (1 - P), hSquare] using hzero
  simpa only [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, eq_comm] using
    Matrix.eq_zero_of_sum_mul_conjTranspose_eq_zero (fun j ↦ K j * (1 - P)) hsum i

/-- In a trace-factorized Kraus map, the output support absorbs every Kraus
operator on the left. Only positivity of the output factor is required. -/
theorem supportProj_mul_of_map_eq_trace_smul
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    {L R : Matrix (Fin D) (Fin D) ℂ} (hR : R.PosSemidef)
    (hmap : ∀ X, map K X = Matrix.trace (L * X) • R) (i : Fin r) :
    hR.supportProj * K i = K i := by
  apply left_absorption_of_map_one
  rw [hmap, Matrix.mul_smul, hR.supportProj_mul_self]

/-- In a trace-factorized Kraus map, the input support absorbs every Kraus
operator on the right. Only positivity of the input factor is required. -/
theorem mul_supportProj_of_map_eq_trace_smul
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    {L R : Matrix (Fin D) (Fin D) ℂ} (hL : L.PosSemidef)
    (hmap : ∀ X, map K X = Matrix.trace (L * X) • R) (i : Fin r) :
    K i * hL.supportProj = K i := by
  apply mul_eq_self_of_map_one_sub_eq_zero K hL.isOrthogonalProjection_supportProj
  rw [hmap, Matrix.mul_sub, Matrix.mul_one, hL.mul_supportProj_self,
    sub_self, Matrix.trace_zero, zero_smul]

end Kraus
