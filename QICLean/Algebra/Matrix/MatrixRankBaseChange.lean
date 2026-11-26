/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Matrix rank under scalar extension

This file proves rank invariance for finite matrices under scalar extension.

## Main results

* `Matrix.rank_map_algebraMap`: extending scalars along a faithful field
  extension preserves the rank of a finite matrix.

Moved from TNLean, `TNLean/MPS/FundamentalTheorem/Refinement/QubitRootRank.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

open Matrix Module Submodule Set

namespace Matrix

variable {K m n : Type*} [Field K] [Fintype n]

variable [Finite m]

/-- Extending scalars along a faithful field extension does not change the rank
of a finite matrix. -/
theorem rank_map_algebraMap {L : Type*}
    [Field L] [Algebra K L] [FaithfulSMul K L]
    (A : Matrix m n K) :
    (A.map (algebraMap K L)).rank = A.rank := by
  classical
  have hli (s : ℕ) (j : Fin s → n) :
      LinearIndependent L (fun i ↦ (A.map (algebraMap K L)).col (j i)) ↔
        LinearIndependent K (fun i ↦ A.col (j i)) := by
    have hcols :
        (fun i ↦ (A.map (algebraMap K L)).col (j i)) =
          (fun i ↦ (algebraMap K L) ∘ A.col (j i)) := by
      funext i x
      rfl
    rw [hcols]
    exact linearIndependent_algebraMap_comp_iff
  apply le_antisymm
  · rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
    obtain ⟨v, hv_mem, _, hv_ind⟩ :=
      Submodule.exists_fun_fin_finrank_span_eq L
        (Set.range (A.map (algebraMap K L)).col)
    choose j hj using hv_mem
    have hselectedL :
        LinearIndependent L (fun i ↦ (A.map (algebraMap K L)).col (j i)) := by
      rw [funext hj]
      exact hv_ind
    have hselectedK : LinearIndependent K (fun i ↦ A.col (j i)) :=
      (hli _ j).mp hselectedL
    have hrange : Set.range (fun i ↦ A.col (j i)) ⊆ Set.range A.col := by
      rintro _ ⟨i, rfl⟩
      exact ⟨j i, rfl⟩
    simpa using (linearIndependent_iff_card_le_finrank_span.mp hselectedK).trans
      (Submodule.finrank_mono (Submodule.span_mono hrange))
  · rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
    obtain ⟨v, hv_mem, _, hv_ind⟩ :=
      Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.col)
    choose j hj using hv_mem
    have hselectedK : LinearIndependent K (fun i ↦ A.col (j i)) := by
      rw [funext hj]
      exact hv_ind
    have hselectedL :
        LinearIndependent L (fun i ↦ (A.map (algebraMap K L)).col (j i)) :=
      (hli _ j).mpr hselectedK
    have hrange :
        Set.range (fun i ↦ (A.map (algebraMap K L)).col (j i)) ⊆
          Set.range (A.map (algebraMap K L)).col := by
      rintro _ ⟨i, rfl⟩
      exact ⟨j i, rfl⟩
    simpa using (linearIndependent_iff_card_le_finrank_span.mp hselectedL).trans
      (Submodule.finrank_mono (Submodule.span_mono hrange))

end Matrix

section MatrixRankKronecker

/-!
# Rank of a Kronecker product

This file proves that matrix rank is multiplicative under the Kronecker product over a field.

## Main results

* `Matrix.rank_kronecker`: the rank of `A ⊗ₖ B` is the product of the ranks of `A` and `B`.
-/

open scoped Kronecker

namespace Matrix

variable {K m n p q : Type*} [Field K] [Finite m] [Fintype n] [Finite p] [Fintype q]

/-- Matrix rank is multiplicative under the Kronecker product over a field. -/
theorem rank_kronecker (A : Matrix m n K) (B : Matrix p q K) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  classical
  rw [Matrix.rank_eq_finrank_range_toLin (A ⊗ₖ B)
      ((Pi.basisFun K m).tensorProduct (Pi.basisFun K p))
      ((Pi.basisFun K n).tensorProduct (Pi.basisFun K q)),
    Matrix.toLin_kronecker,
    TensorProduct.range_map,
    ← TensorProduct.range_mapIncl,
    LinearMap.finrank_range_of_inj
      (Module.Flat.tensorProduct_mapIncl_injective_of_left
        (LinearMap.range (Matrix.toLin (Pi.basisFun K n) (Pi.basisFun K m) A))
        (LinearMap.range (Matrix.toLin (Pi.basisFun K q) (Pi.basisFun K p) B))),
    Module.finrank_tensorProduct,
    ← Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun K m) (Pi.basisFun K n),
    ← Matrix.rank_eq_finrank_range_toLin B (Pi.basisFun K p) (Pi.basisFun K q)]

end Matrix

end MatrixRankKronecker

section

open scoped Matrix BigOperators

private abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

private def detPolar : LinearMap.BilinForm ℂ QubitMatrix :=
  LinearMap.mk₂ ℂ
    (fun A B => A 0 0 * B 1 1 + A 1 1 * B 0 0 - A 0 1 * B 1 0 - A 1 0 * B 0 1)
    (by intro A B C; simp only [Matrix.add_apply]; ring)
    (by intro c A B; simp only [Matrix.smul_apply, smul_eq_mul]; ring)
    (by intro A B C; simp only [Matrix.add_apply]; ring)
    (by intro c A B; simp only [Matrix.smul_apply, smul_eq_mul]; ring)

private theorem detPolar_symm (A B : QubitMatrix) : detPolar A B = detPolar B A := by
  simp only [detPolar, LinearMap.mk₂_apply]
  ring

private theorem detPolar_left_nondegenerate (A : QubitMatrix)
    (hA : ∀ B, detPolar A B = 0) : A = 0 := by
  have h00 := hA (Matrix.single 1 1 1)
  have h01 := hA (Matrix.single 1 0 1)
  have h10 := hA (Matrix.single 0 1 1)
  have h11 := hA (Matrix.single 0 0 1)
  simp [detPolar] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using h00
  · simpa using h01
  · simpa using h10
  · simpa using h11

namespace Matrix

/-- An all-singular complex subspace of `2 × 2` matrices has dimension at
most two. Polarization of determinant makes the subspace isotropic for a
nondegenerate bilinear form on a four-dimensional space. This supplies
the low-dimensional root-rank argument for arXiv:1708.00029, Theorem 4.1. -/
theorem finrank_le_two_of_forall_det_eq_zero_fin_two
    (S : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ))
    (hDet : ∀ X ∈ S, X.det = 0) : Module.finrank ℂ S ≤ 2 := by
  have hNondeg : detPolar.Nondegenerate := by
    refine ⟨detPolar_left_nondegenerate, ?_⟩
    intro A hA
    apply detPolar_left_nondegenerate A
    intro B
    rw [detPolar_symm]
    exact hA B
  have hLe : S ≤ detPolar.orthogonal S := by
    intro A hA
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro B hB
    have hAB := hDet (B + A) (S.add_mem hB hA)
    have hA' := hDet A hA
    have hB' := hDet B hB
    simp only [Matrix.det_fin_two, Matrix.add_apply] at hAB hA' hB'
    change B 0 0 * A 1 1 + B 1 1 * A 0 0 - B 0 1 * A 1 0 - B 1 0 * A 0 1 = 0
    linear_combination hAB - hA' - hB'
  have hDim := Submodule.finrank_mono hLe
  have hTotal : Module.finrank ℂ QubitMatrix = 4 := by simp [Module.finrank_matrix]
  rw [LinearMap.BilinForm.finrank_orthogonal hNondeg, hTotal] at hDim
  change Module.finrank ℂ S ≤ 4 - Module.finrank ℂ S at hDim
  omega

end Matrix

end
