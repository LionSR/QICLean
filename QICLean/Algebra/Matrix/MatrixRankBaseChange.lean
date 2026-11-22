/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.RingTheory.Flat.Basic

/-!
# Matrix rank under scalar extension

This file proves rank invariance for finite matrices under scalar extension.

## Main results

* `Matrix.rank_map_algebraMap`: extending scalars along a faithful field
  extension preserves the rank of a finite matrix.
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
