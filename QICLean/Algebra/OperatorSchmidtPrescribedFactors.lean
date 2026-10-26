/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidt

/-!
# Product decompositions retaining a prescribed finite family of factors

If all partial matrix elements belong to the span of a finite family, that
same family can be retained as one side of a product decomposition. No change
of basis is made within its members. This preserves any property already
proved for the prescribed factors.
The decomposition is supporting algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333.
-/

open scoped BigOperators Kronecker

namespace Matrix

/-- A prescribed finite family spanning every right operator block can be
retained as the right factors. Supporting algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1316–1333. -/
theorem exists_left_factors_of_operatorBlock_mem_span
    {m n ι : Type*} [Fintype ι]
    (M : Matrix (m × n) (m × n) ℂ) (C : ι → Matrix n n ℂ)
    (hC : ∀ i j, operatorBlock M i j ∈ Submodule.span ℂ (Set.range C)) :
    ∃ A : ι → Matrix m m ℂ, M = ∑ t, A t ⊗ₖ C t := by
  classical
  have hcoeff (ij : m × m) : ∃ c : ι → ℂ,
      ∑ t, c t • C t = operatorBlock M ij.1 ij.2 :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hC ij.1 ij.2)
  choose c hc using hcoeff
  refine ⟨fun t i j ↦ c (i, j) t, ?_⟩
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.sum_apply]
  change M (i, k) (j, l) = ∑ t, c (i, j) t * C t k l
  have hentry := congrFun (congrFun (hc (i, j)) k) l
  simpa only [operatorBlock, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using hentry.symm

/-- A prescribed finite family spanning the exterior partial matrix elements
can be retained as the left factors. No finiteness assumption on either local
configuration type is needed. This is the orientation of the middle factors
in ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1316–1333. -/
theorem exists_right_factors_of_left_blocks_mem_span
    {m n ι : Type*} [Fintype ι]
    (M : Matrix (m × n) (m × n) ℂ) (C : ι → Matrix m m ℂ)
    (hC : ∀ i j : n, (fun k l : m ↦ M (k, i) (l, j)) ∈
      Submodule.span ℂ (Set.range C)) :
    ∃ B : ι → Matrix n n ℂ, M = ∑ t, C t ⊗ₖ B t := by
  classical
  have hcoeff (ij : n × n) : ∃ c : ι → ℂ,
      ∑ t, c t • C t = (fun k l : m ↦ M (k, ij.1) (l, ij.2)) :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hC ij.1 ij.2)
  choose c hc using hcoeff
  refine ⟨fun t i j ↦ c (i, j) t, ?_⟩
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.sum_apply]
  change M (i, k) (j, l) = ∑ t, C t i j * c (k, l) t
  have hentry := congrFun (congrFun (hc (k, l)) i) j
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm] using hentry.symm

end Matrix
