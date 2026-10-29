/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidt
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Operator Schmidt rank and the matrix of paired local indices

The operator Schmidt rank equals the ordinary rank of the matrix whose row
index pairs the first subsystem's two indices and whose column index pairs
the second subsystem's two indices. This identifies the operator Schmidt rank with
the coefficient cut rank after combining each site's two physical indices.
See arXiv:1903.05373, equation (1), and the product factors in ALVV,
arXiv:1602.08828v2, Proposition 5.7.
-/

namespace Matrix

/-- Pairing the row and column indices within each tensor factor turns
operator Schmidt rank into ordinary matrix rank. This is the matrix-rank
characterization of the decomposition in arXiv:1903.05373, equation (1). -/
theorem operatorSchmidtRank_eq_rank_realignment
    {R m n : Type*} [Field R] [Fintype m] [Fintype n]
    (M : Matrix (m × n) (m × n) R) :
    operatorSchmidtRank M =
      Matrix.rank (fun (ij : m × m) (kl : n × n) ↦ M (ij.1, kl.1) (ij.2, kl.2)) := by
  let C : Matrix (m × m) (n × n) R :=
    fun ij kl ↦ M (ij.1, kl.1) (ij.2, kl.2)
  let e : Matrix n n R ≃ₗ[R] ((n × n) → R) :=
    (Matrix.ofLinearEquiv (R := R)).symm.trans (LinearEquiv.curry R R n n).symm
  have hspan : (operatorBlockSpan M).map e.toLinearMap =
      Submodule.span R (Set.range C.row) := by
    rw [operatorBlockSpan, ← Submodule.span_image, ← Set.range_comp]
    rfl
  rw [operatorSchmidtRank_eq_finrank_operatorBlockSpan]
  change Module.finrank R (operatorBlockSpan M) = C.rank
  rw [Matrix.rank_eq_finrank_span_row, ← hspan]
  exact (e.finrank_map_eq (operatorBlockSpan M)).symm

end Matrix
