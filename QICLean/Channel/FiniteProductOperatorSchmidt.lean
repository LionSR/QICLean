/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtPartition
import QICLean.Channel.FiniteProduct

/-!
# Operator Schmidt rank in finite-product coordinates

For a uniform finite local dimension, changing the region from `S` to `T`
increases operator Schmidt rank by at most `q ^ (2 * (S ∆ T).card)`.
The operator is expressed in the existing finite-product coordinates on each
side of the region. The two ranks refer to the same original matrix.

Zero local dimension and the empty site set are included. The bound uses the
exact cardinality of the symmetric difference, as in ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1331–1333.
-/

open scoped symmDiff

/-- Changing a region costs the square of the number of configurations on
its symmetric difference with the original region. Supporting finite-product
algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1331–1333.
No positivity assumption on the local dimension is required. -/
theorem FiniteProduct.operatorSchmidtRank_splitEquiv_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (S T : Finset V)
    (M : Matrix (V → Fin q) (V → Fin q) ℂ) :
    Matrix.operatorSchmidtRank
        (M.reindex (FiniteProduct.splitEquiv (fun _ : V ↦ Fin q) T)
          (FiniteProduct.splitEquiv (fun _ : V ↦ Fin q) T)) ≤
      q ^ (2 * (S ∆ T).card) * Matrix.operatorSchmidtRank
        (M.reindex (FiniteProduct.splitEquiv (fun _ : V ↦ Fin q) S)
          (FiniteProduct.splitEquiv (fun _ : V ↦ Fin q) S)) := by
  have hcut (R : Finset V) : Matrix.operatorSchmidtRank
      (M.reindex (FiniteProduct.splitEquiv (fun _ : V ↦ Fin q) R)
        (FiniteProduct.splitEquiv (fun _ : V ↦ Fin q) R)) =
      Matrix.operatorSchmidtRank
        (M.reindex (Equiv.piEquivPiSubtypeProd (fun v ↦ v ∈ R) (fun _ ↦ Fin q))
          (Equiv.piEquivPiSubtypeProd (fun v ↦ v ∈ R) (fun _ ↦ Fin q))) := by
    exact Matrix.operatorSchmidtRank_reindex_prodCongr
      (M.reindex (Equiv.piEquivPiSubtypeProd (fun v ↦ v ∈ R) (fun _ ↦ Fin q))
        (Equiv.piEquivPiSubtypeProd (fun v ↦ v ∈ R) (fun _ ↦ Fin q)))
      (Equiv.refl _) (FiniteProduct.complementEquiv (fun _ : V ↦ Fin q) R)
  rw [hcut T, hcut S]
  exact Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_finset_le q S T M
