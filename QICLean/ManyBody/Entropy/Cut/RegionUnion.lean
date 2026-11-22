/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Entropy.Filter.Optimizer
import QICLean.ManyBody.Sites.RegionUnion

/-!
# Trial filters on a disjoint union of regions

For disjoint regions `X` and `T`, the configurations of `X ∪ T` are pairs of configurations of
`X` and of `T` (`ManyBody.regionUnionEquiv`), and the placement of `A ⊗ B` on `X ∪ T` is the
product of the placements of `A` and of `B` (`ManyBody.place_union_kronecker`). A rank-one
projection onto a column of a unitary, tensored with a filter feasible at floor zero, is
feasible at floor zero on the union.

## Main results

* `Entropy.isFeasibleFilter_union_kronecker`: `|u_i⟩⟨u_i| ⊗ M` is feasible at floor zero on
  `X ∪ T` when `M` is feasible at floor zero on `T`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 3.2
  (`lem:initial-buffer`), `02-initial.tex`, lines 512–520: trial filters
  `|u_i⟩⟨u_i| ⊗ M_j` on `X_j = X ⊔ T_j`.

Independently written from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped Kronecker
open ManyBody (regionUnionEquiv)

namespace Entropy

variable {V : Type*} [DecidableEq V] {n : V → ℕ}

/-- **Trial filters are feasible at floor zero.** If `U` is unitary and `M` is feasible at
floor zero with weight `a > 0`, then `|u_i⟩⟨u_i| ⊗ M`, with `u_i` the `i`-th column of `U`, is
feasible at floor zero on `X ∪ T`. -/
theorem isFeasibleFilter_union_kronecker {X T : Finset V} (hXT : Disjoint X T) {a : ℝ}
    (ha : 0 < a)
        {U : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) X)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) X) ℂ} (hU : Uᴴ * U = 1)
    (i : (ManyBody.RegionConfig (fun v ↦ Fin (n v)) X))
        {M : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) T)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) T) ℂ}
    (hM : IsFeasibleFilter 0 a M) :
    IsFeasibleFilter 0 a (reindex (regionUnionEquiv hXT).symm (regionUnionEquiv hXT).symm
      ((U * diagonal (fun k ↦ if k = i then (1 : ℂ) else 0) * Uᴴ) ⊗ₖ M)) := by
  obtain ⟨W, z, hW, hz, hzs, rfl⟩ := hM
  set e := regionUnionEquiv (β := fun v ↦ Fin (n v)) hXT
  set y : (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (X ∪ T)) → ℝ := fun σ ↦ if (e σ).1 = i then z
      (e σ).2 else 0
  have hha : a / 2 ≠ 0 := by positivity
  refine ⟨reindex e.symm e.symm (U ⊗ₖ W), y, ?_, fun σ ↦ ?_, ?_, ?_⟩
  · rw [conjTranspose_reindex, reindex_apply, reindex_apply, submatrix_mul_equiv,
      conjTranspose_kronecker, ← mul_kronecker_mul, hU, hW, one_kronecker_one,
      submatrix_one_equiv]
  · simp only [y]; split_ifs
    · exact hz _
    · exact le_rfl
  · rw [← Equiv.sum_comp e.symm]
    simpa [y, Equiv.apply_symm_apply, Fintype.sum_prod_type] using hzs
  · have hdiag : diagonal (fun σ ↦ ((y σ ^ (a / 2) : ℝ) : ℂ)) = reindex e.symm e.symm
        (diagonal (fun k ↦ if k = i then (1 : ℂ) else 0) ⊗ₖ
          diagonal (fun l ↦ ((z l ^ (a / 2) : ℝ) : ℂ))) := by
      rw [diagonal_kronecker_diagonal, reindex_apply, Equiv.symm_symm, submatrix_diagonal_equiv]
      congr 1
      funext σ
      simp only [y, Function.comp_apply]
      split_ifs <;> simp [Real.zero_rpow hha]
    rw [hdiag, conjTranspose_reindex, reindex_apply, reindex_apply, reindex_apply,
      reindex_apply, submatrix_mul_equiv, submatrix_mul_equiv, conjTranspose_kronecker,
      ← mul_kronecker_mul, ← mul_kronecker_mul]

end Entropy
