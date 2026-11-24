/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.CorrectedSources.TensorPartition
import QICLean.Analysis.Norm.MatrixKroneckerContraction

/-!
# Product inputs across two sides

A function `f : Q → Bool` sorts the parties into two sides. The vector prepared by an allowed
word without pair sources from a one-dimensional input is a product across the two sides: read
across the cut of the side `true`, its coordinates are the products of the entries of two
columns, each of norm at most one.

## Main results

* `QuantumCircuit.Party.Word.exists_side_product_of_sources_eq_nil`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 137–139 and 409–434.
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.Word

variable {Q : Type} [Fintype Q] [DecidableEq Q] {U X : Q → Type} [∀ q, Fintype (U q)]
  [∀ q, DecidableEq (U q)] [Unique (Config U)] [∀ q, Fintype (X q)]

/-- **A source-free preparation is a product across two sides.** The vector prepared by an
allowed word without pair sources from a one-dimensional input, read across the cut of the
side `true`, has the products of the entries of two columns of norm at most one as
coordinates. Source: Theorem 5.2, `04-compression.tex`, lines 137–139 and 409–434. -/
theorem exists_side_product_of_sources_eq_nil (f : Q → Bool) (p₀ : Word U X)
    (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = []) :
    ∃ (cA : Matrix (RegionConfig (blockSystem f X) {true}) Unit ℂ)
      (cE : Matrix (ComplConfig (blockSystem f X) {true}) Unit ℂ), ‖cA‖ ≤ 1 ∧ ‖cE‖ ≤ 1 ∧
      ∀ s : RegionConfig (blockSystem f X) {true} × ComplConfig (blockSystem f X) {true},
        (p₀.op *ᵥ fun _ ↦ 1) (blockConfigEquiv f X ((cutEquiv (blockSystem f X) {true}).symm s)) =
          cA s.1 () * cE s.2 () := by
  classical
  obtain ⟨c, d, -, -, -, -, hcn, hdn, hop⟩ :=
    isTensorPartitioned_of_sources_internal f p₀ hp₀ (by simp [hp₀s])
  let t := cutEquiv (blockSystem f U) {true} ((blockConfigEquiv f U).symm default)
  have hcol : ∀ {r s : Type} [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
      (M : Matrix r s ℂ) (j : s),
      ‖M.submatrix id fun _ : Unit ↦ j‖ ≤ ‖M‖ := by
    intro r s _ _ _ _ M j
    rw [← l2_opNorm_conjTranspose, conjTranspose_submatrix]
    exact (l2_opNorm_submatrix_le_of_injective _
      (Function.injective_of_subsingleton _)).trans_eq (l2_opNorm_conjTranspose M)
  refine ⟨c.op.submatrix id fun _ ↦ t.1, d.op.submatrix id fun _ ↦ t.2, (hcol _ _).trans hcn,
    (hcol _ _).trans hdn, fun s ↦ ?_⟩
  have hentry := congrFun (congrFun hop ((cutEquiv (blockSystem f X) {true}).symm s))
    ((blockConfigEquiv f U).symm default)
  rw [op_coarsen] at hentry
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    kroneckerMap_apply] at hentry
  simp only [mulVec, dotProduct, mul_one, Fintype.sum_unique, submatrix_apply, id_eq]
  exact hentry

end QuantumCircuit.Party.Word
