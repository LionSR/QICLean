/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.PartialTrace
import QICLean.Algebra.KroneckerFactorPositivity

/-!
# Partial traces of regrouped tensor powers

The partial trace of a tensor product is the tensor product of its partial
traces. The coordinate equivalence below applies one fixed bipartite
decomposition to each copy and then collects all copies of each factor.
No positivity or normalization is needed.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550–560, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker

namespace TensorPower

/-- Apply a bipartite coordinate decomposition to each copy, then collect
the two families of factors. Source: `07-comparators.tex`, lines 550–560. -/
def copiesProductEquiv {A Q T : Type*} (e : A ≃ Q × T) (m : ℕ) :
    (Fin m → A) ≃ (Fin m → Q) × (Fin m → T) :=
  (Equiv.arrowCongr (Equiv.refl (Fin m)) e).trans
    (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Q) (fun _ => T))

end TensorPower

namespace Matrix

/-- The partial trace of the actual regrouped tensor product is the tensor
product of the actual one-copy partial traces. The factors need not agree.
Source: `07-comparators.tex`, lines 550–560. -/
theorem partialTraceRight_finKronecker_reindex
    {A Q T : Type*} [Fintype A] [Fintype Q] [Fintype T]
    (e : A ≃ Q × T) (m : ℕ) (M : Fin m → Matrix A A ℂ) :
    partialTraceRight ((finKronecker M).submatrix
      (TensorPower.copiesProductEquiv e m).symm
      (TensorPower.copiesProductEquiv e m).symm) =
        finKronecker (fun j => partialTraceRight ((M j).submatrix e.symm e.symm)) := by
  ext x y
  simp only [partialTraceRight_apply, submatrix_apply, finKronecker_apply]
  exact (Fintype.prod_sum
    (fun (j : Fin m) (t : T) => M j (e.symm (x j, t)) (e.symm (y j, t)))).symm

end Matrix
