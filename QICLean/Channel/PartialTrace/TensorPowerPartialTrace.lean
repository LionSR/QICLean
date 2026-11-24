/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.PartialTrace
import QICLean.Algebra.Kronecker.KroneckerFactorPositivity

/-!
# Partial traces of regrouped tensor powers

The partial trace of a tensor product is the tensor product of its partial
traces. The coordinate equivalence below applies one fixed bipartite
decomposition to each copy and then collects all copies of each factor.
No positivity or normalization is needed. The same holds for a Kronecker product of a family
of matrices on `X p × E p` whose factor types depend on the index `p`
(`Matrix.partialTraceRight_piKronecker_submatrix`).

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550–560, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`; *Polynomial PEPS approximation of gapped
square-grid ground states*, September 24, 2026, proof of Theorem 5.2, `04-compression.tex`,
lines 574–579.
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

/-- Tracing out the second factors `E p` of a Kronecker product of matrices on `X p × E p`,
after grouping the configurations into the pair `((p ↦ x p), (p ↦ e p))`, gives the Kronecker
product of the partial traces. The factor types may vary with `p`.

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states* (September 24,
2026), proof of Theorem 5.2, `04-compression.tex`, lines 574–579. -/
theorem partialTraceRight_piKronecker_submatrix {P : Type*} [Fintype P] [DecidableEq P]
    {X E : P → Type*} [∀ p, Fintype (E p)] (M : (p : P) → Matrix (X p × E p) (X p × E p) ℂ) :
    partialTraceRight ((piKronecker M).submatrix (Equiv.arrowProdEquivProdArrow P X E).symm
      (Equiv.arrowProdEquivProdArrow P X E).symm) =
      piKronecker fun p ↦ partialTraceRight (M p) := by
  ext x y
  simp only [partialTraceRight_apply, submatrix_apply, piKronecker_apply]
  exact (Fintype.prod_sum fun p (e : E p) ↦ M p (x p, e) (y p, e)).symm

/-- The partial trace of the actual regrouped tensor product is the tensor
product of the actual one-copy partial traces. The factors need not agree.
Source: `07-comparators.tex`, lines 550–560. -/
theorem partialTraceRight_piKronecker_reindex
    {A Q T : Type*} [Fintype T]
    (e : A ≃ Q × T) (m : ℕ) (M : Fin m → Matrix A A ℂ) :
    partialTraceRight ((piKronecker M).submatrix
      (TensorPower.copiesProductEquiv e m).symm
      (TensorPower.copiesProductEquiv e m).symm) =
        piKronecker (fun j => partialTraceRight ((M j).submatrix e.symm e.symm)) := by
  exact partialTraceRight_piKronecker_submatrix fun j => (M j).submatrix e.symm e.symm

end Matrix
