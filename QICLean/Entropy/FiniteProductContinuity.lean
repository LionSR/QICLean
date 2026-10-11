/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.ControlledContinuity
import QICLean.Entropy.FiniteProduct

/-!
# Regional entropy under perturbation of a pure state

The entropy of a fixed region depends continuously on the original pure
state. The dimension in the estimate is that of the region, while the trace
distance is that of the two original states on the complete finite system.
The argument uses contraction of trace distance under the partial trace.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, Lemma 2.1 (`01-preliminaries.tex`, lines 33–46), as used in
`08-scanner.tex`, lines 399–404, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open scoped Matrix ComplexOrder

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The entropy change on a fixed region is bounded by the trace distance
of the original normalized pure states and the dimension of that region.
Source: Lemma 2.1, `01-preliminaries.tex`, lines 33–46, and its application
in `08-scanner.tex`, lines 399–404. -/
theorem abs_entropy_sub_le_sqrt_traceDistance
    (Ω Φ : EuclideanSpace ℂ ((v : V) → β v))
    (hΩ : ‖Ω‖ = 1) (hΦ : ‖Φ‖ = 1) (R : Finset V) :
    |entropy β Ω R - entropy β Φ R| ≤
      4 * Real.sqrt (Matrix.traceDistance
        (Matrix.vecMulVec Ω (star Ω)) (Matrix.vecMulVec Φ (star Φ))) *
        Real.log (Real.exp 1 * Fintype.card (Configuration β R)) := by
  have hcont := Entropy.abs_vonNeumannEntropy_sub_le_sqrt
    (reducedPure_posSemidef β Ω R) (reducedPure_posSemidef β Φ R)
    (trace_reducedPure β Ω hΩ R) (trace_reducedPure β Φ hΦ R)
  have hdist : Matrix.traceDistance (reducedPure β Ω R) (reducedPure β Φ R) ≤
      Matrix.traceDistance (Matrix.vecMulVec Ω (star Ω))
        (Matrix.vecMulVec Φ (star Φ)) :=
    (Matrix.traceDistance_partialTraceRight_le
      ((Matrix.posSemidef_vecMulVec_self_star Ω).submatrix (splitEquiv β R).symm).isHermitian
      ((Matrix.posSemidef_vecMulVec_self_star Φ).submatrix (splitEquiv β R).symm).isHermitian
      ((Matrix.trace_partialTraceRight _).symm.trans
        ((trace_reducedPure β Ω hΩ R).trans
          ((trace_reducedPure β Φ hΦ R).symm.trans (Matrix.trace_partialTraceRight _))))).trans_eq
      (Matrix.traceDistance_submatrix_equiv (splitEquiv β R).symm
        (Matrix.posSemidef_vecMulVec_self_star Ω).isHermitian
        (Matrix.posSemidef_vecMulVec_self_star Φ).isHermitian)
  done

end FiniteProduct
