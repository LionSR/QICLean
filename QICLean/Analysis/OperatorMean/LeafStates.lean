/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.TreeDerivative

/-!
# Leaf states of a finite mean tree

The trace adjoint `Φ_j^†` of a unital completely positive leaf map, defined by
`Tr(Φ_j^†(ρ) Z) = Tr(ρ Φ_j(Z))`, is positive and trace preserving. It therefore carries a
density matrix at the root of a mean tree to a density matrix at each leaf of positive
terminal weight. These are the states against which the area-law argument averages
entropy gains and energy errors.

## Main results

* `Matrix.MeanTree.posSemidef_traceAdjoint_leafMap` — `Φ_j^†` maps positive
  semidefinite matrices to positive semidefinite matrices.
* `Matrix.MeanTree.trace_traceAdjoint_leafMap` — `Φ_j^†` preserves the trace when the
  terminal weight `w_j` is positive.

## References

* *A two-dimensional area law from a global spectral gap* (September 24, 2026),
  `build/sections/06-transport.tex`, lines 11--14 and Lemma 7.2 (`transport:cp`).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.MeanTree

variable {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [DecidableEq ι]
  {A : ι → Matrix n n ℂ}

/-- The trace adjoint of a leaf map is positive. -/
theorem posSemidef_traceAdjoint_leafMap (hA : ∀ i, (A i).PosDef) (T : MeanTree ι) (j : ι)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (traceAdjointMap (T.leafMap A j).toLinearMap ρ).PosSemidef := by
  have hpos : IsPositiveMap (T.leafMap A j).toLinearMap :=
    isNPositiveMap_one_iff_isPositiveMap.mp (isNPositiveMap_leafMap hA T j 1)
  exact hpos.traceAdjointMap ρ hρ

/-- The trace adjoint of a leaf map of positive terminal weight preserves the trace. -/
theorem trace_traceAdjoint_leafMap (hA : ∀ i, (A i).PosDef) (T : MeanTree ι) {j : ι}
    (hw : T.weight j ≠ 0) (ρ : Matrix n n ℂ) :
    (traceAdjointMap (T.leafMap A j).toLinearMap ρ).trace = ρ.trace := by
  have h := trace_traceAdjointMap_mul (T.leafMap A j).toLinearMap ρ 1
  rw [Matrix.mul_one, ContinuousLinearMap.coe_coe, leafMap_one hA T hw, Matrix.mul_one] at h
  exact h

end Matrix.MeanTree
