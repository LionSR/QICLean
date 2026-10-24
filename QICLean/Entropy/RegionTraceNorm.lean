/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.LocalLift
import QICLean.Channel.RectangularTraceNormContraction
import QICLean.Analysis.RectangularTraceNormAlgebra
import QICLean.Analysis.SubnormalizedPureStateError

/-!
# Trace-norm contraction of regional pure-state reduction

Taking a reduced matrix does not increase the full trace-norm difference of
two pure-state matrices. The vectors need not be normalized.
-/

namespace Entropy

/-- Regional reduction contracts the full trace-norm error of pure-state matrices. -/
theorem rectangularTraceNorm_regionState_sub_le {V : Type*} [Fintype V] [DecidableEq V]
    {n : V → ℕ} (ψ φ : EuclideanSpace ℂ (SiteConfig n)) (R : Finset V) :
    Matrix.rectangularTraceNorm (regionState R ψ - regionState R φ) ≤
      Matrix.rectangularTraceNorm
        (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) := by
  let e := cutEquiv n R
  have hcontract := Matrix.rectangularTraceNorm_partialTraceRight_le
    (Matrix.reindex e e (Matrix.euclideanOuterProduct ψ ψ -
      Matrix.euclideanOuterProduct φ φ))
  rw [Matrix.rectangularTraceNorm_reindex, Matrix.reindex_apply,
    Matrix.submatrix_sub] at hcontract
  change Matrix.rectangularTraceNorm (Matrix.partialTraceRightLM
    ((Matrix.euclideanOuterProduct ψ ψ).submatrix e.symm e.symm -
      (Matrix.euclideanOuterProduct φ φ).submatrix e.symm e.symm)) ≤ _ at hcontract
  rw [map_sub] at hcontract
  exact hcontract

end Entropy
