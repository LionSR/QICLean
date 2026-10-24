/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.PureApproximationSpectralTail
import QICLean.Entropy.RegionEntropy
import QICLean.Analysis.RectangularTraceNormAlgebra

/-!
# Half-error spectral tails of regional reductions

A rank bound on the approximant's regional reduction bounds the target's
ordered spectral tail by half the global full trace error, when that error is
strictly below one. Only the target vector is normalized. This is the regional
form of the optimized pure-error and Ky Fan estimates in SWVC08,
arXiv:0705.0292v2, lines 160–173 and 247–264.
-/

open scoped ComplexOrder

namespace Entropy

/-- Regional discarded spectral mass is bounded by half the global pure-density
trace error. This is the regional form of the optimized pure-error and Ky Fan
estimates in SWVC08, arXiv:0705.0292v2, lines 160–173 and 247–264. -/
theorem sum_descEigenvalue_regionState_tail_le_half_pure_trace_error
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    (ψ φ : EuclideanSpace ℂ (SiteConfig n)) (hψ : ‖ψ‖ = 1)
    (R : Finset V) {D : ℕ} (hrank : (regionState R φ).rank ≤ D)
    {δ : ℝ} (hδ : δ < 1)
    (herror : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) ≤ δ) :
    ∑ i ∈ Finset.Ico D (Fintype.card (RegionConfig n R)),
      (regionState_posSemidef R ψ).isHermitian.descEigenvalue i ≤ δ / 2 := by
  have hn : ‖cutVector R ψ‖ = 1 := (norm_cutVector R ψ).trans hψ
  have he : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct (cutVector R ψ) (cutVector R ψ) -
        Matrix.euclideanOuterProduct (cutVector R φ) (cutVector R φ)) ≤ δ := by
    change Matrix.rectangularTraceNorm (Matrix.reindex (cutEquiv n R) (cutEquiv n R)
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ)) ≤ δ
    simpa only [Matrix.rectangularTraceNorm_reindex] using herror
  exact Matrix.sum_descEigenvalue_tail_le_half_pure_trace_error
    (cutVector R ψ) (cutVector R φ) hn hrank hδ he

end Entropy
