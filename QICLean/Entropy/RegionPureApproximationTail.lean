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
    (ψ φ : EuclideanSpace ℂ (∀ v, Fin (n v))) (hψ : ‖ψ‖ = 1)
    (R : Finset V) {D : ℕ} (hrank : (ManyBody.regionState φ R).rank ≤ D)
    {δ : ℝ} (hδ : δ < 1)
    (herror : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) ≤ δ) :
    ∑ i ∈ Finset.Ico D (Fintype.card (ManyBody.RegionConfig (fun v ↦ Fin (n v)) R)),
      (ManyBody.regionState_posSemidef R ψ).isHermitian.descEigenvalue i ≤ δ / 2 := by
  have hn : ‖ManyBody.cutVector R ψ‖ = 1 := (norm_cutVector R ψ).trans hψ
  have he : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct (ManyBody.cutVector R ψ) (ManyBody.cutVector R ψ) -
        Matrix.euclideanOuterProduct (ManyBody.cutVector R φ) (ManyBody.cutVector R φ)) ≤ δ := by
    change Matrix.rectangularTraceNorm
        (Matrix.reindex (ManyBody.cutEquiv (fun v ↦ Fin (n v)) R)
        (ManyBody.cutEquiv (fun v ↦ Fin (n v)) R)
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ)) ≤ δ
    simpa only [Matrix.rectangularTraceNorm_reindex] using herror
  rw [ManyBody.regionState_eq_partialTraceRight_cutVector] at hrank
  convert Matrix.sum_descEigenvalue_tail_le_half_pure_trace_error
    (ManyBody.cutVector R ψ) (ManyBody.cutVector R φ) hn hrank hδ he using 3
  exact ManyBody.regionState_eq_partialTraceRight_cutVector R ψ

end Entropy
