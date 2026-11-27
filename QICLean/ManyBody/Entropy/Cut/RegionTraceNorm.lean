/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.Entropy.Surprisal.FilterMoment
import QICLean.ManyBody.Sites.RegionState
import QICLean.Analysis.TraceNorm.RectangularTraceNormContraction
import QICLean.Analysis.TraceNorm.RectangularTraceNormAlgebra
import QICLean.Analysis.TraceNorm.SubnormalizedPureStateError
import QICLean.Channel.Schmidt.PureApproximationSpectralTail
import QICLean.ManyBody.Entropy.RegionEntropy

/-!
# Trace-norm contraction of regional pure-state reduction

Taking a reduced matrix does not increase the full trace-norm difference of
two pure-state matrices. The vectors need not be normalized.

## Main results

* `Entropy.sum_descEigenvalue_regionState_tail_le_half_pure_trace_error`: half-error spectral tails
  of regional reductions.
-/

section RegionTraceNorm

namespace Entropy

/-- Regional reduction contracts the full trace-norm error of pure-state matrices. -/
theorem rectangularTraceNorm_regionState_sub_le {V : Type*} [Fintype V] [DecidableEq V]
    {n : V → ℕ} (ψ φ : EuclideanSpace ℂ (∀ v, Fin (n v))) (R : Finset V) :
    Matrix.rectangularTraceNorm (ManyBody.regionState ψ R - ManyBody.regionState φ R) ≤
      Matrix.rectangularTraceNorm
        (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) := by
  rw [ManyBody.regionState_eq_partialTraceRight_cutVector,
    ManyBody.regionState_eq_partialTraceRight_cutVector]
  let e := ManyBody.cutEquiv (fun v ↦ Fin (n v)) R
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

end RegionTraceNorm

section RegionPureApproximationTail

/-!
## Half-error spectral tails of regional reductions

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

end RegionPureApproximationTail
