/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.KyFanNorm
import QICLean.Analysis.TraceDistance
import QICLean.Analysis.RectangularTraceNormAlgebra

/-!
# Spectral tails and trace-norm approximation

The finite-dimensional spectral estimate used in Schuch–Wolf–Verstraete–Cirac,
*Entropy scaling and simulability by matrix product states*, arXiv:0705.0292v2,
Eq. (eps-lower): approximation by a matrix of rank at most `k` costs at least
the sum of the eigenvalues discarded after the first `k`.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {n k : ℕ} {ρ σ E H : Matrix (Fin n) (Fin n) ℂ}

private theorem trace_effect_le_posPart
    {ι : Type*} [Fintype ι] [DecidableEq ι] {H E : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hE : E.PosSemidef) (hE1 : E ≤ 1) :
    (E * H).trace.re ≤ (H⁺).trace.re := by
  have hp : (H⁺).PosSemidef := nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H)
  have hn : (H⁻).PosSemidef := nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)
  have hpos := hp.re_trace_mul_le_of_le_one hE1
  have heq := congrArg (fun A : Matrix ι ι ℂ ↦ (E * A).trace.re)
    (CFC.posPart_sub_negPart H hH)
  simp only [mul_sub, trace_sub, Complex.sub_re] at heq
  linarith [hE.re_trace_mul_nonneg hn]

private theorem tail_le_complement (hρ : ρ.PosSemidef) (hσ : σ.IsHermitian)
    (hrank : σ.rank ≤ k) (hk : k < n) :
    ∑ i ∈ Finset.Ico k n, hρ.isHermitian.descEigenvalue i ≤
      ((1 - hσ.supportProj) * ρ).trace.re := by
  have hky := hρ.isHermitian.trace_mul_re_le_kyFanNorm
    (by simpa using hrank.trans_lt hk) hσ.supportProj_isHermitian
    hσ.supportProj_idem (by simp [hσ.supportProj_trace])
  have hmono := hρ.kyFanNorm_mono hrank
  have hsum : (∑ i ∈ Finset.range n, hρ.isHermitian.descEigenvalue i) = ρ.trace.re := by
    simpa only [Fintype.card_fin, IsHermitian.kyFanNorm] using
      hρ.isHermitian.kyFanNorm_card_eq_trace_re
  rw [Finset.sum_Ico_eq_sub _ hk.le, hsum, sub_mul, one_mul, trace_sub, Complex.sub_re]
  exact sub_le_sub_left (hky.trans hmono) _

private theorem tail_le_posPart
    (hρ : ρ.PosSemidef) (hσ : σ.IsHermitian) (hrank : σ.rank ≤ k) :
    ∑ i ∈ Finset.Ico k n, hρ.isHermitian.descEigenvalue i ≤ ((ρ - σ)⁺).trace.re := by
  by_cases hk : k < n
  · have htail := tail_le_complement hρ hσ hrank hk
    have hP : IsOrthogonalProjection hσ.supportProj :=
      ⟨hσ.supportProj_isHermitian, hσ.supportProj_idem⟩
    have hbound := trace_effect_le_posPart (hρ.isHermitian.sub hσ)
      (isOrthogonalProjection_posSemidef hP.one_sub)
      (sub_le_self _ hP.isStarProjection.nonneg)
    simp only [mul_sub, hσ.one_sub_supportProj_mul_self, sub_zero] at hbound
    exact htail.trans hbound
  · simpa [Finset.Ico_eq_empty_of_le (Nat.le_of_not_gt hk)] using
      (Complex.nonneg_iff.mp
        (nonneg_iff_posSemidef.mp (CFC.posPart_nonneg (ρ - σ))).trace_nonneg).1

/-- The discarded ordered spectral mass is bounded by the full trace norm of
any Hermitian rank-`k` approximation. This is the finite-dimensional estimate
in SWVC08, arXiv:0705.0292v2, Eq. (eps-lower), without normalization assumptions.
In particular it applies to every positive semidefinite approximation. -/
theorem PosSemidef.sum_descEigenvalue_tail_le_traceNorm
    (hρ : ρ.PosSemidef) (hσ : σ.IsHermitian) (hrank : σ.rank ≤ k) :
    ∑ i ∈ Finset.Ico k n, hρ.isHermitian.descEigenvalue i ≤ traceNorm (ρ - σ) := by
  have htail := tail_le_posPart hρ hσ hrank
  rw [(hρ.isHermitian.sub hσ).traceNorm_eq_re_trace_posPart_add_negPart]
  exact htail.trans (le_add_of_nonneg_right ((Complex.nonneg_iff.mp
    (nonneg_iff_posSemidef.mp (CFC.negPart_nonneg (ρ - σ))).trace_nonneg).1))

/-- For equal traces, the discarded ordered spectral mass is bounded by half
of the full trace norm. In particular this strengthens SWVC08,
arXiv:0705.0292v2, Eq. (eps-lower), for two normalized density matrices. -/
theorem PosSemidef.sum_descEigenvalue_tail_le_half_traceNorm
    (hρ : ρ.PosSemidef) (hσ : σ.IsHermitian) (hrank : σ.rank ≤ k)
    (htrace : ρ.trace = σ.trace) :
    ∑ i ∈ Finset.Ico k n, hρ.isHermitian.descEigenvalue i ≤ traceNorm (ρ - σ) / 2 := by
  have htail := tail_le_posPart hρ hσ hrank
  simpa only [(re_trace_posPart_eq_traceDistance hρ.isHermitian hσ htrace).1,
    traceDistance_eq_traceNorm] using htail

/-- Ordered spectral tails are Lipschitz in trace distance on Hermitian matrices
of equal trace, for arbitrary finite index types. This is the spectral estimate
used in SWVC08, arXiv:0705.0292v2, lines 539–559. -/
theorem IsHermitian.sum_descEigenvalue_tail_le_add_traceDistance
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (htrace : ρ.trace = σ.trace) (k : ℕ) :
    ∑ i ∈ Finset.Ico k (Fintype.card ι), hρ.descEigenvalue i ≤
      (∑ i ∈ Finset.Ico k (Fintype.card ι), hσ.descEigenvalue i) + traceDistance ρ σ := by
  by_cases hk : k < Fintype.card ι
  · obtain ⟨P, hPh, hPi, hPtr, hPσ⟩ := hσ.exists_isProj_trace_eq_kyFanNorm k
    have hPρ := hρ.trace_mul_re_le_kyFanNorm (by simpa using hk) hPh hPi
      (by simpa only [Fintype.card_fin, min_eq_left (Nat.cast_le.mpr hk.le :
        (k : ℝ) ≤ Fintype.card ι)] using hPtr)
    have hP : IsStarProjection P := ⟨hPi, hPh⟩
    have hbound := trace_effect_le_posPart (hρ.sub hσ)
      (nonneg_iff_posSemidef.mp hP.one_sub.nonneg)
      (sub_le_self _ hP.nonneg)
    simp only [sub_mul, one_mul, mul_sub, trace_sub, Complex.sub_re, htrace,
      (re_trace_posPart_eq_traceDistance hρ hσ htrace).1,
      hPσ] at hbound
    have hsum (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
        (∑ i ∈ Finset.range (Fintype.card ι), hA.descEigenvalue i) = A.trace.re := by
      simpa only [Fintype.card_fin, IsHermitian.kyFanNorm] using
        hA.kyFanNorm_card_eq_trace_re
    rw [Finset.sum_Ico_eq_sub _ hk.le, Finset.sum_Ico_eq_sub _ hk.le,
      hsum ρ hρ, hsum σ hσ, htrace]
    simp only [IsHermitian.kyFanNorm] at hPρ hbound
    linarith
  · simpa [Finset.Ico_eq_empty_of_le (Nat.le_of_not_gt hk)] using
      traceDistance_nonneg ρ σ

/-- The spectral mass omitted by a Ky-Fan sum is stable under trace distance,
including indices at or beyond the dimension. -/
theorem IsHermitian.trace_sub_kyFanNorm_le_add_traceDistance
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (htrace : ρ.trace = σ.trace) (k : ℕ) :
    ρ.trace.re - hρ.kyFanNorm k ≤
      σ.trace.re - hσ.kyFanNorm k + traceDistance ρ σ := by
  by_cases hk : k ≤ Fintype.card ι
  · have h := hρ.sum_descEigenvalue_tail_le_add_traceDistance hσ htrace k
    rw [Finset.sum_Ico_eq_sub _ hk, Finset.sum_Ico_eq_sub _ hk] at h
    change hρ.kyFanNorm (Fintype.card ι) - hρ.kyFanNorm k ≤
      hσ.kyFanNorm (Fintype.card ι) - hσ.kyFanNorm k + traceDistance ρ σ at h
    simpa only [hρ.kyFanNorm_card_eq_trace_re, hσ.kyFanNorm_card_eq_trace_re] using h
  · rw [hρ.kyFanNorm_eq_trace_re_of_card_le (by omega),
      hσ.kyFanNorm_eq_trace_re_of_card_le (by omega)]
    simpa using traceDistance_nonneg ρ σ

/-- Ordered spectral tails are Lipschitz in the half-trace norm on Hermitian
matrices of equal trace. For density matrices this supplies the spectral
estimate needed for the smoothing argument in SWVC08, arXiv:0705.0292v2,
lines 539–559. -/
theorem IsHermitian.sum_descEigenvalue_tail_le_add_half_traceNorm
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (htrace : ρ.trace = σ.trace) (k : ℕ) :
    ∑ i ∈ Finset.Ico k n, hρ.descEigenvalue i ≤
      (∑ i ∈ Finset.Ico k n, hσ.descEigenvalue i) + traceNorm (ρ - σ) / 2 := by
  simpa only [Fintype.card_fin, traceDistance_eq_traceNorm] using
    hρ.sum_descEigenvalue_tail_le_add_traceDistance hσ htrace k

/-- Trace distance is half the full nuclear norm, independently of coordinates. -/
theorem traceDistance_eq_rectangularTraceNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    traceDistance ρ σ = rectangularTraceNorm (ρ - σ) / 2 := by
  have h := traceDistance_submatrix_equiv (Fintype.equivFin ι).symm hρ hσ
  rw [← h, traceDistance_eq_traceNorm, ← rectangularTraceNorm_square]
  exact congrArg (fun x : ℝ ↦ x / 2)
    (rectangularTraceNorm_reindex (Fintype.equivFin ι) (Fintype.equivFin ι) (ρ - σ))

end Matrix
