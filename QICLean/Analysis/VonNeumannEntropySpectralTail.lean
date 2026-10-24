/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProbabilityEntropyConcentration
import QICLean.Analysis.Entropy
import QICLean.Analysis.SpectralTailTraceNorm
import QICLean.Analysis.RectangularTraceNormAlgebra

/-!
# Von Neumann entropy from a spectral tail

Concentration of the ordered spectrum on its first `D` eigenvalues bounds the
entropy by `log D + ε * log dim + log 2`, where `ε` bounds the omitted mass.
The rank budget is unrestricted, including zero and values above the dimension.

Combining this estimate with the trace-norm spectral-tail bound gives an
auxiliary entropy bound for approximation by an arbitrary Hermitian matrix of
rank at most `D`. The approximant need not have trace one or be positive.
This auxiliary bound has the full trace-error coefficient; it does not assert
the sharper pure-state coefficient in Schuch–Wolf–Verstraete–Cirac,
arXiv:0705.0292v2, lines 278–305.
-/

open scoped ComplexOrder

namespace Matrix

/-- An ordered spectral tail of mass at most `ε` bounds von Neumann entropy.
This finite-dimensional concentration estimate is an auxiliary ingredient for
SWVC08, arXiv:0705.0292v2, lines 278–305. The rank budget may be zero or exceed
the dimension, with the convention `Real.log 0 = 0`. -/
theorem PosSemidef.vonNeumannEntropy_le_log_rank_add_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) {D : ℕ} {ε : ℝ}
    (htail : ∑ i ∈ Finset.Ico D (Fintype.card ι), hρ.isHermitian.descEigenvalue i ≤ ε) :
    vonNeumannEntropy ρ hρ.isHermitian ≤ Real.log D +
      ε * Real.log (Fintype.card ι) + Real.log 2 := by
  rw [vonNeumannEntropy_eq_probabilityEntropy_eigenvalues₀]
  let p := hρ.isHermitian.eigenvalues₀
  have hdesc (i : Fin (Fintype.card ι)) :
      hρ.isHermitian.descEigenvalue i.val = p i := by
    simp only [IsHermitian.descEigenvalue, dite_eq_left i.isLt, p]
  have hp (i) : 0 ≤ p i := by
    rw [← hdesc i]
    exact hρ.descEigenvalue_nonneg i.val
  have hsum : ∑ i, p i = 1 := by
    simp_rw [← hdesc]
    rw [Fin.sum_univ_eq_sum_range, hρ.isHermitian.sum_descEigenvalue_card]
    exact posSemidef_trace_one_eigenvalues_sum_one hρ hρ1
  let s := Finset.univ.filter (fun i : Fin (Fintype.card ι) => i.val < D)
  have ht : ∑ i ∈ sᶜ, p i ≤ ε := by
    simp only [s, Finset.compl_filter, not_lt]
    simp_rw [← hdesc, Finset.sum_filter]
    rw [Fin.sum_univ_eq_sum_range (fun j => if D ≤ j then hρ.isHermitian.descEigenvalue j else 0)]
    have hset : (Finset.range (Fintype.card ι)).filter (fun j => D ≤ j) =
        Finset.Ico D (Fintype.card ι) := by
      ext j
      simp [and_comm]
    simpa only [← Finset.sum_filter, hset] using htail
  have hb := Entropy.probabilityEntropy_le_log_card_add_tail p hp hsum s ht
  have hc : Real.log s.card ≤ Real.log D := by
    rcases Nat.eq_zero_or_pos s.card with hz | hz
    · simpa only [hz, Nat.cast_zero, Real.log_zero] using Real.log_natCast_nonneg D
    · apply Real.log_le_log (by exact_mod_cast hz)
      exact_mod_cast (show s.card ≤ D by
        simpa only [s, Fin.card_filter_val_lt] using min_le_right (Fintype.card ι) D)
  simp only [Fintype.card_fin] at hb
  exact hb.trans (add_le_add (add_le_add hc le_rfl) le_rfl)

/-- Auxiliary entropy estimate from a low-rank Hermitian approximation.
The error is the full trace norm. This is weaker than the pure-state coefficient
in SWVC08, arXiv:0705.0292v2, lines 278–305; no normalization of the approximant
is required. -/
theorem PosSemidef.vonNeumannEntropy_le_log_rank_add_traceNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ : σ.IsHermitian)
    {D : ℕ} (hrank : σ.rank ≤ D) {δ : ℝ}
    (herror : rectangularTraceNorm (ρ - σ) ≤ δ) :
    vonNeumannEntropy ρ hρ.isHermitian ≤ Real.log D +
      δ * Real.log (Fintype.card ι) + Real.log 2 := by
  let e := Fintype.equivFin ι
  have hr := hρ.submatrix e.symm
  have he : traceNorm (ρ.submatrix e.symm e.symm - σ.submatrix e.symm e.symm) ≤ δ := by
    change rectangularTraceNorm (reindex e e (ρ - σ)) ≤ δ
    simpa only [rectangularTraceNorm_reindex] using herror
  have ht := (hr.sum_descEigenvalue_tail_le_traceNorm (hσ.submatrix e.symm)
    (by simpa only [rank_submatrix] using hrank)).trans he
  have hb := hr.vonNeumannEntropy_le_log_rank_add_tail
    (by simpa only [trace_submatrix_equiv] using hρ1) (by simpa using ht)
  rw [vonNeumannEntropy_submatrix_equiv e.symm ρ hρ.isHermitian] at hb
  simpa only [Fintype.card_fin] using hb

end Matrix
