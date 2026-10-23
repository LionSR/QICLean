/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralTailTraceNorm
import QICLean.Analysis.RectangularTraceNormAlgebra
import QICLean.Entropy.RenyiTail
import QICLean.Entropy.RenyiMassBound
import QICLean.Entropy.Renyi.Defs

/-!
# Rényi lower bounds for low-rank approximation

The order-greater-than-one bound in SWVC08, arXiv:0705.0292v2, lines 333–345,
with the corrected sign of the logarithmic error term. Only the original
positive matrix is normalized; the Hermitian approximant may have arbitrary trace.

**Local fix (error-term sign):** the correction is documented in TNLean’s
[Rényi bond-dimension sign note](https://github.com/LionSR/TNLean/commit/ebf04b6495d29691ddefac5c85dd70ca6ba3bad6#diff-83cdf7e9f9eb1a229f1f7c212c73baa355968807efb4cef898c364519490b75a).
-/

open scoped ComplexOrder

namespace Matrix

/-- A low-rank approximation in full trace norm forces a lower bound on its
rank budget. Source: SWVC08, arXiv:0705.0292v2, Eq. (eps-lower) and lines 333–345,
with the corrected sign of the error term. -/
theorem PosSemidef.renyiEntropy_add_log_error_le_log_rank
    {n D : ℕ} {ρ σ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ : σ.IsHermitian)
    (hrank : σ.rank ≤ D) {α δ : ℝ} (hα : 1 < α) (hδ : δ < 1)
    (herror : traceNorm (ρ - σ) ≤ δ) :
    renyiEntropy ρ hρ.isHermitian α + α / (α - 1) * Real.log (1 - δ) ≤ Real.log D := by
  have htail := (hρ.sum_descEigenvalue_tail_le_traceNorm hσ hrank).trans herror
  let p := hρ.isHermitian.eigenvalues₀
  have hdesc (i : Fin (Fintype.card (Fin n))) :
      hρ.isHermitian.descEigenvalue i.val = p i := by
    simp only [IsHermitian.descEigenvalue, dite_eq_left i.isLt, p]
  have hp (i) : 0 ≤ p i := by
    rw [← hdesc i]
    exact hρ.descEigenvalue_nonneg i.val
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have hsum : ∑ i, p i = 1 := by
    simpa only [← Equiv.sum_comp e, IsHermitian.eigenvalues, e,
      Equiv.symm_apply_apply, p] using posSemidef_trace_one_eigenvalues_sum_one hρ hρ1
  have htail' : ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card (Fin n)) =>
      D ≤ i.val), p i ≤ δ := by
    simp_rw [← hdesc, Finset.sum_filter]
    rw [Fin.sum_univ_eq_sum_range (fun j => if D ≤ j then hρ.isHermitian.descEigenvalue j else 0)]
    have hset : (Finset.range n).filter (fun j => D ≤ j) = Finset.Ico D n := by
      ext j
      simp [and_comm]
    simpa only [Fintype.card_fin, ← Finset.sum_filter, hset] using htail
  let s := Finset.univ.filter (fun i : Fin (Fintype.card (Fin n)) => i.val < D)
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin (Fintype.card (Fin n)) => i.val < D) p
  have hmass : 1 - δ ≤ ∑ i ∈ s, p i := by
    simp only [not_lt, hsum] at hsplit
    dsimp only [s]
    linarith
  have hcard : s.card ≤ D := by
    simpa only [s, Fin.card_filter_val_lt] using (min_le_right (Fintype.card (Fin n)) D)
  have hD : 0 < D := by
    by_contra h
    have hzero : D = 0 := by omega
    simp only [s, hzero, Nat.not_lt_zero, Finset.filter_false, Finset.sum_empty] at hmass
    linarith
  have hbound := Entropy.log_card_bound_of_renyi_mass p hp s hD hcard hα hδ hmass
  simpa only [renyiEntropy, ite_eq_right (show α ≠ 0 by linarith), ite_eq_right (ne_of_gt hα),
    hρ.isHermitian.trace_cfc_eq_sum_eigenvalues₀, p, div_eq_mul_inv, mul_comm] using hbound

/-- The Rényi rank lower bound for an arbitrary finite index set, measured in
full trace norm. Source: SWVC08, arXiv:0705.0292v2, Eq. (eps-lower) and
lines 333–345, with the corrected sign of the error term. -/
theorem PosSemidef.renyiEntropy_add_log_error_le_log_rank_of_rectangularTraceNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ} {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ : σ.IsHermitian)
    (hrank : σ.rank ≤ D) {α δ : ℝ} (hα : 1 < α) (hδ : δ < 1)
    (herror : rectangularTraceNorm (ρ - σ) ≤ δ) :
    renyiEntropy ρ hρ.isHermitian α + α / (α - 1) * Real.log (1 - δ) ≤ Real.log D := by
  let e := Fintype.equivFin ι
  have hr := hρ.submatrix e.symm
  have he : traceNorm (ρ.submatrix e.symm e.symm - σ.submatrix e.symm e.symm) ≤ δ := by
    change rectangularTraceNorm (reindex e e (ρ - σ)) ≤ δ
    simpa only [rectangularTraceNorm_reindex] using herror
  have hb := hr.renyiEntropy_add_log_error_le_log_rank
    (by simpa only [trace_submatrix_equiv] using hρ1) (hσ.submatrix e.symm)
    (by simpa only [rank_submatrix] using hrank) hα hδ he
  simpa only [renyiEntropy, ite_eq_right (show α ≠ 0 by linarith),
    ite_eq_right (ne_of_gt hα), ← IsHermitian.cfc_eq, cfc_submatrix_equiv hρ.isHermitian _ e,
    trace_submatrix_equiv] using hb

end Matrix
