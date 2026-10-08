/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchurLabelMoments

/-!
# Quantitative transfer of centered surprisal moments to Schur labels

For an actual permutation-invariant density on `k` copies, assume an explicit
quadratic bound for the logarithm of its centered surprisal moment on a
symmetric interval. The positive label moment has the same bound. The negative
label moment has twice the quadratic coefficient and an explicit logarithmic
loss from the polynomial Schur remainder.

This is the conditional scalar transfer in OpenAI's area-law manuscript,
September 24, 2026, `07-comparators.tex`, lines 227–238. The hypothesis is the
centered `k`-copy surprisal estimate. Identifying it with the tensor power of a
marginal and deriving it from the one-copy assumption `comparator:mgf-data`
(lines 75–85) are separate arguments. No label moment bound is assumed.
-/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- A nonzero positive trace weight pairs strictly positively with a Hermitian
exponential; the exponential is positive definite even when the weight is singular. -/
private theorem re_trace_mul_exp_pos {X : Type*} [Fintype X] [DecidableEq X]
    {ρ A : Matrix X X ℂ} (hρ : ρ.PosSemidef) (hne : ρ ≠ 0) (hA : A.IsHermitian) :
    0 < (ρ * NormedSpace.exp A).trace.re := by
  let _ : NormedAlgebra ℚ (Matrix X X ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hp : (NormedSpace.exp A).PosDef :=
    (show IsSelfAdjoint A from hA).exp_nonneg.posSemidef.posDef_iff_isUnit.mpr
      (NormedSpace.isUnit_exp A)
  exact (Complex.pos_iff.mp (hρ.trace_mul_pos_of_ne_zero_of_posDef hne hp)).1

end Matrix

namespace TensorPower

open PermutationRepresentation

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}
  {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}

/-
Provenance-ID: 8753-qic-schur-label-mgf-01
Original formalization, no upstream Lean proof text reused.
Declaration: TensorPower.log_centered_labelEntropy_moments_le
Manuscript: September 24, 2026, comparator:signed-label-moments, lines 227–238.
-/

/-- A centered surprisal logarithmic moment bound transfers to both label signs,
with explicit coefficients and the common range `u ≤ min(c₀,1)/(2√ℬ)`.
This is the conditional transfer in `07-comparators.tex`, lines 227–238;
the assumed moment estimate concerns the actual `k`-copy surprisal, not the label. -/
theorem log_centered_labelEntropy_moments_le (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hinv : ∀ σ, Commute (permOp (copyPerm Ω k) σ) ρ)
    (s C₀ c₀ ℬ : ℝ) (hℬ : 1 ≤ ℬ)
    (hL : ∀ t : ℝ, |t| ≤ c₀ / Real.sqrt ℬ →
      Real.log (ρ * NormedSpace.exp ((t : ℂ) • (-CFC.log ρ - (s : ℂ) • 1))).trace.re ≤
        C₀ * k * ℬ * t ^ 2)
    (u : ℝ) (hu : 0 ≤ u) (hur : u ≤ (min c₀ 1 / 2) / Real.sqrt ℬ) :
    Real.log (ρ * NormedSpace.exp ((u : ℂ) •
      (labelEntropy (copyPerm Ω k) - (s : ℂ) • 1))).trace.re ≤ C₀ * k * ℬ * u ^ 2 ∧
    Real.log (ρ * NormedSpace.exp ((-u : ℂ) •
      (labelEntropy (copyPerm Ω k) - (s : ℂ) • 1))).trace.re ≤
        2 * C₀ * k * ℬ * u ^ 2 + ((Fintype.card Ω : ℝ) ^ 2 / 2) * Real.log (k + 1) := by
  have hsqrt : 1 ≤ Real.sqrt ℬ := (Real.one_le_sqrt).mpr hℬ
  have hsqrtpos : 0 < Real.sqrt ℬ := zero_lt_one.trans_le hsqrt
  have hmul := (le_div_iff₀ hsqrtpos).mp hur
  have hu_mul : u ≤ u * Real.sqrt ℬ := le_mul_of_one_le_right hu hsqrt
  have hsmall : 2 * u ≤ 1 := by linarith [min_le_right c₀ (1 : ℝ)]
  have hdouble : 2 * u ≤ c₀ / Real.sqrt ℬ := by
    apply (le_div_iff₀ hsqrtpos).mpr
    nlinarith [min_le_left c₀ (1 : ℝ)]
  have hplusrange : |u| ≤ c₀ / Real.sqrt ℬ := by
    rw [abs_of_nonneg hu]
    linarith
  have hminusrange : |-2 * u| ≤ c₀ / Real.sqrt ℬ := by
    rw [abs_of_nonpos (by linarith : -2 * u ≤ 0)]
    linarith
  have hne : ρ ≠ 0 := by
    intro hz
    simp [hz] at htr
  have hpos (A : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) (hA : A.IsHermitian) (t : ℝ) :
      0 < (ρ * NormedSpace.exp ((t : ℂ) • (A - (s : ℂ) • 1))).trace.re := by
    apply Matrix.re_trace_mul_exp_pos hρ hne
    apply Matrix.IsHermitian.smul
    · exact hA.sub (Matrix.isHermitian_one.smul
        (by change star (s : ℂ) = (s : ℂ); simp))
    · change star (t : ℂ) = (t : ℂ)
      simp
  have hF := (posSemidef_labelEntropy (copyPerm Ω k)).isHermitian
  have hlog : (-CFC.log ρ).IsHermitian := IsSelfAdjoint.log.neg
  obtain ⟨hplus, hminus⟩ := centered_labelEntropy_moments_le hρ htr hinv s u hu hsmall
  refine ⟨(Real.log_le_log (hpos _ hF u) hplus).trans (hL u hplusrange), ?_⟩
  have hnpos : 0 < (ρ * NormedSpace.exp ((-u : ℂ) •
      (labelEntropy (copyPerm Ω k) - (s : ℂ) • 1))).trace.re := by
    simpa only [Complex.ofReal_neg] using hpos _ hF (-u)
  have hLpos : 0 < (ρ * NormedSpace.exp ((-2 * u : ℂ) •
      (-CFC.log ρ - (s : ℂ) • 1))).trace.re := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat] using
      hpos _ hlog (-2 * u)
  have hpolypos : 0 < ((k : ℝ) + 1) ^ (Fintype.card Ω ^ 2) := by positivity
  have hm := Real.log_le_log hnpos hminus
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hm
  rw [Real.log_sqrt (mul_nonneg hLpos.le hpolypos.le),
    Real.log_mul hLpos.ne' hpolypos.ne', Real.log_pow] at hm
  have hminusL := hL (-2 * u) hminusrange
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat] at hminusL
  calc
    _ ≤ ((Real.log (ρ * NormedSpace.exp ((-2 * u : ℂ) •
          (-CFC.log ρ - (s : ℂ) • 1))).trace.re) +
            (Fintype.card Ω ^ 2 : ℕ) * Real.log ((k : ℝ) + 1)) / 2 := hm
    _ ≤ (C₀ * k * ℬ * (-2 * u) ^ 2 +
            (Fintype.card Ω ^ 2 : ℕ) * Real.log ((k : ℝ) + 1)) / 2 := by gcongr
    _ = _ := by push_cast; ring

/-
Provenance-ID: 8753-qic-schur-label-mgf-02
Original formalization, no upstream Lean proof text reused.
Declaration: TensorPower.log_centered_labelEntropy_moments_uniform
Manuscript: September 24, 2026, comparator:signed-label-moments, lines 227–238.
-/

/-- Both signs satisfy one quadratic-plus-logarithmic bound on the same symmetric
interval. This is the conditional uniform form of `comparator:signed-label-moments`,
`07-comparators.tex`, lines 227–238. Its quadratic coefficient is independent of
the one-copy dimension; that dimension enters only the logarithmic remainder. -/
theorem log_centered_labelEntropy_moments_uniform
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hinv : ∀ σ, Commute (permOp (copyPerm Ω k) σ) ρ)
    (s C₀ c₀ ℬ : ℝ) (hC : 0 ≤ C₀) (hc : 0 < c₀) (hℬ : 1 ≤ ℬ)
    (hL : ∀ t : ℝ, |t| ≤ c₀ / Real.sqrt ℬ →
      Real.log (ρ * NormedSpace.exp ((t : ℂ) • (-CFC.log ρ - (s : ℂ) • 1))).trace.re ≤
        C₀ * k * ℬ * t ^ 2) :
    0 < min c₀ 1 / 2 ∧
      ∀ t : ℝ, |t| ≤ (min c₀ 1 / 2) / Real.sqrt ℬ →
    Real.log (ρ * NormedSpace.exp ((t : ℂ) •
      (labelEntropy (copyPerm Ω k) - (s : ℂ) • 1))).trace.re ≤
        2 * C₀ * k * ℬ * t ^ 2 + ((Fintype.card Ω : ℝ) ^ 2 / 2) * Real.log (k + 1) := by
  refine ⟨div_pos (lt_min hc zero_lt_one) (by norm_num), ?_⟩
  intro t ht
  obtain ⟨hplus, hminus⟩ := log_centered_labelEntropy_moments_le
    hρ htr hinv s C₀ c₀ ℬ hℬ hL |t| (abs_nonneg t) ht
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0] at hplus
    have hquad : 0 ≤ C₀ * k * ℬ * t ^ 2 := by positivity
    have hlog : 0 ≤ Real.log ((k : ℝ) + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hpoly : 0 ≤ ((Fintype.card Ω : ℝ) ^ 2 / 2) * Real.log ((k : ℝ) + 1) :=
      mul_nonneg (by positivity) hlog
    nlinarith
  · simpa only [abs_of_nonpos (le_of_lt (lt_of_not_ge ht0)), Complex.ofReal_neg,
      neg_neg, neg_sq] using hminus

end TensorPower
