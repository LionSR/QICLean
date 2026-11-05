/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceBootstrap

/-!
# A uniform polynomial threshold for the half-size sampling failure

The existing corrected bootstrap failure is polynomially small in the
length once the input dimension exceeds a fixed polynomial
threshold. The coefficient is selected before the target dimension,
length and input dimension. The sample remains the actual
natural quotient by twice the square of the family parameter.

This is a sufficient numerical auxiliary for ALVV,
arXiv:1602.08828v2, `eq:bootstrap-cond-dg` and `l:rs`, lines
530–558 and 1065–1074. It does not assert the printed logarithmic
threshold or a probability estimate for an adaptive construction.

**Local fix (complex sphere net count):** The existing failure retains the
corrected complex-sphere exponent and net scale documented in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

namespace Submodule

/-- For every positive error coefficient and natural length exponent,
a single natural threshold coefficient gives the requested decay for
all subsequent target dimensions, lengths and input dimensions.
This is a sufficient numerical auxiliary for ALVV,
arXiv:1602.08828v2, `eq:bootstrap-cond-dg`, lines 1065–1074.
The target dimension and length may be zero, and the error coefficient
is not required to be at most one. -/
theorem exists_bootstrapFailure_polynomial_threshold
    (D a : ℕ) (hD : 2 ≤ D) (eta : ℝ) (heta : 0 < eta) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ r N Q : ℕ,
      K * (r + 1) * (N + 2) ^ 2 ≤ Q →
      4 * D ^ 2 ≤ Q ∧ bootstrapFailure D Q r ≤ eta / ((N : ℝ) + 2) ^ a := by
  let K := max (D ^ 24)
    ⌈128 * (D : ℝ) ^ 2 * ((a : ℝ) + |Real.log eta| + 1)⌉₊
  have hD1 : 1 ≤ D := by omega
  have hD0 : 0 < D := by omega
  have hDR : 0 < (D : ℝ) := Nat.cast_pos.mpr hD0
  have hden : 0 < 128 * (D : ℝ) ^ 2 := by positivity
  have hKD : D ^ 24 ≤ K := le_max_left _ _
  have hK : 128 * (D : ℝ) ^ 2 * ((a : ℝ) + |Real.log eta| + 1) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  refine ⟨K, (one_le_pow₀ hD1).trans hKD, ?_⟩
  intro r N Q hQ
  have hr : max 1 r ≤ r + 1 := max_le (by omega) (by omega)
  have hXnat : 1 ≤ (N + 2) ^ 2 := one_le_pow₀ (by omega)
  have hQrank : max 1 r * D ^ 24 ≤ Q := by
    calc
      max 1 r * D ^ 24 ≤ (r + 1) * K := Nat.mul_le_mul hr hKD
      _ = K * (r + 1) := Nat.mul_comm _ _
      _ = K * (r + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ K * (r + 1) * (N + 2) ^ 2 := Nat.mul_le_mul_left _ hXnat
      _ ≤ Q := hQ
  have hD24Q : D ^ 24 ≤ Q := by
    calc
      D ^ 24 ≤ max 1 r * D ^ 24 := by
        simpa only [one_mul] using Nat.mul_le_mul_right (D ^ 24) (le_max_left 1 r)
      _ ≤ Q := hQrank
  have hD4 : 4 * D ^ 2 ≤ D ^ 24 := by
    calc
      4 * D ^ 2 ≤ D ^ 2 * D ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hD 2)
      _ = D ^ 4 := by ring
      _ ≤ D ^ 24 := pow_le_pow_right₀ hD1 (by decide)
  refine ⟨hD4.trans hD24Q, ?_⟩
  let X := (N : ℝ) + 2
  have hNR : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hX : 2 ≤ X := by dsimp only [X]; linarith only [hNR]
  have hX0 : 0 < X := by linarith only [hX]
  have hXsq : 1 ≤ X ^ 2 := by nlinarith only [hX, sq_nonneg (X - 1)]
  have hlogX : Real.log X ≤ X ^ 2 := by
    nlinarith only [Real.log_le_sub_one_of_pos hX0, hX, sq_nonneg (X - 1)]
  have hQreal : (K : ℝ) * ((r : ℝ) + 1) * X ^ 2 ≤ (Q : ℝ) := by
    change (K : ℝ) * ((r : ℝ) + 1) * ((N : ℝ) + 2) ^ 2 ≤ (Q : ℝ)
    exact_mod_cast hQ
  have hQscale : (K : ℝ) * X ^ 2 ≤ (Q : ℝ) := by
    have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have hrR : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith only [hr0]
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrR (Nat.cast_nonneg K)) (sq_nonneg X)
    have hstep : (K : ℝ) * X ^ 2 ≤ (K : ℝ) * ((r : ℝ) + 1) * X ^ 2 := by
      simpa only [mul_one] using hmul
    exact hstep.trans hQreal
  have hcost : (a : ℝ) * Real.log X + |Real.log eta| ≤
      ((a : ℝ) + |Real.log eta| + 1) * X ^ 2 := by
    have ha := mul_le_mul_of_nonneg_left hlogX (Nat.cast_nonneg a)
    have he := mul_le_mul_of_nonneg_left hXsq (abs_nonneg (Real.log eta))
    nlinarith only [ha, he, sq_nonneg X]
  have hbudget : (a : ℝ) * Real.log X + |Real.log eta| ≤
      (Q : ℝ) / (128 * (D : ℝ) ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    calc
      ((a : ℝ) * Real.log X + |Real.log eta|) * (128 * (D : ℝ) ^ 2) =
          (128 * (D : ℝ) ^ 2) * ((a : ℝ) * Real.log X + |Real.log eta|) := mul_comm _ _
      _ ≤ (128 * (D : ℝ) ^ 2) *
          (((a : ℝ) + |Real.log eta| + 1) * X ^ 2) :=
        mul_le_mul_of_nonneg_left hcost hden.le
      _ = (128 * (D : ℝ) ^ 2 * ((a : ℝ) + |Real.log eta| + 1)) * X ^ 2 := by ring
      _ ≤ (K : ℝ) * X ^ 2 := mul_le_mul_of_nonneg_right hK (sq_nonneg X)
      _ ≤ Q := hQscale
  calc
    bootstrapFailure D Q r ≤ Real.exp (-(Q : ℝ) / (128 * (D : ℝ) ^ 2)) :=
      bootstrapFailure_le_exp_neg_of_ge_mul_pow D r Q hD hQrank
    _ ≤ Real.exp (Real.log eta - (a : ℝ) * Real.log X) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      linarith only [hbudget, neg_le_abs (Real.log eta)]
    _ = eta / X ^ a := by
      rw [Real.exp_sub, Real.exp_log heta, Real.exp_nat_mul, Real.exp_log hX0]

end Submodule
