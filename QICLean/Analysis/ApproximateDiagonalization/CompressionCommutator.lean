/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ApproximateDiagonalization.OffDiagonalFamily
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Commutators under orthogonal compression

Both cross terms of the compression identity are retained. This is the
refinement estimate in Hastings, arXiv:cond-mat/0508554v3, lines 1695–1708.

**Local fix (compression cross terms):** these estimates retain both products
through the discarded subspace. Repeated refinement consequently weakens
the decay rate; see `docs/paper-gaps/hastings05_basis_refinement.tex`.
-/

open scoped InnerProductSpace

namespace ApproximateDiagonalization


section Compression

variable {A : Type*} [NormedRing A]

/-- The commutator of two compressions includes two cross terms.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem commutator_compression_eq (P B C : A) (hP : P * P = P) :
    P * B * P * (P * C * P) - P * C * P * (P * B * P) =
      P * (B * C - C * B) * P -
        (P * B * (1 - P)) * ((1 - P) * C * P) +
        (P * C * (1 - P)) * ((1 - P) * B * P) := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hP]
  have h1 : P * B * P * (P * C * P) = P * B * (P * P) * C * P := by
    simp only [mul_assoc]
  have h2 : P * C * P * (P * B * P) = P * C * (P * P) * B * P := by
    simp only [mul_assoc]
  rw [h1, h2, hP]
  have h3 : (P * B * (1 - P)) * ((1 - P) * C * P) =
      P * B * ((1 - P) * (1 - P)) * C * P := by simp only [mul_assoc]
  have h4 : (P * C * (1 - P)) * ((1 - P) * B * P) =
      P * C * ((1 - P) * (1 - P)) * B * P := by simp only [mul_assoc]
  rw [h3, h4, hQ]
  noncomm_ring

/-- A contraction compression does not increase the operator norm.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_compression_le (P B : A) (hP : ‖P‖ ≤ 1) : ‖P * B * P‖ ≤ ‖B‖ := by
  calc ‖P * B * P‖ ≤ ‖P‖ * ‖B‖ * ‖P‖ := norm_mul₃_le
    _ ≤ 1 * ‖B‖ * 1 := by gcongr
    _ = ‖B‖ := by ring

/-- A scalar centre contributes no cross-block operator. The hypothesis `P c Q = 0`
is satisfied by scalar multiples of the identity for orthogonal projections.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_crossBlock_le_of_center (P Q B c : A) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hc : P * c * Q = 0) {ρ : ℝ} (hB : ‖B - c‖ ≤ ρ) : ‖P * B * Q‖ ≤ ρ := by
  have hid : P * (B - c) * Q = P * B * Q := by
    rw [mul_sub, sub_mul, hc, sub_zero]
  rw [← hid]
  calc ‖P * (B - c) * Q‖ ≤ ‖P‖ * ‖B - c‖ * ‖Q‖ := norm_mul₃_le
    _ ≤ 1 * ‖B - c‖ * 1 := by gcongr
    _ ≤ ρ := by simpa using hB

/-- The two cross terms bound the change in a compressed commutator.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_commutator_compression_le (P B C : A) (hPP : P * P = P)
    (hP : ‖P‖ ≤ 1) :
    ‖P * B * P * (P * C * P) - P * C * P * (P * B * P)‖ ≤
      ‖B * C - C * B‖ + ‖P * B * (1 - P)‖ * ‖(1 - P) * C * P‖ +
        ‖P * C * (1 - P)‖ * ‖(1 - P) * B * P‖ := by
  rw [commutator_compression_eq P B C hPP]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add (norm_compression_le _ _ hP) (norm_mul_le _ _)))
    (norm_mul_le _ _))

end Compression

/-- Combining a spectral-spread bound and a commutator bound eliminates the spread
from the cross-block estimate. Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem le_sqrt_mul_of_le_spread {x ρ C f : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hf : 0 ≤ f) (hspread : x ≤ ρ) (hcomm : ρ * x ≤ C * f ^ 2) :
    x ≤ Real.sqrt C * f := by
  have hsq : x ^ 2 ≤ (Real.sqrt C * f) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
    nlinarith [mul_le_mul_of_nonneg_right hspread hx]
  exact (pow_le_pow_iff_left₀ hx (mul_nonneg (Real.sqrt_nonneg _) hf) two_ne_zero).mp hsq

/-- The triangle inequality preserves exponential decay through the anchor of a split.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem exp_dist_half_mul_le {ι : Type*} [PseudoMetricSpace ι] {γ : ℝ}
    (hγ : 0 ≤ γ) (i j k : ι) :
    Real.exp (-(γ * dist i j) / 2) * Real.exp (-(γ * dist j k) / 2) ≤
      Real.exp (-(γ * dist i k) / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left (dist_triangle i j k) hγ]

/-- Compressing after a spectral split preserves a uniform exponential commutator
estimate, with half the decay rate. The two displayed cross-block estimates are the
inputs supplied by the spectral-spread and spectral-gap bounds.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_commutator_compression_le_exp {A ι : Type*} [NormedRing A]
    [PseudoMetricSpace ι] (P : A) (hPP : P * P = P) (hP : ‖P‖ ≤ 1)
    (B : ι → A) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {C D γ : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hγ : 0 ≤ γ) (j : ι)
    (hcomm : ∀ i k, ‖B i * B k - B k * B i‖ ≤
      C * w i * w k * Real.exp (-(γ * dist i k)))
    (hcross : ∀ i, ‖P * B i * (1 - P)‖ ≤
      D * w i * Real.exp (-(γ * dist i j) / 2))
    (hcross' : ∀ i, ‖(1 - P) * B i * P‖ ≤
      D * w i * Real.exp (-(γ * dist i j) / 2)) (i k : ι) :
    ‖P * B i * P * (P * B k * P) - P * B k * P * (P * B i * P)‖ ≤
      (C + 2 * D ^ 2) * w i * w k * Real.exp (-(γ * dist i k) / 2) := by
  have hprod (a b : ι) :
      ‖P * B a * (1 - P)‖ * ‖(1 - P) * B b * P‖ ≤
        D ^ 2 * w a * w b * Real.exp (-(γ * dist a b) / 2) := by
    have hwa := hw a
    have hwb := hw b
    calc
      _ ≤ (D * w a * Real.exp (-(γ * dist a j) / 2)) *
          (D * w b * Real.exp (-(γ * dist b j) / 2)) :=
        mul_le_mul (hcross a) (hcross' b) (norm_nonneg _) (by positivity)
      _ = (D ^ 2 * w a * w b) *
          (Real.exp (-(γ * dist a j) / 2) * Real.exp (-(γ * dist j b) / 2)) := by
        rw [dist_comm b j]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exp_dist_half_mul_le hγ a j b) (by positivity)
  have hwi := hw i
  have hwk := hw k
  have hdecay : Real.exp (-(γ * dist i k)) ≤ Real.exp (-(γ * dist i k) / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hγ (dist_nonneg (x := i) (y := k))]
  have hc := (hcomm i k).trans
    (mul_le_mul_of_nonneg_left hdecay (by positivity : 0 ≤ C * w i * w k))
  have h1 := hprod i k
  have h2 := hprod k i
  rw [dist_comm k i] at h2
  exact (norm_commutator_compression_le P (B i) (B k) hPP hP).trans (by nlinarith)

/-- Compression preserves a symmetric decay kernel after taking its square root.
The multiplicative triangle inequality also covers disconnected graph metrics.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_commutator_compression_le_kernel {A ι : Type*} [NormedRing A]
    (P : A) (hPP : P * P = P) (hP : ‖P‖ ≤ 1) (B : ι → A)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (f : ι → ι → ℝ)
    (hf0 : ∀ i k, 0 ≤ f i k) (hf1 : ∀ i k, f i k ≤ 1)
    (hsymm : ∀ i k, f i k = f k i)
    (htriangle : ∀ i j k, f i j * f j k ≤ f i k) (j : ι)
    (hcomm : ∀ i k, ‖B i * B k - B k * B i‖ ≤ C * f i k)
    (hcross : ∀ i, ‖P * B i * (1 - P)‖ ≤ D * Real.sqrt (f i j))
    (hcross' : ∀ i, ‖(1 - P) * B i * P‖ ≤ D * Real.sqrt (f i j)) (i k : ι) :
    ‖P * B i * P * (P * B k * P) - P * B k * P * (P * B i * P)‖ ≤
      (C + 2 * D ^ 2) * Real.sqrt (f i k) := by
  have hprod (a b : ι) :
      ‖P * B a * (1 - P)‖ * ‖(1 - P) * B b * P‖ ≤
        D ^ 2 * Real.sqrt (f a b) := by
    calc
      _ ≤ (D * Real.sqrt (f a j)) * (D * Real.sqrt (f b j)) :=
        mul_le_mul (hcross a) (hcross' b) (norm_nonneg _) (by positivity)
      _ = D ^ 2 * Real.sqrt (f a j * f j b) := by
        rw [hsymm b j, Real.sqrt_mul (hf0 a j)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (htriangle a j b)) (sq_nonneg D)
  have hc := (hcomm i k).trans
    (mul_le_mul_of_nonneg_left (Real.le_sqrt_self_iff.mpr (hf1 i k)) hC)
  have h1 := hprod i k
  have h2 := hprod k i
  rw [hsymm k i] at h2
  exact (norm_commutator_compression_le P (B i) (B k) hPP hP).trans (by nlinarith)


end ApproximateDiagonalization
