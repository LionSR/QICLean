/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordMarked

/-!
# Weighted growth of observables on Poisson words

A nonnegative kernel controls the sum of the increments obtained by appending
one letter. If a nonnegative profile is a supersolution for that kernel with
rate `v`, the sums over words of length `m` grow at most as `(N + v) ^ m`, where
`N` is the alphabet size. Summing against the actual Poisson-word weights then
proves integrability and bounds the expectation by the initial profile times
`exp (v * t)`. Profile entries may vanish.

This is the generic stochastic growth estimate underlying the weighted
oscillation argument in the amplification source, `09-amplification.tex`,
lines 159–188. The application-specific oscillation, spatial profile, and
chronological clock construction are not hypotheses proved in this module.
-/

open MeasureTheory
open scoped BigOperators NNReal

namespace PoissonWord

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Summing over words of successor length is summing over every actual prefix
and every letter appended on the right. -/
lemma sum_length_succ (f : Word ι → ℝ) (m : ℕ) :
    (∑ w : Fin (m + 1) → ι, f ⟨m + 1, w⟩) =
      ∑ u : Fin m → ι, ∑ i : ι, f (append ⟨m, u⟩ (singleton i)) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (m + 1) ↦ ι)).sum_comp
    (fun w ↦ f ⟨m + 1, w⟩), Fintype.sum_prod_type, Finset.sum_comm]
  simp only [append, singleton, Fin.append_right_eq_snoc]
  rfl

/-- An upper bound on the summed one-letter increments gives a recurrence for
the actual finite-length word sums. -/
lemma sum_length_succ_le_of_append_singleton (f : Word ι → κ → ℝ)
    (A : κ → κ → ℝ)
    (hstep : ∀ u y, (∑ i : ι, (f (append u (singleton i)) y - f u y)) ≤
      ∑ z : κ, A y z * f u z) (m : ℕ) (y : κ) :
    (∑ w : Fin (m + 1) → ι, f ⟨m + 1, w⟩ y) ≤
      (Fintype.card ι : ℝ) * (∑ u : Fin m → ι, f ⟨m, u⟩ y) +
        ∑ z : κ, A y z * (∑ u : Fin m → ι, f ⟨m, u⟩ z) := by
  rw [sum_length_succ (fun w ↦ f w y) m]
  calc
    _ ≤ ∑ u : Fin m → ι,
        ((Fintype.card ι : ℝ) * f ⟨m, u⟩ y + ∑ z : κ, A y z * f ⟨m, u⟩ z) := by
      apply Finset.sum_le_sum
      intro u _
      have h := hstep ⟨m, u⟩ y
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul] at h
      linarith
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]

/-- A weighted kernel supersolution bounds the sum over all words of each
length. No division by the profile occurs, so zero entries are allowed. -/
theorem sum_length_le_pow_of_weighted_growth (f : Word ι → κ → ℝ)
    (A : κ → κ → ℝ) (r : κ → ℝ) {v C : ℝ}
    (hA : ∀ y z, 0 ≤ A y z) (hv : 0 ≤ v) (hC : 0 ≤ C)
    (hinitial : ∀ y, f nil y ≤ C * r y)
    (hstep : ∀ u y, (∑ i : ι, (f (append u (singleton i)) y - f u y)) ≤
      ∑ z : κ, A y z * f u z)
    (hkernel : ∀ y, (∑ z : κ, A y z * r z) ≤ v * r y) (m : ℕ) (y : κ) :
    (∑ w : Fin m → ι, f ⟨m, w⟩ y) ≤
      ((Fintype.card ι : ℝ) + v) ^ m * C * r y := by
  induction m generalizing y with
  | zero =>
      simpa [nil, Subsingleton.elim (default : Fin 0 → ι) Fin.elim0] using hinitial y
  | succ m ih =>
      have hpow : 0 ≤ ((Fintype.card ι : ℝ) + v) ^ m * C := by positivity
      calc
        _ ≤ (Fintype.card ι : ℝ) * (∑ u : Fin m → ι, f ⟨m, u⟩ y) +
            ∑ z : κ, A y z * (∑ u : Fin m → ι, f ⟨m, u⟩ z) :=
          sum_length_succ_le_of_append_singleton f A hstep m y
        _ ≤ (Fintype.card ι : ℝ) *
              (((Fintype.card ι : ℝ) + v) ^ m * C * r y) +
            ∑ z : κ, A y z * (((Fintype.card ι : ℝ) + v) ^ m * C * r z) := by
          exact add_le_add (mul_le_mul_of_nonneg_left (ih y) (Nat.cast_nonneg _))
            (Finset.sum_le_sum fun z _ ↦ mul_le_mul_of_nonneg_left (ih z) (hA y z))
        _ = (((Fintype.card ι : ℝ) + v) ^ m * C) *
              ((Fintype.card ι : ℝ) * r y + ∑ z : κ, A y z * r z) := by
          simp only [Finset.mul_sum, mul_add]
          congr 1
          · ring
          · apply Finset.sum_congr rfl
            intro z _
            ring
        _ ≤ (((Fintype.card ι : ℝ) + v) ^ m * C) *
              ((Fintype.card ι : ℝ) * r y + v * r y) :=
          mul_le_mul_of_nonneg_left (add_le_add_right (hkernel y) _) hpow
        _ = _ := by rw [pow_succ]; ring

/-- For the actual Poisson-word law, nonnegative observables with a weighted
one-letter growth bound are integrable and have the expected exponential bound.
The estimate allows vanishing profile entries and requires no uniform bound on
the observable. -/
theorem integrable_and_integral_le_of_weighted_growth (t : ℝ≥0)
    (f : Word ι → κ → ℝ) (A : κ → κ → ℝ) (r : κ → ℝ) {v C : ℝ}
    (hf : ∀ u y, 0 ≤ f u y) (hA : ∀ y z, 0 ≤ A y z)
    (hr : ∀ y, 0 ≤ r y) (hv : 0 ≤ v) (hC : 0 ≤ C)
    (hinitial : ∀ y, f nil y ≤ C * r y)
    (hstep : ∀ u y, (∑ i : ι, (f (append u (singleton i)) y - f u y)) ≤
      ∑ z : κ, A y z * f u z)
    (hkernel : ∀ y, (∑ z : κ, A y z * r z) ≤ v * r y) (y : κ) :
    Integrable (fun u ↦ f u y) (measure ι t) ∧
      (∫ u, f u y ∂measure ι t) ≤ Real.exp (v * t) * C * r y := by
  have h := integrable_and_integral_le_of_sum_le_pow t (fun u ↦ f u y) (fun u ↦ hf u y)
    (add_nonneg (Nat.cast_nonneg _) hv) (mul_nonneg hC (hr y))
    (fun m ↦ by
      simpa only [mul_assoc] using
        sum_length_le_pow_of_weighted_growth f A r hA hv hC hinitial hstep hkernel m y)
  simpa only [add_sub_cancel_left, ← mul_assoc] using h

/-- A zero profile entry forces the corresponding nonnegative observable to
vanish at every word, including every disconnected component certified by such
a profile. -/
theorem eq_zero_of_weighted_growth_of_profile_eq_zero
    (f : Word ι → κ → ℝ) (A : κ → κ → ℝ) (r : κ → ℝ) {v C : ℝ}
    (hf : ∀ u y, 0 ≤ f u y) (hA : ∀ y z, 0 ≤ A y z)
    (hv : 0 ≤ v) (hC : 0 ≤ C)
    (hinitial : ∀ y, f nil y ≤ C * r y)
    (hstep : ∀ u y, (∑ i : ι, (f (append u (singleton i)) y - f u y)) ≤
      ∑ z : κ, A y z * f u z)
    (hkernel : ∀ y, (∑ z : κ, A y z * r z) ≤ v * r y)
    (y : κ) (hy : r y = 0) (u : Word ι) : f u y = 0 := by
  apply le_antisymm _ (hf u y)
  calc
    f u y ≤ ∑ w : Fin u.1 → ι, f ⟨u.1, w⟩ y :=
      Finset.single_le_sum (fun w _ ↦ hf ⟨u.1, w⟩ y) (Finset.mem_univ u.2)
    _ ≤ ((Fintype.card ι : ℝ) + v) ^ u.1 * C * r y :=
      sum_length_le_pow_of_weighted_growth f A r hA hv hC hinitial hstep hkernel u.1 y
    _ = 0 := by rw [hy, mul_zero]

end PoissonWord
