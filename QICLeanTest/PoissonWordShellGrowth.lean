/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordShellGrowth

/-! Empty event families and empty initial support for the constructed shell dynamics. -/

open MeasureTheory PoissonWord
open scoped BigOperators ENNReal NNReal

namespace PoissonWordShellGrowthTest

open Classical in
example {κ : Type*} [Fintype κ] [PseudoEMetricSpace κ]
    (T : ℝ≥0) (f : Word (Fin 0) → κ → ℝ) (S : Set κ) {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ u y, 0 ≤ f u y)
    (h0 : ∀ y, f nil y ≤ M * S.indicator (fun _ ↦ (1 : ℝ)) y) (y : κ) :
    Integrable (fun u ↦ f u y) (measure (Fin 0) T) ∧
      (∫ u, f u y ∂measure (Fin 0) T) ≤
        M * Metric.exponentialDistanceProfile S (1 / 4) 1 y := by
  have h := integrable_and_integral_le_of_shell_growth T f
    (fun i : Fin 0 ↦ (Fin.elim0 i : κ)) S
    (C := 1) (c := 1) (α := 1) (B := 0) (V := 0)
    (by norm_num) (by norm_num) (by norm_num) le_rfl le_rfl le_rfl hM hf h0
    (fun _ _ ↦ by simp [Metric.stretchedBallKernel, Metric.ballIncidenceKernel])
    (fun _ _ ↦ by simp) (fun _ i ↦ Fin.elim0 i)
  convert (h.2.2.1 y) using 1
  norm_num

-- The actual geometric hypotheses suffice; no row or profile inequality is supplied.
open Classical in
example {ι κ : Type*} [Fintype ι] [Fintype κ] [PseudoEMetricSpace κ]
    (f : Word ι → κ → ℝ) (anchor : ι → κ) {C c α B V : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hf : ∀ u y, 0 ≤ f u y)
    (h0 : ∀ y, f nil y ≤ 0)
    (hs : ∀ u y, (∑ i : ι, (f (append u (singleton i)) y - f u y)) ≤
      ∑ z : κ, Metric.stretchedBallKernel anchor C c α y z * f u z)
    (hlabels : ∀ (n : ℕ) (y : κ),
      ((Finset.univ.filter fun i : ι ↦ edist y (anchor i) ≤ (n : ℝ≥0)).card : ℝ) ≤
        B * (1 + (n : ℝ)) ^ 2)
    (hballs : ∀ (n : ℕ) (i : ι),
      ((Finset.univ.filter fun z : κ ↦ edist z (anchor i) ≤ (n : ℝ≥0)).card : ℝ) ≤
        V * (1 + (n : ℝ)) ^ 2) (y : κ) (u : Word ι) : f u y = 0 := by
  have h := integrable_and_integral_le_of_shell_growth (0 : ℝ≥0) f anchor ∅
    hC hc hα hα₁ hB hV (M := 1) zero_le_one hf
    (fun z ↦ by simpa using h0 z) hs hlabels hballs
  exact h.2.2.2 y (by simp) u

end PoissonWordShellGrowthTest
