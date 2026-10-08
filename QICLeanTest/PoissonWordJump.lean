/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordJump

/-! Signed integrability, chronological orientation, and degenerate jump consumers. -/

open MeasureTheory PoissonWord
open scoped BigOperators NNReal

namespace PoissonWordJumpTest

-- The algebraic prefix telescope does not require a finite alphabet.
example (f : Word ℕ → ℝ) (w : Word ℕ) :
    (∑ j : Fin w.1, (f (append (take w j) (singleton (w.2 j))) - f (take w j))) =
      f w - f nil := sum_prefix_increment f w

-- Appending the second letter preserves [false,true]; prepending reverses it.
example : List.ofFn (append (singleton false) (singleton true)).2 = [false, true] ∧
    List.ofFn (append (singleton true) (singleton false)).2 ≠ [false, true] := by
  decide

-- A negative kernel has a negative expectation, rather than being clipped to zero.
example {ι : Type*} [Fintype ι] (T : ℝ≥0) :
    (∫ w : Word ι, ∑ _j : Fin w.1, (-1 : ℝ) ∂measure ι T) =
      -((Fintype.card ι : ℝ) * T) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_neg, mul_one]
  rw [integral_neg, integral_length]

-- Genuine integrability is available both before and after time integration.
example {ι : Type*} [Fintype ι] (T : ℝ≥0) (F : Word ι → ι → ℝ) {C : ℝ}
    (hb : ∀ u i, |F u i| ≤ C) :
    Integrable (fun w ↦ ∑ j : Fin w.1, F (take w j) (w.2 j)) (measure ι T) ∧
      IntegrableOn (fun s : ℝ ↦ ∑ i : ι,
        ∫ u, F u i ∂measure ι (Real.toNNReal s)) (Set.Ioc 0 (T : ℝ)) ∧
      (∫ w, ∑ j : Fin w.1, F (take w j) (w.2 j) ∂measure ι T) =
        ∫ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
          ∫ u, F u i ∂measure ι (Real.toNNReal s) :=
  ⟨integrable_sum_prefix_of_abs_le_const T F hb,
    integrableOn_sum_word_integral_of_abs_le_const T F hb,
    integral_sum_prefix_of_abs_le_const T F hb⟩

example (F : Word (Fin 2) → Fin 2 → ℝ) {C : ℝ} (hb : ∀ u i, |F u i| ≤ C) :
    (∫ w, ∑ j : Fin w.1, F (take w j) (w.2 j) ∂measure (Fin 2) 0) = 0 := by
  rw [integral_sum_prefix_of_abs_le_const 0 F hb]
  simp

-- A negative bound is harmless when the label type is empty: its premise is vacuous.
example (T : ℝ≥0) (F : Word (Fin 0) → Fin 0 → ℝ) :
    Integrable (fun w ↦ ∑ j : Fin w.1, F (take w j) (w.2 j)) (measure (Fin 0) T) ∧
      (∫ w, ∑ j : Fin w.1, F (take w j) (w.2 j) ∂measure (Fin 0) T) = 0 := by
  have hb (u) (i : Fin 0) : |F u i| ≤ (-1 : ℝ) := Fin.elim0 i
  refine ⟨integrable_sum_prefix_of_abs_le_const T F hb, ?_⟩
  rw [integral_sum_prefix_of_abs_le_const T F hb]
  simp

example {ι : Type*} [Fintype ι] (T : ℝ≥0) :
    Integrable (fun _w : Word ι ↦ (-7 : ℝ)) (measure ι T) ∧
      (∫ _w : Word ι, (-7 : ℝ) ∂measure ι T) = -7 := by
  refine ⟨integrable_of_abs_le_const T _ (C := 7) (by intros; norm_num), ?_⟩
  simp

-- A pointwise order-sensitive observable catches reversal hidden by symmetric word weights.
example :
    let w : Word Bool := ⟨2, ![false, true]⟩
    let f : Word Bool → ℝ := fun u ↦ if List.ofFn u.2 = [false, true] then 1 else 0
    (∑ j : Fin w.1, (f (append (take w j) (singleton (w.2 j))) - f (take w j))) = 1 := by
  dsimp only
  calc
    _ = (if List.ofFn (![false, true] : Fin 2 → Bool) = [false, true] then 1 else 0) -
        (if List.ofFn (nil : Word Bool).2 = [false, true] then 1 else 0) :=
      sum_prefix_increment (fun u : Word Bool ↦
        if List.ofFn u.2 = [false, true] then 1 else 0) ⟨2, ![false, true]⟩
    _ = 1 := by norm_num [nil, List.ofFn_succ]

-- The empty-word indicator has negative jumps; signed subtraction is essential.
example {ι : Type*} [Fintype ι] (T : ℝ≥0) :
    (∫ w : Word ι, (if w.1 = 0 then (1 : ℝ) else 0) ∂measure ι T) - 1 =
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ _i : ι,
        ∫ u : Word ι, -(if u.1 = 0 then (1 : ℝ) else 0)
          ∂measure ι (Real.toNNReal s) := by
  have hb (u : Word ι) : |if u.1 = 0 then (1 : ℝ) else 0| ≤ 1 := by
    split_ifs <;> norm_num
  simpa [nil] using integral_sub_eq_integral_sum_increment T
    (fun u : Word ι ↦ if u.1 = 0 then (1 : ℝ) else 0) hb

example {ι : Type*} [Fintype ι] (f : Word ι → ℝ) {C : ℝ}
    (hb : ∀ u, |f u| ≤ C) : (∫ w, f w ∂measure ι 0) = f nil := by
  simp

example (T : ℝ≥0) (f : Word (Fin 0) → ℝ) {C : ℝ}
    (hb : ∀ u, |f u| ≤ C) : (∫ w, f w ∂measure (Fin 0) T) = f nil := by
  have h := integral_sub_eq_integral_sum_increment T f hb
  apply sub_eq_zero.mp
  simpa using h

-- Zero increment majorants imply nonincreasing expectation without positivity of f.
example {ι : Type*} [Fintype ι] (T : ℝ≥0) (f : Word ι → ℝ) {C : ℝ}
    (hb : ∀ u, |f u| ≤ C) (hdec : ∀ u i, f (append u (singleton i)) ≤ f u) :
    (∫ w, f w ∂measure ι T) ≤ f nil := by
  simpa using integral_le_add_integral_sum_of_increment_le T f (fun _ _ ↦ 0) hb
    (fun _ _ ↦ le_rfl) (fun _ _ ↦ le_rfl) (fun u i ↦ sub_nonpos.mpr (hdec u i))

end PoissonWordJumpTest
