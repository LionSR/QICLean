/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordRealOccupation

/-! Real occupation consumers check finite integrals as well as their values. -/

open MeasureTheory PoissonWord
open scoped BigOperators ENNReal NNReal

namespace PoissonWordRealOccupationTest

example {ι : Type*} [Fintype ι] (T : ℝ≥0) :
    Integrable (fun w : Word ι ↦ (w.1 : ℝ)) (measure ι T) ∧
      (∫ w : Word ι, (w.1 : ℝ) ∂measure ι T) = (Fintype.card ι : ℝ) * T :=
  ⟨integrable_length T, integral_length T⟩

-- The sum, every inner expectation, and the time integrand are genuinely integrable.
example {ι : Type*} [Fintype ι] (T : ℝ≥0) (F : Word ι → ι → ℝ) {C : ℝ}
    (hF : ∀ u i, 0 ≤ F u i) (hb : ∀ u i, F u i ≤ C) :
    Integrable (fun w ↦ ∑ j : Fin w.1, F (take w j) (w.2 j)) (measure ι T) ∧
    (∀ s : ℝ, ∀ i, Integrable (F · i) (measure ι (Real.toNNReal s))) ∧
    IntegrableOn (fun s : ℝ ↦ ∑ i : ι, ∫ u, F u i ∂measure ι (Real.toNNReal s))
      (Set.Ioc 0 (T : ℝ)) ∧
    (∫ w, ∑ j : Fin w.1, F (take w j) (w.2 j) ∂measure ι T) =
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
        ∫ u, F u i ∂measure ι (Real.toNNReal s) :=
  ⟨integrable_sum_prefix T F hF hb,
    fun _s i ↦ integrable_of_nonneg_le_const _ _ (hF · i) (hb · i),
    integrableOn_sum_word_integral T Finset.univ F hF hb,
    integral_sum_prefix T F hF hb⟩

example {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] (T : ℝ≥0)
    (F : Word {i // p i} → ι → ℝ) {C : ℝ}
    (hF : ∀ u i, 0 ≤ F u i) (hb : ∀ u i, F u i ≤ C) :
    Integrable (fun w ↦ ∑ j : Fin w.1,
      F (partitionWords p (take w j)).1 (w.2 j)) (measure ι T) ∧
    IntegrableOn (fun s : ℝ ↦ ∑ i : ι,
      ∫ u, F u i ∂measure {i // p i} (Real.toNNReal s)) (Set.Ioc 0 (T : ℝ)) ∧
    (∫ w, ∑ j : Fin w.1, F (partitionWords p (take w j)).1 (w.2 j) ∂measure ι T) =
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
        ∫ u, F u i ∂measure {i // p i} (Real.toNNReal s) :=
  ⟨integrable_sum_partition_prefix p T F hF hb,
    integrableOn_sum_word_integral T Finset.univ F hF hb,
    integral_sum_partition_prefix p T F hF hb⟩

example {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] (T : ℝ≥0)
    (F : Word {i // p i} → ι → ℝ) {C : ℝ}
    (hF : ∀ u i, 0 ≤ F u i) (hb : ∀ u i, F u i ≤ C) :
    Integrable (fun w ↦ ∑ j : Fin w.1,
      if p (w.2 j) then 0 else F (partitionWords p (take w j)).1 (w.2 j))
      (measure ι T) ∧
    IntegrableOn (fun s : ℝ ↦ ∑ i ∈ Finset.univ.filter (fun i ↦ ¬p i),
      ∫ u, F u i ∂measure {i // p i} (Real.toNNReal s)) (Set.Ioc 0 (T : ℝ)) ∧
    (∫ w, ∑ j : Fin w.1,
      if p (w.2 j) then 0 else F (partitionWords p (take w j)).1 (w.2 j)
        ∂measure ι T) =
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i ∈ Finset.univ.filter (fun i ↦ ¬p i),
        ∫ u, F u i ∂measure {i // p i} (Real.toNNReal s) :=
  ⟨integrable_sum_omitted_partition_prefix p T F hF hb,
    integrableOn_sum_word_integral T _ F hF hb,
    integral_sum_omitted_partition_prefix p T F hF hb⟩

-- A nonconstant prefix kernel, depending on the retained prefix length.
example (T : ℝ≥0) :
    Integrable (fun w : Word (Fin 2) ↦ ∑ j : Fin w.1,
      if w.2 j = 0 then 0
      else if (partitionWords (fun i : Fin 2 ↦ i = 0) (take w j)).1.1 = 0
        then (1 : ℝ) else 0) (measure (Fin 2) T) := by
  apply integrable_sum_omitted_partition_prefix (fun i : Fin 2 ↦ i = 0) T
    (fun u _ ↦ if u.1 = 0 then 1 else 0) (C := 1)
  · intro u i
    split_ifs <;> norm_num
  · intro u i
    split_ifs <;> norm_num

example (F : Word (Fin 3) → Fin 3 → ℝ) {C : ℝ}
    (hF : ∀ u i, 0 ≤ F u i) (hb : ∀ u i, F u i ≤ C) :
    Integrable (fun w ↦ ∑ j : Fin w.1, F (take w j) (w.2 j)) (measure (Fin 3) 0) ∧
      (∫ w, ∑ j : Fin w.1, F (take w j) (w.2 j) ∂measure (Fin 3) 0) = 0 := by
  refine ⟨integrable_sum_prefix 0 F hF hb, ?_⟩
  rw [integral_sum_prefix 0 F hF hb]
  simp

-- No nonempty alphabet assumption is used in either integrability or equality.
example (T : ℝ≥0) (F : Word (Fin 0) → Fin 0 → ℝ) :
    Integrable (fun w ↦ ∑ j : Fin w.1, F (take w j) (w.2 j)) (measure (Fin 0) T) ∧
      (∫ w, ∑ j : Fin w.1, F (take w j) (w.2 j) ∂measure (Fin 0) T) = 0 := by
  have hF (u) (i : Fin 0) : 0 ≤ F u i := Fin.elim0 i
  have hb (u) (i : Fin 0) : F u i ≤ 0 := Fin.elim0 i
  refine ⟨integrable_sum_prefix T F hF hb, ?_⟩
  rw [integral_sum_prefix T F hF hb]
  simp

-- A singleton omitted label has expected count T, with finite real integrals.
example (T : ℝ≥0) :
    Integrable (fun w : Word (Fin 3) ↦ ∑ j : Fin w.1,
      if w.2 j ≠ 1 then (0 : ℝ) else 1) (measure (Fin 3) T) ∧
      (∫ w : Word (Fin 3), ∑ j : Fin w.1,
        if w.2 j ≠ 1 then (0 : ℝ) else 1 ∂measure (Fin 3) T) = T := by
  have h0 (_u : Word {i : Fin 3 // i ≠ 1}) (_i : Fin 3) : (0 : ℝ) ≤ 1 := zero_le_one
  have h1 (_u : Word {i : Fin 3 // i ≠ 1}) (_i : Fin 3) : (1 : ℝ) ≤ 1 := le_rfl
  refine ⟨integrable_sum_omitted_partition_prefix (fun i : Fin 3 ↦ i ≠ 1) T
    (fun _ _ ↦ 1) h0 h1, ?_⟩
  rw [integral_sum_omitted_partition_prefix (fun i : Fin 3 ↦ i ≠ 1) T
    (fun _ _ ↦ 1) h0 h1]
  have hc : (Finset.univ.filter (fun i : Fin 3 ↦ i = 1)).card = 1 := by decide
  simp [hc, Measure.real, Real.volume_Ioc]

end PoissonWordRealOccupationTest
