/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Birkhoff

/-!
# Doubly substochastic boundary cases and foundation checks

Check the exact public statements, the empty dimension, the zero matrix, and a strictly
substochastic matrix with tied positive entries. All applications use actual entry and sum
conditions; no convex decomposition or extremality is supplied as an assumption.
-/

open TNLean

/-- info:
'TNLean.exists_doublyStochastic_completion' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.exists_doublyStochastic_completion

/-- info:
'TNLean.wolf_birkhoff_doublySubstochastic_convexHull' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.wolf_birkhoff_doublySubstochastic_convexHull

/-- info:
'TNLean.wolf_birkhoff_extremePoints_doublySubstochastic' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.wolf_birkhoff_extremePoints_doublySubstochastic

/-- info:
'TNLean.doublySubstochastic_isPolytope' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.doublySubstochastic_isPolytope

example : doublySubstochastic (Fin 0) =
    convexHull ℝ {M : Matrix (Fin 0) (Fin 0) ℝ | IsPartialPermutation M} :=
  wolf_birkhoff_doublySubstochastic_convexHull

example : (0 : Matrix (Fin 0) (Fin 0) ℝ) ∈
    Set.extremePoints ℝ (doublySubstochastic (Fin 0)) := by
  rw [wolf_birkhoff_extremePoints_doublySubstochastic]
  simp [IsPartialPermutation]

example (d : ℕ) : (0 : Matrix (Fin d) (Fin d) ℝ) ∈
    Set.extremePoints ℝ (doublySubstochastic (Fin d)) := by
  rw [wolf_birkhoff_extremePoints_doublySubstochastic]
  simp [IsPartialPermutation]

example (d : ℕ) : ∃ N : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ,
    N ∈ doublyStochastic ℝ (Fin d ⊕ Fin d) ∧
      ∀ i j, N (Sum.inl i) (Sum.inl j) = 0 := by
  apply exists_doublyStochastic_completion (M := 0)
  simp [doublySubstochastic]

private noncomputable def tiedMatrix : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1 / 4

private lemma tiedMatrix_mem : tiedMatrix ∈ doublySubstochastic (Fin 2) := by
  norm_num [doublySubstochastic, tiedMatrix, Fin.sum_univ_two]

example : tiedMatrix ∈ convexHull ℝ {M : Matrix (Fin 2) (Fin 2) ℝ | IsPartialPermutation M} := by
  rw [← wolf_birkhoff_doublySubstochastic_convexHull]
  exact tiedMatrix_mem

example : ∃ N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ,
    N ∈ doublyStochastic ℝ (Fin 2 ⊕ Fin 2) ∧
      ∀ i j, N (Sum.inl i) (Sum.inl j) = tiedMatrix i j :=
  exists_doublyStochastic_completion tiedMatrix_mem

example : tiedMatrix ∉ Set.extremePoints ℝ (doublySubstochastic (Fin 2)) := by
  rw [wolf_birkhoff_extremePoints_doublySubstochastic]
  intro h
  have hentry := h.1 0 0
  norm_num [tiedMatrix] at hentry
