/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.VectorMajorization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Actual-name boundary and foundation checks for Wolf Theorem 8.4(1,2,4). -/

open Finset Matrix TNLean

-- The definition really uses decreasing prefixes, with equality at the full dimension.
example {d : ℕ} (x y : Fin d → ℝ) :
    VectorMajorized x y ↔
      (∀ k ≤ d, vectorPrefix (decreasingSort x) k ≤ vectorPrefix (decreasingSort y) k) ∧
        vectorPrefix (decreasingSort x) d = vectorPrefix (decreasingSort y) d := by
  simp only [VectorMajorized, vectorPrefix_dim, sum_decreasingSort]

-- The matrix condition includes all entries and every row and column sum.
example {d : ℕ} (x y : Fin d → ℝ) :
    VectorMajorized x y ↔ ∃ M : Matrix (Fin d) (Fin d) ℝ,
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) ∧
        (∀ j, ∑ i, M i j = 1) ∧ x = M *ᵥ y := by
  rw [vectorMajorized_iff_exists_doublyStochastic]
  simp only [mem_doublyStochastic_iff_sum, and_assoc]

-- All convex functions on all of ℝ, without monotonicity or regularity assumptions.
example {d : ℕ} (x y : Fin d → ℝ) :
    (∃ M ∈ doublyStochastic ℝ (Fin d), x = M *ᵥ y) ↔
      ∀ f : ℝ → ℝ, ConvexOn ℝ Set.univ f → ∑ i, f (x i) ≤ ∑ i, f (y i) :=
  (vectorMajorized_iff_exists_doublyStochastic x y).symm.trans
    (vectorMajorized_iff_sum_convex_le x y)

example {d : ℕ} (x y : Fin d → ℝ) (σ τ : Equiv.Perm (Fin d)) :
    VectorMajorized (x ∘ σ) (y ∘ τ) ↔ VectorMajorized x y :=
  vectorMajorized_comp_perm_iff x y σ τ

example {d : ℕ} (x : Fin d → ℝ) (σ : Equiv.Perm (Fin d)) :
    VectorMajorized (x ∘ σ) x := by
  apply (vectorMajorized_iff_exists_doublyStochastic _ _).mpr
  exact ⟨σ.permMatrix ℝ, permMatrix_mem_doublyStochastic, (permMatrix_mulVec σ).symm⟩

example (x y : Fin 0 → ℝ) : VectorMajorized x y := by
  apply vectorMajorized_of_sum_convex_le
  intro f _
  simp

example (x y : Fin 0 → ℝ) :
    ∃ M ∈ doublyStochastic ℝ (Fin 0), x = M *ᵥ y := by
  apply VectorMajorized.exists_doublyStochastic
  constructor
  · intro k hk
    have : k = 0 := by omega
    subst k
    simp
  · simp

example (x y : Fin 1 → ℝ) : VectorMajorized x y ↔ x = y := by
  constructor
  · intro h
    ext i
    simpa only [Fin.sum_univ_one, Subsingleton.elim i 0] using h.2
  · rintro rfl
    exact ⟨fun _ _ => le_rfl, rfl⟩

-- Repeated entries survive sorting; this is a three-coordinate vector.
example : decreasingSort (![2, 2, -1] : Fin 3 → ℝ) = ![2, 2, -1] := by
  apply decreasingSort_eq_self
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> norm_num

-- Negative entries and negative total sum; the concrete prefix condition is tested directly.
private theorem negative_majorization :
    VectorMajorized (![-2, -2] : Fin 2 → ℝ) ![-1, -3] := by
  have hx : Antitone (![-2, -2] : Fin 2 → ℝ) := by
    intro i j _
    fin_cases i <;> fin_cases j <;> norm_num
  have hy : Antitone (![-1, -3] : Fin 2 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  refine ⟨?_, by norm_num [Fin.sum_univ_two]⟩
  rw [decreasingSort_eq_self hx, decreasingSort_eq_self hy]
  intro k hk
  interval_cases k <;> norm_num [vectorPrefix, sum_filter, Fin.sum_univ_two]

example : ∃ M ∈ doublyStochastic ℝ (Fin 2),
    (![-2, -2] : Fin 2 → ℝ) = M *ᵥ ![-1, -3] :=
  negative_majorization.exists_doublyStochastic

example (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    f (-2) + f (-2) ≤ f (-1) + f (-3) := by
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
    (vectorMajorized_iff_sum_convex_le _ _).mp negative_majorization f hf

-- Upper-prefix inequalities alone must not silently become majorization.
example : ¬ VectorMajorized (![-2] : Fin 1 → ℝ) ![-1] := by
  intro h
  have ht := h.2
  norm_num [Fin.sum_univ_one] at ht

-- The mean is majorized by every real vector, not only probability vectors.
example {d : ℕ} (hd : d ≠ 0) (x : Fin d → ℝ) :
    VectorMajorized (fun _ : Fin d => (∑ j, x j) / d) x := by
  classical
  apply (vectorMajorized_iff_exists_doublyStochastic _ _).mpr
  refine ⟨fun _ _ => (d : ℝ)⁻¹, ?_, ?_⟩
  · apply mem_doublyStochastic_iff_sum.mpr
    have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
    refine ⟨fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg d), ?_, ?_⟩ <;>
      intro i <;> simp [hd']
  · ext i
    simp [mulVec, dotProduct, ← sum_mul, div_eq_mul_inv, mul_comm]

-- The uniform probability vector is below a pure distribution (Eq. 8.17).
example : VectorMajorized (fun _ : Fin 2 => (1 / 2 : ℝ)) ![1, 0] := by
  apply (vectorMajorized_iff_exists_doublyStochastic _ _).mpr
  refine ⟨fun _ _ => 1 / 2, ?_, ?_⟩
  · apply mem_doublyStochastic_iff_sum.mpr
    refine ⟨fun _ _ => by norm_num, ?_, ?_⟩ <;> intro i <;>
      norm_num [Fin.sum_univ_two]
  · ext i
    norm_num [mulVec, dotProduct, Fin.sum_univ_two]

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``TNLean.decreasingPerm, ``TNLean.decreasingSort,
    ``TNLean.antitone_decreasingSort, ``TNLean.decreasingSort_comp_perm,
    ``TNLean.decreasingSort_eq_self, ``TNLean.vectorPrefix,
    ``TNLean.vectorPrefix_zero, ``TNLean.vectorPrefix_dim, ``TNLean.sum_decreasingSort,
    ``TNLean.VectorMajorized, ``TNLean.vectorMajorized_comp_perm_iff,
    ``TNLean.sum_convex_le_of_doublyStochastic, ``TNLean.vectorMajorized_of_sum_convex_le,
    ``TNLean.VectorMajorized.mem_convexHull_permutations,
    ``TNLean.VectorMajorized.exists_doublyStochastic,
    ``TNLean.vectorMajorized_iff_exists_doublyStochastic,
    ``TNLean.vectorMajorized_iff_sum_convex_le]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
