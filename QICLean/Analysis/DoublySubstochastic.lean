/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Matrix.Block

/-!
# Doubly substochastic matrices and partial permutations

Wolf, Theorem 8.6 (`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 263–266):
the doubly substochastic matrices form the convex hull of the partial permutation matrices,
and their extreme points are exactly those matrices. No nonempty dimension is assumed.

The completion to a doubly stochastic matrix has diagonal row and column deficit blocks
and a lower-right block given by the outer product of the column and row sums, divided
by their common total. The zero-total case is treated separately.

The extreme-point rigidity proof adapts `Mathlib/Analysis/Convex/Birkhoff.lean` at
commit `c55e6e786f49471c72fbddbec5415808896aec1e`, replacing stochastic entry bounds
by substochastic entry bounds; the completion and partial-permutation arguments are new.
-/

namespace TNLean

open Finset Matrix

variable {n : Type*} [Fintype n]

/-- Nonnegative square matrices whose row and column sums are at most one. -/
def doublySubstochastic (n : Type*) [Fintype n] : Set (Matrix n n ℝ) :=
  {M | (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j ≤ 1) ∧ ∀ j, ∑ i, M i j ≤ 1}

/-- A partial permutation matrix has zero-one entries and at most one one in each row and column. -/
def IsPartialPermutation (M : Matrix n n ℝ) : Prop :=
  (∀ i j, M i j = 0 ∨ M i j = 1) ∧
    (∀ i j k, M i j = 1 → M i k = 1 → j = k) ∧
    ∀ i j k, M i j = 1 → M k j = 1 → i = k

/-- Each entry of a doubly substochastic matrix belongs to the unit interval. -/
lemma doublySubstochastic_entry_le_one {M : Matrix n n ℝ}
    (hM : M ∈ doublySubstochastic n) (i j : n) : M i j ≤ 1 :=
  (single_le_sum (fun k _ => hM.1 i k) (mem_univ j)).trans (hM.2.1 i)

/-- Doubly substochastic matrices form a convex set. -/
lemma convex_doublySubstochastic : Convex ℝ (doublySubstochastic n) := by
  intro M hM N hN a b ha hb hab
  refine ⟨fun i j => add_nonneg (mul_nonneg ha (hM.1 i j))
    (mul_nonneg hb (hN.1 i j)), ?_, ?_⟩
  · intro i
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
    calc
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left (hM.2.1 i) ha)
        (mul_le_mul_of_nonneg_left (hN.2.1 i) hb)
      _ = 1 := by simpa using hab
  · intro j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
    calc
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left (hM.2.2 j) ha)
        (mul_le_mul_of_nonneg_left (hN.2.2 j) hb)
      _ = 1 := by simpa using hab

private lemma sum_le_one_of_zero_one_unique (v : n → ℝ)
    (hv : ∀ i, v i = 0 ∨ v i = 1) (hu : ∀ i j, v i = 1 → v j = 1 → i = j) :
    ∑ i, v i ≤ 1 := by
  classical
  by_cases h : ∃ i, v i = 1
  · obtain ⟨i, hi⟩ := h
    have hs : ∑ j, v j = v i := by
      apply sum_eq_single i
      · intro j _ hji
        rcases hv j with hj | hj
        · exact hj
        · exact (hji (hu j i hj hi)).elim
      · simp
    simp [hs, hi]
  · have hz (i : n) : v i = 0 := (hv i).resolve_right (fun hi => h ⟨i, hi⟩)
    simp [hz]

/-- Partial permutation matrices are doubly substochastic. -/
lemma IsPartialPermutation.mem_doublySubstochastic {M : Matrix n n ℝ}
    (hM : IsPartialPermutation M) : M ∈ doublySubstochastic n := by
  refine ⟨fun i j => ?_, fun i => sum_le_one_of_zero_one_unique _ (hM.1 i) (hM.2.1 i),
    fun j => sum_le_one_of_zero_one_unique _ (fun i => hM.1 i j) (fun i k => hM.2.2 i j k)⟩
  rcases hM.1 i j with h | h <;> simp [h]

/-- Among doubly substochastic matrices, zero-one entries characterize partial permutations. -/
lemma isPartialPermutation_iff {M : Matrix n n ℝ} :
    IsPartialPermutation M ↔ M ∈ doublySubstochastic n ∧
      ∀ i j, M i j = 0 ∨ M i j = 1 := by
  classical
  constructor
  · intro hM
    exact ⟨hM.mem_doublySubstochastic, hM.1⟩
  · rintro ⟨hM, hz⟩
    refine ⟨hz, ?_, ?_⟩
    · intro i j k hj hk
      by_contra h
      have hsum : M i j + M i k ≤ ∑ l, M i l := by
        calc
          _ = ∑ l ∈ {j, k}, M i l := by simp [h]
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by simp) (fun l _ _ => hM.1 i l)
      linarith [hM.2.1 i]
    · intro i j k hi hk
      by_contra h
      have hsum : M i j + M k j ≤ ∑ l, M l j := by
        calc
          _ = ∑ l ∈ {i, k}, M l j := by simp [h]
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by simp) (fun l _ _ => hM.1 l j)
      linarith [hM.2.2 j]

omit [Fintype n] in
/-- There are finitely many partial permutation matrices. -/
lemma finite_isPartialPermutation [Finite n] :
    {M : Matrix n n ℝ | IsPartialPermutation M}.Finite := by
  have hrow : {v : n → ℝ | ∀ i, v i ∈ ({0, 1} : Set ℝ)}.Finite :=
    Set.Finite.pi' fun _ => Set.toFinite _
  exact (Set.Finite.pi' fun _ : n => hrow).subset fun M hM i j => by
    rcases hM.1 i j with h | h <;> simp [h]

private lemma exists_nonneg_matrix_with_sums (r c : n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j) (ht : ∑ i, r i = ∑ j, c j) :
    ∃ B : Matrix n n ℝ, (∀ i j, 0 ≤ B i j) ∧
      (∀ i, ∑ j, B i j = c i) ∧ ∀ j, ∑ i, B i j = r j := by
  let T := ∑ i, r i
  by_cases hT : T = 0
  · have hr0 (i : n) : r i = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun i _ => hr i)).1 hT i (mem_univ i)
    have hc0 (i : n) : c i = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun i _ => hc i)).1 (ht.symm.trans hT) i (mem_univ i)
    exact ⟨0, by simp, by simp [hc0], by simp [hr0]⟩
  · have hTpos : 0 < T := lt_of_le_of_ne (sum_nonneg fun i _ => hr i) (Ne.symm hT)
    refine ⟨fun i j => c i * r j / T,
      fun i j => div_nonneg (mul_nonneg (hc i) (hr j)) hTpos.le, ?_, ?_⟩
    · intro i
      rw [← sum_div, ← mul_sum]
      exact mul_div_cancel_right₀ (c i) hT
    · intro j
      rw [← sum_div, ← sum_mul, ← ht]
      exact mul_div_cancel_left₀ (r j) hT

variable [DecidableEq n]

/-- Every doubly substochastic matrix is the upper-left block of a doubly stochastic matrix
on the disjoint union of two copies of its index set. -/
theorem exists_doublyStochastic_completion {M : Matrix n n ℝ}
    (hM : M ∈ doublySubstochastic n) :
    ∃ N : Matrix (n ⊕ n) (n ⊕ n) ℝ, N ∈ doublyStochastic ℝ (n ⊕ n) ∧
      ∀ i j, N (Sum.inl i) (Sum.inl j) = M i j := by
  classical
  let r : n → ℝ := fun i => ∑ j, M i j
  let c : n → ℝ := fun j => ∑ i, M i j
  obtain ⟨B, hB, hBr, hBc⟩ := exists_nonneg_matrix_with_sums r c
    (fun i => sum_nonneg fun j _ => hM.1 i j)
    (fun j => sum_nonneg fun i _ => hM.1 i j) (sum_comm)
  refine ⟨fromBlocks M (diagonal fun i => 1 - r i) (diagonal fun j => 1 - c j) B,
    mem_doublyStochastic_iff_sum.2 ⟨?_, ?_, ?_⟩, fun _ _ => rfl⟩
  · rintro (i | i) (j | j)
    · exact hM.1 i j
    · simp only [fromBlocks_apply₁₂, diagonal_apply]
      split_ifs <;> first | exact sub_nonneg.2 (hM.2.1 i) | exact le_rfl
    · simp only [fromBlocks_apply₂₁, diagonal_apply]
      split_ifs <;> first | exact sub_nonneg.2 (hM.2.2 i) | exact le_rfl
    · exact hB i j
  · rintro (i | i)
    · simp [Fintype.sum_sum_type, diagonal_apply, r]
    · simp [Fintype.sum_sum_type, diagonal_apply, hBr, c]
  · rintro (j | j)
    · simp [Fintype.sum_sum_type, diagonal_apply, c]
    · simp [Fintype.sum_sum_type, diagonal_apply, hBc, r]

private lemma toBlocks₁₁_mem_doublySubstochastic {N : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hN : N ∈ doublyStochastic ℝ (n ⊕ n)) : N.toBlocks₁₁ ∈ doublySubstochastic n := by
  refine ⟨fun i j => hN.1 _ _, ?_, ?_⟩
  · intro i
    have hrow := sum_row_of_mem_doublyStochastic hN (Sum.inl i)
    rw [Fintype.sum_sum_type] at hrow
    have hright : 0 ≤ ∑ j, N (Sum.inl i) (Sum.inr j) :=
      sum_nonneg fun j _ => hN.1 _ _
    change ∑ j, N (Sum.inl i) (Sum.inl j) ≤ 1
    linarith
  · intro j
    have hcol := sum_col_of_mem_doublyStochastic hN (Sum.inl j)
    rw [Fintype.sum_sum_type] at hcol
    have hbottom : 0 ≤ ∑ i, N (Sum.inr i) (Sum.inl j) :=
      sum_nonneg fun i _ => hN.1 _ _
    change ∑ i, N (Sum.inl i) (Sum.inl j) ≤ 1
    linarith

omit [Fintype n] in
private lemma isPartialPermutation_toBlocks₁₁_permMatrix [Finite n]
    (σ : Equiv.Perm (n ⊕ n)) :
    IsPartialPermutation (σ.permMatrix ℝ).toBlocks₁₁ := by
  classical
  let := Fintype.ofFinite n
  rw [isPartialPermutation_iff]
  refine ⟨toBlocks₁₁_mem_doublySubstochastic permMatrix_mem_doublyStochastic, ?_⟩
  intro i j
  change σ.permMatrix ℝ (Sum.inl i) (Sum.inl j) = 0 ∨
    σ.permMatrix ℝ (Sum.inl i) (Sum.inl j) = 1
  simp only [PEquiv.toMatrix_apply]
  split_ifs <;> simp

omit [DecidableEq n] in
/-- The doubly substochastic matrices are the convex hull of the partial permutation matrices
(Wolf, Theorem 8.6). -/
theorem doublySubstochastic_eq_convexHull_isPartialPermutation :
    doublySubstochastic n = convexHull ℝ {M : Matrix n n ℝ | IsPartialPermutation M} := by
  classical
  refine (convexHull_min (fun _ hM => hM.mem_doublySubstochastic)
    convex_doublySubstochastic).antisymm' ?_
  intro M hM
  obtain ⟨N, hN, hNM⟩ := exists_doublyStochastic_completion hM
  obtain ⟨w, hw, hw1, hwN⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hN
  refine mem_convexHull_of_exists_fintype w (fun σ => (σ.permMatrix ℝ).toBlocks₁₁)
    hw hw1 isPartialPermutation_toBlocks₁₁_permMatrix ?_
  ext i j
  have hij := congrArg (fun X : Matrix (n ⊕ n) (n ⊕ n) ℝ => X (Sum.inl i) (Sum.inl j)) hwN
  simpa only [Matrix.sum_apply, Matrix.smul_apply, toBlocks₁₁, of_apply, hNM] using hij

omit [DecidableEq n] in
/-- The extreme points of the doubly substochastic matrices are exactly the partial permutation
matrices (Wolf, Theorem 8.6). The entrywise rigidity argument follows
Mathlib's `extremePoints_doublyStochastic`, at commit
`c55e6e786f49471c72fbddbec5415808896aec1e`, with substochastic bounds. -/
theorem extremePoints_doublySubstochastic :
    Set.extremePoints ℝ (doublySubstochastic n) =
      {M : Matrix n n ℝ | IsPartialPermutation M} := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · rw [doublySubstochastic_eq_convexHull_isPartialPermutation]
    exact extremePoints_convexHull_subset
  intro M hM
  refine ⟨hM.mem_doublySubstochastic, fun X hX Y hY hseg => ?_⟩
  suffices hXY : ∀ i j, X i j = Y i j by
    obtain rfl : X = Y := Matrix.ext hXY
    simp_all
  intro i j
  have hentry : M i j ∈ openSegment ℝ (X i j) (Y i j) :=
    image_openSegment _ (entryLinearMap ℝ ℝ i j).toAffineMap X Y ▸ ⟨_, hseg, rfl⟩
  by_contra hne
  have hbounds : openSegment ℝ (X i j) (Y i j) ⊆ Set.Ioo 0 1 := by
    rw [openSegment_eq_Ioo' hne]
    apply Set.Ioo_subset_Ioo
    · exact le_min (hX.1 i j) (hY.1 i j)
    · exact max_le (doublySubstochastic_entry_le_one hX i j)
        (doublySubstochastic_entry_le_one hY i j)
  have hstrict := hbounds hentry
  rcases hM.1 i j with hzero | hone <;> simp_all

omit [DecidableEq n] in
/-- Doubly substochastic matrices form a convex polytope, with its full finite vertex set. -/
theorem doublySubstochastic_isPolytope :
    ∃ S : Finset (Matrix n n ℝ),
      (∀ M, M ∈ S ↔ IsPartialPermutation M) ∧ doublySubstochastic n = convexHull ℝ (S : Set _) := by
  classical
  refine ⟨finite_isPartialPermutation.toFinset, by simp, ?_⟩
  simpa using (doublySubstochastic_eq_convexHull_isPartialPermutation (n := n))

/-- The doubly substochastic convex-hull equality in Wolf, Theorem 8.6. -/
theorem wolf_birkhoff_doublySubstochastic_convexHull {d : ℕ} :
    doublySubstochastic (Fin d) =
      convexHull ℝ {M : Matrix (Fin d) (Fin d) ℝ | IsPartialPermutation M} :=
  doublySubstochastic_eq_convexHull_isPartialPermutation

/-- The doubly substochastic extreme-point equality in Wolf, Theorem 8.6. -/
theorem wolf_birkhoff_extremePoints_doublySubstochastic {d : ℕ} :
    Set.extremePoints ℝ (doublySubstochastic (Fin d)) =
      {M : Matrix (Fin d) (Fin d) ℝ | IsPartialPermutation M} :=
  extremePoints_doublySubstochastic

end TNLean
