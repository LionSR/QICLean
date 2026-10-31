/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Majorization of real vectors

Wolf, Chapter 8, Eq. (8.16) and Theorem 8.4, clauses 1, 2 and 4
(`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 220–251).
Vectors have arbitrary real entries. Sorting preserves multiplicities.

**Scope restriction (Wolf Theorem 8.4):** the orthostochastic characterization
in clause 3 is not included. See
`docs/paper-gaps/wolf_ch8_vector_majorization_orthostochastic_gap.tex`.
-/

open Finset Matrix

namespace TNLean

variable {d : ℕ}

/-- The permutation arranging a real vector in decreasing order. -/
noncomputable def decreasingPerm (x : Fin d → ℝ) : Equiv.Perm (Fin d) :=
  Tuple.sort (α := ℝᵒᵈ) x

/-- The entries of a real vector in decreasing order, including repeated entries. -/
noncomputable def decreasingSort (x : Fin d → ℝ) : Fin d → ℝ :=
  x ∘ decreasingPerm x

theorem antitone_decreasingSort (x : Fin d → ℝ) : Antitone (decreasingSort x) :=
  Tuple.monotone_sort (α := ℝᵒᵈ) x

theorem decreasingSort_comp_perm (x : Fin d → ℝ) (σ : Equiv.Perm (Fin d)) :
    decreasingSort (x ∘ σ) = decreasingSort x :=
  Tuple.comp_perm_comp_sort_eq_comp_sort (α := ℝᵒᵈ)

theorem decreasingSort_eq_self {x : Fin d → ℝ} (hx : Antitone x) :
    decreasingSort x = x := by
  exact Tuple.unique_antitone (antitone_decreasingSort x) (σ := decreasingPerm x)
    (τ := Equiv.refl _) hx

/-- The sum of the first `k` coordinates (all coordinates when `d ≤ k`). -/
def vectorPrefix (x : Fin d → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin d with i.val < k, x i

@[simp] theorem vectorPrefix_zero (x : Fin d → ℝ) : vectorPrefix x 0 = 0 := by
  simp [vectorPrefix]

@[simp] theorem vectorPrefix_dim (x : Fin d → ℝ) : vectorPrefix x d = ∑ i, x i := by
  simp [vectorPrefix]

theorem sum_decreasingSort (x : Fin d → ℝ) : ∑ i, decreasingSort x i = ∑ i, x i :=
  Equiv.sum_comp (decreasingPerm x) x

/-- Majorization by decreasing prefixes and equal total sum, Wolf Eq. (8.16). -/
def VectorMajorized (x y : Fin d → ℝ) : Prop :=
  (∀ k ≤ d, vectorPrefix (decreasingSort x) k ≤ vectorPrefix (decreasingSort y) k) ∧
    ∑ i, x i = ∑ i, y i

theorem vectorMajorized_comp_perm_iff (x y : Fin d → ℝ)
    (σ τ : Equiv.Perm (Fin d)) :
    VectorMajorized (x ∘ σ) (y ∘ τ) ↔ VectorMajorized x y := by
  simp only [VectorMajorized, decreasingSort_comp_perm, Function.comp_apply,
    Equiv.sum_comp]

/-- Finite Jensen applied to each row, then summed using the column sums. -/
theorem sum_convex_le_of_doublyStochastic {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin d)) (y : Fin d → ℝ)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ∑ i, f ((M *ᵥ y) i) ≤ ∑ i, f (y i) := by
  calc
    _ ≤ ∑ i, ∑ j, M i j * f (y j) := by
      apply sum_le_sum
      intro i _
      simpa [mulVec, dotProduct, smul_eq_mul] using
        hf.map_sum_le (t := univ) (w := M i) (p := y)
          (fun j _ => nonneg_of_mem_doublyStochastic hM)
          (sum_row_of_mem_doublyStochastic hM i) (fun _ _ => Set.mem_univ _)
    _ = _ := by
      rw [sum_comm]
      simp_rw [← sum_mul, sum_col_of_mem_doublyStochastic hM, one_mul]

private def extendVector (x : Fin d → ℝ) (i : ℕ) : ℝ :=
  if h : i < d then x ⟨i, h⟩ else 0

private theorem vectorPrefix_eq_range (x : Fin d → ℝ) {k : ℕ} (hk : k ≤ d) :
    vectorPrefix x k = ∑ i ∈ range k, extendVector x i := by
  classical
  apply sum_bij (fun i _ => i.val)
  · intro i hi
    simpa using (mem_filter.mp hi).2
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro i hi
    have hi' := mem_range.mp hi
    exact ⟨⟨i, lt_of_lt_of_le hi' hk⟩, by simp [hi'], rfl⟩
  · intro i _
    simp [extendVector]

private theorem sum_mul_le_of_prefix {x y w : Fin d → ℝ}
    (hp : ∀ k ≤ d, vectorPrefix x k ≤ vectorPrefix y k)
    (ht : ∑ i, x i = ∑ i, y i) (hw : Antitone w) :
    ∑ i, x i * w i ≤ ∑ i, y i * w i := by
  classical
  cases d with
  | zero => simp
  | succ n =>
    let g : ℕ → ℝ := fun i =>
      if h : i < n + 1 then w ⟨i, h⟩ - w (Fin.last n) else 0
    have hg : 0 ≤ g := by
      intro i
      dsimp [g]
      split_ifs with hi
      · exact sub_nonneg.mpr (hw (Fin.le_last _))
      · exact le_rfl
    have hmono : AntitoneOn g (Set.Iio (n + 1)) := by
      intro i hi j hj hij
      change i < n + 1 at hi
      change j < n + 1 at hj
      simpa only [g, hi, hj, dite_true] using sub_le_sub_right
        (hw (show (⟨i, hi⟩ : Fin (n + 1)) ≤ ⟨j, hj⟩ from hij)) (w (Fin.last n))
    have h := sum_mul_le_sum_mul_of_sum_range_le
      (f := extendVector x) (c := extendVector y)
      (fun k hk => by
        rw [← vectorPrefix_eq_range _ hk, ← vectorPrefix_eq_range _ hk]
        exact hp k hk)
      hg hmono
    have hz (z : Fin (n + 1) → ℝ) :
        (∑ i ∈ range (n + 1), extendVector z i * g i) =
          ∑ i, z i * (w i - w (Fin.last n)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro i _
      simp [extendVector, g, Nat.le_of_lt_succ i.isLt]
    rw [hz x, hz y] at h
    simpa only [mul_sub, sum_sub_distrib, ← sum_mul, ht, sub_le_sub_iff_right] using h

private theorem prefix_le_hinge (x : Fin d → ℝ) (k : ℕ) (t : ℝ) :
    vectorPrefix x k ≤ vectorPrefix (fun _ : Fin d => t) k +
      ∑ i, max (x i - t) 0 := by
  classical
  have h : vectorPrefix x k - vectorPrefix (fun _ : Fin d => t) k ≤
      ∑ i, max (x i - t) 0 := by
    simp only [vectorPrefix, ← sum_sub_distrib, sum_filter]
    apply sum_le_sum
    intro i _
    split_ifs
    · exact le_max_left _ _
    · simp
  linarith

private theorem hinge_eq_prefix {y : Fin d → ℝ} (hy : Antitone y)
    {k : ℕ} (hk : k < d) :
    ∑ i, max (y i - y ⟨k, hk⟩) 0 =
      vectorPrefix y k - vectorPrefix (fun _ : Fin d => y ⟨k, hk⟩) k := by
  classical
  simp only [vectorPrefix, ← sum_sub_distrib, sum_filter]
  apply sum_congr rfl
  intro i _
  split_ifs with hi
  · exact max_eq_left (sub_nonneg.mpr (hy (show i ≤ ⟨k, hk⟩ from hi.le)))
  · simpa using max_eq_right
      (sub_nonpos.mpr (hy (show ⟨k, hk⟩ ≤ i from Nat.le_of_not_gt hi)))

/-- All convex functions detect exactly the decreasing-prefix inequalities, in one direction.
The affine functions detect the total sum; the hinge functions detect each proper prefix. -/
theorem vectorMajorized_of_sum_convex_le {x y : Fin d → ℝ}
    (h : ∀ f : ℝ → ℝ, ConvexOn ℝ Set.univ f → ∑ i, f (x i) ≤ ∑ i, f (y i)) :
    VectorMajorized x y := by
  have ht : ∑ i, x i = ∑ i, y i := by
    have h₁ := h id (convexOn_id convex_univ)
    have h₂ := h (fun t => -t) (concaveOn_id convex_univ).neg
    simp only [id_eq] at h₁
    simp only [sum_neg_distrib] at h₂
    linarith
  refine ⟨?_, ht⟩
  intro k hk
  rcases lt_or_eq_of_le hk with hkd | rfl
  · let t := decreasingSort y ⟨k, hkd⟩
    have hc : ConvexOn ℝ Set.univ (fun z : ℝ => max (z - t) 0) :=
      ((convexOn_id convex_univ).sub (concaveOn_const t convex_univ)).sup
        (convexOn_const 0 convex_univ)
    have hh := h _ hc
    have hs (z : Fin d → ℝ) :
        ∑ i, max (decreasingSort z i - t) 0 = ∑ i, max (z i - t) 0 :=
      Equiv.sum_comp (decreasingPerm z) (fun a => max (z a - t) 0)
    rw [← hs x, ← hs y, hinge_eq_prefix (antitone_decreasingSort y) hkd] at hh
    have hp := prefix_le_hinge (decreasingSort x) k t
    dsimp [t] at hp ⊢
    linarith
  · simp only [vectorPrefix_dim, sum_decreasingSort, ht, le_refl]

private theorem sum_mul_le_sorted (a x : Fin d → ℝ) :
    ∑ i, a i * x i ≤ ∑ i, decreasingSort a i * decreasingSort x i := by
  classical
  rw [← Equiv.sum_comp (decreasingPerm a) (fun i => a i * x i)]
  have h := ((antitone_decreasingSort a).monovary
    (antitone_decreasingSort x)).sum_mul_comp_perm_le_sum_mul
      (σ := (decreasingPerm a).trans (decreasingPerm x).symm)
  simpa [decreasingSort, Function.comp_def] using h

private theorem exists_perm_sum_mul_le {x y : Fin d → ℝ}
    (h : VectorMajorized x y) (a : Fin d → ℝ) :
    ∃ σ : Equiv.Perm (Fin d), ∑ i, a i * x i ≤ ∑ i, a i * y (σ i) := by
  classical
  let σ := (decreasingPerm a).symm.trans (decreasingPerm y)
  refine ⟨σ, ?_⟩
  calc
    _ ≤ ∑ i, decreasingSort a i * decreasingSort x i := sum_mul_le_sorted a x
    _ ≤ ∑ i, decreasingSort a i * decreasingSort y i := by
      simpa only [mul_comm] using sum_mul_le_of_prefix h.1
        (by simpa only [sum_decreasingSort] using h.2) (antitone_decreasingSort a)
    _ = _ := by
      rw [← Equiv.sum_comp (decreasingPerm a) (fun i => a i * y (σ i))]
      simp [σ, decreasingSort]

private theorem linear_apply_eq_sum (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (x : Fin d → ℝ) :
    f x = ∑ i, f (Pi.single i 1) * x i := by
  classical
  conv_lhs => rw [← univ_sum_single x]
  rw [map_sum]
  apply sum_congr rfl
  intro i _
  have hs : Pi.single i (x i) = x i • (Pi.single i 1 : Fin d → ℝ) := by
    ext j
    simp [Pi.single_apply, smul_eq_mul]
  rw [hs, map_smul]
  simp [smul_eq_mul, mul_comm]

/-- Decreasing-prefix majorization places a vector in the convex hull of all permutations
of the other vector. The proof separates a point from that finite convex hull. -/
theorem VectorMajorized.mem_convexHull_permutations {x y : Fin d → ℝ}
    (h : VectorMajorized x y) :
    x ∈ convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin d) => y ∘ σ)) := by
  classical
  by_contra hx
  obtain ⟨f, u, hu, hfx⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) ((Set.finite_range _).isClosed_convexHull ℝ) hx
  obtain ⟨σ, hσ⟩ := exists_perm_sum_mul_le h (fun i => f (Pi.single i 1))
  have hle : f x ≤ f (y ∘ σ) := by
    change f.toLinearMap x ≤ f.toLinearMap (y ∘ σ)
    rw [linear_apply_eq_sum, linear_apply_eq_sum]
    exact hσ
  have hfu := hu (y ∘ σ) (subset_convexHull ℝ _ (Set.mem_range_self σ))
  linarith

/-- The stochastic witness in Wolf Theorem 8.4(2) is obtained from the convex hull,
using Birkhoff's theorem, rather than supplied as a hypothesis. -/
theorem VectorMajorized.exists_doublyStochastic {x y : Fin d → ℝ}
    (h : VectorMajorized x y) :
    ∃ M ∈ doublyStochastic ℝ (Fin d), x = M *ᵥ y := by
  classical
  let L : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] (Fin d → ℝ) :=
    (Matrix.mulVecBilin ℝ ℝ).flip y
  have himage : L '' {σ.permMatrix ℝ | σ : Equiv.Perm (Fin d)} =
      Set.range (fun σ : Equiv.Perm (Fin d) => y ∘ σ) := by
    ext z
    constructor
    · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
      exact ⟨σ, (Matrix.permMatrix_mulVec _).symm⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨σ.permMatrix ℝ, ⟨σ, rfl⟩, Matrix.permMatrix_mulVec _⟩
  have hx := h.mem_convexHull_permutations
  rw [← himage, ← L.image_convexHull, ← doublyStochastic_eq_convexHull_permMatrix] at hx
  obtain ⟨M, hM, hMx⟩ := hx
  exact ⟨M, hM, hMx.symm⟩

/-- Wolf Theorem 8.4, clauses 1 and 2, for arbitrary real vectors. -/
theorem vectorMajorized_iff_exists_doublyStochastic (x y : Fin d → ℝ) :
    VectorMajorized x y ↔ ∃ M ∈ doublyStochastic ℝ (Fin d), x = M *ᵥ y := by
  refine ⟨VectorMajorized.exists_doublyStochastic, ?_⟩
  rintro ⟨M, hM, rfl⟩
  exact vectorMajorized_of_sum_convex_le (fun _ hf => sum_convex_le_of_doublyStochastic hM y hf)

/-- Wolf Theorem 8.4, clauses 1 and 4. The quantifier ranges over all convex
functions on the entire real line. -/
theorem vectorMajorized_iff_sum_convex_le (x y : Fin d → ℝ) :
    VectorMajorized x y ↔
      ∀ f : ℝ → ℝ, ConvexOn ℝ Set.univ f → ∑ i, f (x i) ≤ ∑ i, f (y i) := by
  refine ⟨?_, vectorMajorized_of_sum_convex_le⟩
  intro h f hf
  obtain ⟨M, hM, rfl⟩ := h.exists_doublyStochastic
  exact sum_convex_le_of_doublyStochastic hM y hf

end TNLean
