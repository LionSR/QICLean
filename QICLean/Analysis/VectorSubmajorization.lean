/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.VectorMajorization
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

/-!
# Submajorization

A real vector `x` is weakly submajorized by `y`, `x ≺_w y`, if the sum of its `k` largest
entries is at most that of `y` for every `k`. Wolf's Theorem "Submajorization" states four
equivalent conditions. This file proves:

* `x ≺_w y` iff some `z ≺ y` dominates `x` entrywise;
* `x ≺_w y` iff `∑ f(xᵢ) ≤ ∑ f(yᵢ)` for every monotone convex `f`;
* for nonnegative vectors, `x ≺_w y` iff `x = M y` for a doubly substochastic matrix `M`.

The dominating vector is `z = max(x, θ)` for the threshold `θ` with `∑ zᵢ = ∑ yᵢ`, chosen by the
intermediate value theorem.

**Local fix (doubly substochastic clause):** Wolf states the doubly substochastic clause for all
real vectors. It fails for negative entries: for `d = 1`, `x = -2 ≤ y = -1` is submajorized but
`x = m y` forces `m = 2`. The clause is proved for nonnegative vectors, the standard setting.
Documented in `docs/paper-gaps/wolf_ch8_submajorization_nonnegative.tex`.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8, Theorem "Submajorization",
  local source `Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 252--261.
-/

open Finset Matrix
open scoped BigOperators

namespace TNLean

variable {d : ℕ}

/-- Weak submajorization `x ≺_w y`: every decreasing prefix sum of `x` is at most that of `y`.
Wolf, Chapter 8, Theorem "Submajorization", clause 1. -/
def VectorSubmajorized (x y : Fin d → ℝ) : Prop :=
  ∀ k ≤ d, vectorPrefix (decreasingSort x) k ≤ vectorPrefix (decreasingSort y) k

/-- A real matrix is doubly substochastic if its entries are nonnegative and every row sum and
every column sum is at most one. -/
def IsDoublySubstochastic (M : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j ≤ 1) ∧ ∀ j, ∑ i, M i j ≤ 1

theorem VectorMajorized.vectorSubmajorized {x y : Fin d → ℝ} (h : VectorMajorized x y) :
    VectorSubmajorized x y := h.1

/-- Adding one more coordinate to a prefix sum. -/
theorem vectorPrefix_add_one (v : Fin d → ℝ) {k : ℕ} (hk : k < d) :
    vectorPrefix v (k + 1) = vectorPrefix v k + v ⟨k, hk⟩ := by
  classical
  unfold vectorPrefix
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun i : Fin d ↦ i.val < k + 1)
    (fun i ↦ i.val < k)]
  congr 1
  · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · rw [Finset.sum_eq_single ⟨k, hk⟩]
    · intro i hi hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact absurd (Fin.ext (by simp only; omega)) hne
    · intro h; simp at h

/-- Prefix sums of entrywise equal vectors on the first `k` coordinates agree. -/
private theorem vectorPrefix_congr {u v : Fin d → ℝ} {k : ℕ}
    (h : ∀ i : Fin d, i.val < k → u i = v i) :
    vectorPrefix u k = vectorPrefix v k :=
  Finset.sum_congr rfl fun i hi ↦ h i (Finset.mem_filter.mp hi).2

/-- The complement of a prefix sum. -/
private theorem vectorPrefix_eq_sub (v : Fin d → ℝ) (k : ℕ) :
    vectorPrefix v k = ∑ i, v i - ∑ i ∈ Finset.univ.filter (fun i : Fin d ↦ ¬ i.val < k), v i := by
  unfold vectorPrefix
  rw [eq_sub_iff_add_eq, Finset.sum_filter_add_sum_filter_not]

/-- **The dominating majorized vector for sorted vectors.** For antitone `x, y` with
`x ≺_w y`, the vector `z = max(x, θ)` with `∑ zᵢ = ∑ yᵢ` satisfies `x ≤ z ≺ y`. -/
private theorem exists_majorized_ge_of_antitone {x y : Fin d → ℝ} (hx : Antitone x)
    (hy : Antitone y) (hpre : ∀ k ≤ d, vectorPrefix x k ≤ vectorPrefix y k) :
    ∃ z : Fin d → ℝ, VectorMajorized z y ∧ ∀ i, x i ≤ z i := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨x, ⟨fun k _ ↦ by simp [vectorPrefix], by simp⟩, fun i ↦ le_rfl⟩
  have hsum : ∑ i, x i ≤ ∑ i, y i := by simpa using hpre d le_rfl
  -- The threshold.
  let g : ℝ → ℝ := fun θ ↦ ∑ i, max (x i) θ
  have hg : Continuous g := continuous_finsetSum _ fun i _ ↦ continuous_const.max continuous_id
  let i0 : Fin d := ⟨d - 1, by omega⟩
  let θ0 := x i0
  have hg0 : g θ0 = ∑ i, x i := Finset.sum_congr rfl fun i _ ↦ max_eq_left (hx (by
    change i.val ≤ d - 1; omega))
  let θ1 := max θ0 ((∑ i, y i) / d)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hg1 : ∑ i, y i ≤ g θ1 := by
    have : ∑ _i : Fin d, θ1 ≤ g θ1 := Finset.sum_le_sum fun i _ ↦ le_max_right _ _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    have h2 : (d : ℝ) * ((∑ i, y i) / d) ≤ d * θ1 :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hdpos.le
    rw [mul_div_cancel₀ _ hdpos.ne'] at h2
    linarith
  obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc (le_max_left θ0 _) hg.continuousOn
    ⟨hg0 ▸ hsum, hg1⟩
  let z : Fin d → ℝ := fun i ↦ max (x i) θ
  have hz : Antitone z := fun i j hij ↦ max_le_max (hx hij) le_rfl
  have hzsum : ∑ i, z i = ∑ i, y i := hθ
  refine ⟨z, ⟨fun k hk ↦ ?_, hzsum⟩, fun i ↦ le_max_left _ _⟩
  rw [decreasingSort_eq_self hz, decreasingSort_eq_self hy]
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < d := by omega
    have ih := ih (by omega)
    let i : Fin d := ⟨k, hk'⟩
    by_cases hxi : θ ≤ x i
    · -- The first `k + 1` coordinates are unchanged.
      have hpref : vectorPrefix z (k + 1) = vectorPrefix x (k + 1) := vectorPrefix_congr
        fun j hj ↦ max_eq_left (hxi.trans (hx (show j ≤ i by change j.val ≤ k; omega)))
      rw [hpref]
      exact hpre (k + 1) (by omega)
    · push Not at hxi
      have hzi : z i = θ := max_eq_right hxi.le
      by_cases hyi : θ ≤ y i
      · rw [vectorPrefix_add_one z hk', vectorPrefix_add_one y hk']
        change vectorPrefix z k + z i ≤ vectorPrefix y k + y i
        rw [hzi]; linarith
      · push Not at hyi
        -- Every later coordinate of `z` exceeds that of `y`.
        have hlate : ∑ j ∈ Finset.univ.filter (fun j : Fin d ↦ ¬ j.val < k + 1), y j ≤
            ∑ j ∈ Finset.univ.filter (fun j : Fin d ↦ ¬ j.val < k + 1), z j := by
          refine Finset.sum_le_sum fun j hj ↦ ?_
          have hj' : ¬ j.val < k + 1 := (Finset.mem_filter.mp hj).2
          exact ((hy (show i ≤ j by change k ≤ j.val; omega)).trans hyi.le).trans
            (le_max_right _ _)
        rw [vectorPrefix_eq_sub z, vectorPrefix_eq_sub y, hzsum]
        linarith

/-- **Wolf, Submajorization, clause 1 ⇒ 3.** If `x ≺_w y`, some `z ≺ y` dominates `x`
entrywise. -/
theorem VectorSubmajorized.exists_majorized_ge {x y : Fin d → ℝ} (h : VectorSubmajorized x y) :
    ∃ z : Fin d → ℝ, VectorMajorized z y ∧ ∀ i, x i ≤ z i := by
  classical
  let σ := decreasingPerm x
  let τ := decreasingPerm y
  have hsorted : ∀ k ≤ d, vectorPrefix (decreasingSort x) k ≤ vectorPrefix (decreasingSort y) k :=
    h
  obtain ⟨z, hz, hle⟩ := exists_majorized_ge_of_antitone (antitone_decreasingSort x)
    (antitone_decreasingSort y) hsorted
  refine ⟨z ∘ σ.symm, ?_, fun i ↦ ?_⟩
  · refine (vectorMajorized_comp_perm_iff (z ∘ σ.symm) y σ τ).mp ?_
    have hzz : (z ∘ σ.symm) ∘ σ = z := by ext i; simp
    rw [hzz]
    exact hz
  · have := hle (σ.symm i)
    simpa [decreasingSort, σ] using this

/-- **Wolf, Submajorization, clause 3 ⇒ 4.** If `x ≤ z ≺ y`, then `∑ f(xᵢ) ≤ ∑ f(yᵢ)` for every
monotone convex `f`. -/
theorem sum_le_of_le_of_vectorMajorized {x y z : Fin d → ℝ} (hz : VectorMajorized z y)
    (hle : ∀ i, x i ≤ z i) {f : ℝ → ℝ} (hmono : Monotone f) (hf : ConvexOn ℝ Set.univ f) :
    ∑ i, f (x i) ≤ ∑ i, f (y i) :=
  (Finset.sum_le_sum fun i _ ↦ hmono (hle i)).trans
    ((vectorMajorized_iff_sum_convex_le z y).mp hz f hf)

/-- **Wolf, Submajorization, clause 4 ⇒ 1.** Comparison for every monotone convex function
implies `x ≺_w y`. -/
theorem vectorSubmajorized_of_sum_monotone_convex_le {x y : Fin d → ℝ}
    (h : ∀ f : ℝ → ℝ, Monotone f → ConvexOn ℝ Set.univ f → ∑ i, f (x i) ≤ ∑ i, f (y i)) :
    VectorSubmajorized x y := by
  intro k hk
  rcases lt_or_eq_of_le hk with hkd | rfl
  · let t := decreasingSort y ⟨k, hkd⟩
    have hc : ConvexOn ℝ Set.univ (fun z : ℝ ↦ max (z - t) 0) :=
      ((convexOn_id convex_univ).sub (concaveOn_const t convex_univ)).sup
        (convexOn_const 0 convex_univ)
    have hm : Monotone (fun z : ℝ ↦ max (z - t) 0) := fun a b hab ↦
      max_le_max (by linarith) le_rfl
    have hh := h _ hm hc
    have hs (z : Fin d → ℝ) :
        ∑ i, max (decreasingSort z i - t) 0 = ∑ i, max (z i - t) 0 :=
      Equiv.sum_comp (decreasingPerm z) (fun a ↦ max (z a - t) 0)
    rw [← hs x, ← hs y, hinge_eq_prefix (antitone_decreasingSort y) hkd] at hh
    have hp := prefix_le_hinge (decreasingSort x) k t
    dsimp [t] at hp ⊢
    linarith
  · have h₁ := h id monotone_id (convexOn_id convex_univ)
    simp only [id_eq] at h₁
    simpa only [vectorPrefix_dim, sum_decreasingSort] using h₁

/-- **Wolf's Submajorization theorem, clauses 1, 3 and 4.** -/
theorem vectorSubmajorized_tfae (x y : Fin d → ℝ) :
    List.TFAE [VectorSubmajorized x y,
      ∃ z : Fin d → ℝ, VectorMajorized z y ∧ ∀ i, x i ≤ z i,
      ∀ f : ℝ → ℝ, Monotone f → ConvexOn ℝ Set.univ f → ∑ i, f (x i) ≤ ∑ i, f (y i)] := by
  tfae_have 1 → 2 := VectorSubmajorized.exists_majorized_ge
  tfae_have 2 → 3 := fun ⟨z, hz, hle⟩ f hm hf ↦ sum_le_of_le_of_vectorMajorized hz hle hm hf
  tfae_have 3 → 1 := vectorSubmajorized_of_sum_monotone_convex_le
  tfae_finish

/-- **Wolf, Submajorization, clause 2 for nonnegative vectors.** For nonnegative `x, y`,
`x ≺_w y` iff `x = M y` for a doubly substochastic matrix `M`.

**Local fix (nonnegative vectors):** the printed clause is stated for all real vectors and fails
for negative entries; see `docs/paper-gaps/wolf_ch8_submajorization_nonnegative.tex`. -/
theorem vectorSubmajorized_iff_exists_doublySubstochastic {x y : Fin d → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hy : ∀ i, 0 ≤ y i) :
    VectorSubmajorized x y ↔ ∃ M, IsDoublySubstochastic M ∧ x = M *ᵥ y := by
  classical
  constructor
  · intro h
    obtain ⟨z, hz, hle⟩ := h.exists_majorized_ge
    obtain ⟨D, hD, rfl⟩ := hz.exists_doublyStochastic
    have hDnn : ∀ i j, 0 ≤ D i j := (mem_doublyStochastic.mp hD).1
    have hDrow : ∀ i, ∑ j, D i j = 1 := fun i ↦ by
      have := congrFun (mem_doublyStochastic.mp hD).2.1 i
      simpa [mulVec, dotProduct] using this
    have hDcol : ∀ j, ∑ i, D i j = 1 := fun j ↦ by
      have := congrFun (mem_doublyStochastic.mp hD).2.2 j
      simpa [vecMul, dotProduct] using this
    let r : Fin d → ℝ := fun i ↦ if (D *ᵥ y) i = 0 then 0 else x i / (D *ᵥ y) i
    have hz0 : ∀ i, 0 ≤ (D *ᵥ y) i := fun i ↦ by
      simp only [mulVec, dotProduct]
      exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hDnn i j) (hy j)
    have hr0 : ∀ i, 0 ≤ r i := fun i ↦ by
      dsimp only [r]; split_ifs
      · exact le_rfl
      · exact div_nonneg (hx i) (hz0 i)
    have hr1 : ∀ i, r i ≤ 1 := fun i ↦ by
      dsimp only [r]; split_ifs with h0
      · norm_num
      · exact (div_le_one (lt_of_le_of_ne (hz0 i) (Ne.symm h0))).mpr (hle i)
    refine ⟨Matrix.of fun i j ↦ r i * D i j, ⟨fun i j ↦ mul_nonneg (hr0 i) (hDnn i j),
      fun i ↦ ?_, fun j ↦ ?_⟩, ?_⟩
    · simp only [of_apply, ← Finset.mul_sum, hDrow, mul_one]
      exact hr1 i
    · calc ∑ i, r i * D i j ≤ ∑ i, D i j :=
            Finset.sum_le_sum fun i _ ↦ mul_le_of_le_one_left (hDnn i j) (hr1 i)
        _ = 1 := hDcol j
    · ext i
      have hmul : (Matrix.of fun i j ↦ r i * D i j) *ᵥ y = fun i ↦ r i * (D *ᵥ y) i := by
        ext i; simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rw [hmul]
      dsimp only [r]
      split_ifs with h0
      · have := hle i; rw [h0] at this; simp only [zero_mul]; linarith [hx i]
      · field_simp
  · rintro ⟨M, ⟨hM0, hrow, hcol⟩, rfl⟩
    refine vectorSubmajorized_of_sum_monotone_convex_le fun f hm hf ↦ ?_
    -- Jensen in each row with the remaining weight on `0`.
    have hrowJ : ∀ i, f ((M *ᵥ y) i) ≤ ∑ j, M i j * f (y j) + (1 - ∑ j, M i j) * f 0 := by
      intro i
      have hw : ∀ j ∈ (Finset.univ : Finset (Option (Fin d))),
          0 ≤ Option.elim j (1 - ∑ j, M i j) (fun j ↦ M i j) := by
        intro j _; cases j with
        | none => simpa using hrow i
        | some j => exact hM0 i j
      have hsum1 : ∑ j : Option (Fin d), Option.elim j (1 - ∑ j, M i j) (fun j ↦ M i j) = 1 := by
        simp [Fintype.sum_option]
      have hJ := hf.map_sum_le (t := Finset.univ) (w := fun j : Option (Fin d) ↦
        Option.elim j (1 - ∑ j, M i j) (fun j ↦ M i j))
        (p := fun j : Option (Fin d) ↦ Option.elim j 0 y) hw hsum1 (fun _ _ ↦ Set.mem_univ _)
      simpa [Fintype.sum_option, mulVec, dotProduct, smul_eq_mul, add_comm] using hJ
    have hf0 : ∀ j, f 0 ≤ f (y j) := fun j ↦ hm (hy j)
    calc ∑ i, f ((M *ᵥ y) i)
        ≤ ∑ i, (∑ j, M i j * f (y j) + (1 - ∑ j, M i j) * f 0) :=
          Finset.sum_le_sum fun i _ ↦ hrowJ i
      _ = ∑ j, ((∑ i, M i j) * f (y j) + (1 - ∑ i, M i j) * f 0) := by
          simp only [Finset.sum_add_distrib, sub_mul, one_mul, Finset.sum_sub_distrib,
            Finset.sum_mul]
          rw [Finset.sum_comm]
          simp [Finset.sum_comm (f := fun i j ↦ M i j * f 0)]
      _ ≤ ∑ j, f (y j) := Finset.sum_le_sum fun j _ ↦ by
          nlinarith [hcol j, hf0 j, Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ hM0 i j]

end TNLean
