/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Majorization.VectorMajorization
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The orthostochastic characterization of majorization

For real vectors, `x ≺ y` holds exactly when `x = O^{∘2} y` for a real orthogonal matrix `O`,
that is, `xᵢ = ∑ⱼ Oᵢⱼ² yⱼ`. This is clause 3 of Wolf's Theorem 8.4.

The proof is Horn's induction. After sorting both vectors decreasingly, one plane rotation in
the coordinates `0` and `j` makes the first diagonal entry of `R diag(y) Rᵀ` equal to `x₀`, where
`j` is the first index with `y_j ≤ x₀`. The remaining diagonal block is `diag(z')`, and the
remaining coordinates of `x` are majorized by `z'`; the induction hypothesis supplies an
orthogonal matrix for them, and the block sum with `1` composed with `R` gives `O` with
`diag(O diag(y) Oᵀ) = x`.

## Main results

* `TNLean.VectorMajorized.exists_orthostochastic`: Horn's theorem.
* `TNLean.vectorMajorized_iff_exists_orthostochastic`: clause 3 of Wolf's Theorem 8.4.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8, Theorem 8.4, local source
  `Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 220--251.
* A. Horn, *Doubly stochastic matrices and the diagonal of a rotation matrix*, Amer. J. Math.
  76 (1954), 620--630.
-/

open Finset Matrix
open scoped BigOperators

namespace TNLean

variable {d : ℕ}

/-- A strictly monotone map from `Fin m` to `Fin d` does not decrease indices. -/
private theorem val_le_of_strictMono {m : ℕ} {e : Fin m → Fin d} (he : StrictMono e)
    (k : Fin m) : k.val ≤ (e k).val := by
  suffices h : ∀ t : ℕ, ∀ k : Fin m, k.val = t → t ≤ (e k).val from h _ k rfl
  intro t
  induction t with
  | zero => intro _ _; exact Nat.zero_le _
  | succ t ih =>
    intro k hk
    have hlt : (⟨t, by omega⟩ : Fin m) < k := by
      change t < k.val; omega
    have h1 := ih ⟨t, by omega⟩ rfl
    have h2 : (e ⟨t, by omega⟩).val < (e k).val := he hlt
    omega

/-- For an antitone vector, the sum over any `m` coordinates is at most the sum of the first
`m` coordinates. -/
theorem sum_le_vectorPrefix_of_antitone {f : Fin d → ℝ} (hf : Antitone f) (S : Finset (Fin d)) :
    ∑ i ∈ S, f i ≤ vectorPrefix f S.card := by
  classical
  let e := S.orderEmbOfFin rfl
  have hS : ∑ i ∈ S, f i = ∑ k : Fin S.card, f (e k) := by
    rw [← Finset.sum_coe_sort S]
    exact (Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv.symm _ _ (fun i ↦ by
      simp only [e]
      rw [← Finset.coe_orderIsoOfFin_apply]
      exact congrArg (fun a : S ↦ f a) ((S.orderIsoOfFin rfl).apply_symm_apply i).symm)).trans rfl
  have hcard : S.card ≤ d := by simpa using Finset.card_le_univ S
  have hP : vectorPrefix f S.card = ∑ k : Fin S.card, f (Fin.castLE hcard k) := by
    unfold vectorPrefix
    refine Finset.sum_bij' (fun i hi ↦ ⟨i.val, (Finset.mem_filter.mp hi).2⟩)
      (fun k _ ↦ Fin.castLE hcard k) (by simp) (fun k _ ↦ by simp) (by simp) (by simp)
      (fun i _ ↦ rfl)
  rw [hS, hP]
  refine Finset.sum_le_sum fun k _ ↦ hf ?_
  change (Fin.castLE hcard k).val ≤ (e k).val
  simpa using val_le_of_strictMono (S.orderEmbOfFin rfl).strictMono k

/-- For an arbitrary vector, the sum over any `m` coordinates is at most the sum of its `m`
largest coordinates. -/
theorem sum_le_vectorPrefix_decreasingSort (z : Fin d → ℝ) (S : Finset (Fin d)) :
    ∑ i ∈ S, z i ≤ vectorPrefix (decreasingSort z) S.card := by
  classical
  let π := decreasingPerm z
  have h := sum_le_vectorPrefix_of_antitone (antitone_decreasingSort z) (S.map π.symm.toEmbedding)
  rw [Finset.card_map] at h
  refine le_trans (le_of_eq ?_) h
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [decreasingSort, π]

/-- The diagonal of `O diag(y) Oᵀ` is the orthostochastic image `∑ⱼ Oᵢⱼ² yⱼ`. -/
theorem mul_diagonal_mul_transpose_apply_self {n : Type*} [Fintype n] [DecidableEq n]
    (O : Matrix n n ℝ) (y : n → ℝ) (i : n) :
    (O * diagonal y * Oᵀ) i i = ∑ j, O i j ^ 2 * y j := by
  simp only [mul_apply, diagonal_apply, transpose_apply, mul_ite, mul_zero, sum_ite_eq',
    mem_univ, ite_true]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- Reindexing an orthogonal matrix along two equivalences gives an orthogonal matrix. -/
theorem submatrix_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℝ} (hO : O ∈ orthogonalGroup n ℝ) (e f : n ≃ n) :
    O.submatrix e f ∈ orthogonalGroup n ℝ := by
  rw [mem_orthogonalGroup_iff] at hO ⊢
  rw [transpose_submatrix, submatrix_mul_equiv O Oᵀ e f e, hO, submatrix_one_equiv]

/-- The block sum of `1` and an orthogonal matrix on `Fin (n+1)`. -/
def blockOne {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i k ↦ Fin.cases (Fin.cases 1 (fun _ ↦ 0) k)
    (fun i' ↦ Fin.cases 0 (fun k' ↦ O i' k') k) i

@[simp] theorem blockOne_zero_zero {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) :
    blockOne O 0 0 = 1 := rfl
@[simp] theorem blockOne_zero_succ {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    blockOne O 0 k.succ = 0 := rfl
@[simp] theorem blockOne_succ_zero {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    blockOne O i.succ 0 = 0 := rfl
@[simp] theorem blockOne_succ_succ {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (i k : Fin n) :
    blockOne O i.succ k.succ = O i k := rfl

theorem blockOne_mem_orthogonalGroup {n : ℕ} {O : Matrix (Fin n) (Fin n) ℝ}
    (hO : O ∈ orthogonalGroup (Fin n) ℝ) : blockOne O ∈ orthogonalGroup (Fin (n + 1)) ℝ := by
  rw [mem_orthogonalGroup_iff] at hO ⊢
  ext i k
  refine Fin.cases ?_ (fun i' ↦ ?_) i <;> refine Fin.cases ?_ (fun k' ↦ ?_) k <;>
    simp only [mul_apply, transpose_apply, Fin.sum_univ_succ, blockOne_zero_zero,
      blockOne_zero_succ, blockOne_succ_zero, blockOne_succ_succ, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, zero_add, mul_one, one_apply]
  · simp
  · simp [(Fin.succ_ne_zero k').symm]
  · simp [Fin.succ_ne_zero i']
  · have h := congrFun (congrFun hO i') k'
    simp only [mul_apply, transpose_apply, one_apply] at h
    simpa [Fin.succ_inj] using h

section Rotation

variable {n : ℕ}

/-- The rotation in the coordinate plane spanned by `0` and `j` with `cos² = c`. -/
noncomputable def planeRotation (j : Fin (n + 1)) (c : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun p l ↦
    if p = 0 then (if l = 0 then Real.sqrt c else if l = j then Real.sqrt (1 - c) else 0)
    else if p = j then (if l = 0 then -Real.sqrt (1 - c) else if l = j then Real.sqrt c else 0)
    else if l = p then 1 else 0

private theorem sum_two {j : Fin (n + 1)} (hj : j ≠ 0) (a b : ℝ) (g : Fin (n + 1) → ℝ) :
    ∑ l, (if l = 0 then a else if l = j then b else 0) * g l = a * g 0 + b * g j := by
  rw [Fintype.sum_eq_add 0 j hj.symm (fun l hl ↦ by simp [hl.1, hl.2])]
  simp [hj]

private theorem sum_one {p : Fin (n + 1)} (g : Fin (n + 1) → ℝ) :
    ∑ l, (if l = p then (1 : ℝ) else 0) * g l = g p := by
  simp

theorem planeRotation_mem_orthogonalGroup {j : Fin (n + 1)} (hj : j ≠ 0) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    planeRotation j c ∈ orthogonalGroup (Fin (n + 1)) ℝ := by
  rw [mem_orthogonalGroup_iff]
  have hs : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0
  have ht : Real.sqrt (1 - c) * Real.sqrt (1 - c) = 1 - c := Real.mul_self_sqrt (by linarith)
  have hj' : (0 : Fin (n + 1)) ≠ j := Ne.symm hj
  ext p q
  simp only [mul_apply, transpose_apply, one_apply]
  by_cases hp0 : p = 0
  · subst hp0
    simp only [planeRotation, of_apply, ite_true]
    rw [sum_two hj]
    by_cases hq0 : q = 0
    · subst hq0; simp only [ite_true, hj, ite_false]; linarith
    · have hq0' : (0 : Fin (n + 1)) ≠ q := Ne.symm hq0
      by_cases hqj : q = j
      · subst hqj; simp [hq0, hq0']; ring
      · have hqj' : j ≠ q := Ne.symm hqj
        simp [hq0, hq0', hqj, hqj']
  · have hp0' : (0 : Fin (n + 1)) ≠ p := Ne.symm hp0
    by_cases hpj : p = j
    · subst hpj
      simp only [planeRotation, of_apply, hp0, ite_false, ite_true]
      rw [sum_two hp0]
      by_cases hq0 : q = 0
      · subst hq0; simp [hp0]; ring
      · have hq0' : (0 : Fin (n + 1)) ≠ q := Ne.symm hq0
        by_cases hqj : q = p
        · subst hqj; simp [hq0]; linarith
        · have hqj' : p ≠ q := Ne.symm hqj
          simp [hq0, hq0', hqj, hqj']
    · have hpj' : j ≠ p := Ne.symm hpj
      simp only [planeRotation, of_apply, hp0, hpj, ite_false]
      rw [sum_one]
      by_cases hq0 : q = 0
      · subst hq0; simp [hp0, hpj]
      · by_cases hqj : q = j
        · subst hqj; simp [hq0, hpj, hp0]
        · simp only [hq0, hqj, ite_false]

/-- The conjugated diagonal matrix: its `0,0` entry is `c y₀ + (1 - c) y_j`, and off the
coordinate `0` it is diagonal, with `j,j` entry `(1 - c) y₀ + c y_j`. -/
theorem planeRotation_conj_diagonal {j : Fin (n + 1)} (hj : j ≠ 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (y : Fin (n + 1) → ℝ) :
    (planeRotation j c * diagonal y * (planeRotation j c)ᵀ) 0 0 = c * y 0 + (1 - c) * y j ∧
    ∀ p q : Fin (n + 1), p ≠ 0 → q ≠ 0 →
      (planeRotation j c * diagonal y * (planeRotation j c)ᵀ) p q =
        if p = q then (if p = j then (1 - c) * y 0 + c * y j else y p) else 0 := by
  have hs : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0
  have ht : Real.sqrt (1 - c) * Real.sqrt (1 - c) = 1 - c := Real.mul_self_sqrt (by linarith)
  have hj' : (0 : Fin (n + 1)) ≠ j := Ne.symm hj
  have hrow : ∀ p q : Fin (n + 1),
      (planeRotation j c * diagonal y * (planeRotation j c)ᵀ) p q =
        ∑ l, planeRotation j c p l * (y l * planeRotation j c q l) := by
    intro p q
    simp only [mul_apply, diagonal_apply, transpose_apply, mul_ite, mul_zero, sum_ite_eq',
      mem_univ, ite_true]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  constructor
  · rw [hrow]
    simp only [planeRotation, of_apply, ite_true]
    rw [sum_two hj]
    simp only [ite_true, hj, ite_false]
    linear_combination (y 0) * hs + (y j) * ht
  · intro p q hp hq
    have hp' : (0 : Fin (n + 1)) ≠ p := Ne.symm hp
    have hq' : (0 : Fin (n + 1)) ≠ q := Ne.symm hq
    rw [hrow]
    by_cases hpj : p = j
    · subst hpj
      simp only [planeRotation, of_apply, hp, ite_false, ite_true]
      rw [sum_two hp]
      by_cases hqj : q = p
      · subst hqj
        simp only [hq, ite_false, ite_true]
        linear_combination (y 0) * ht + (y q) * hs
      · have hqj' : p ≠ q := Ne.symm hqj
        simp [hq, hq', hqj, hqj']
    · have hpj' : j ≠ p := Ne.symm hpj
      simp only [planeRotation, of_apply, hp, hpj, ite_false]
      rw [sum_one]
      by_cases hqj : q = j
      · subst hqj; simp [hp, hpj, hq]
      · simp only [hq, hqj, ite_false]
        by_cases hpq : p = q <;> simp_all

end Rotation

/-- Splitting off the first coordinate of a prefix sum. -/
theorem vectorPrefix_succ {n : ℕ} (v : Fin (n + 1) → ℝ) (t : ℕ) :
    vectorPrefix v (t + 1) = v 0 + vectorPrefix (v ∘ Fin.succ) t := by
  classical
  unfold vectorPrefix
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  simp [Fin.val_succ]

/-- Horn's induction step for decreasingly sorted vectors. -/
private theorem exists_orthostochastic_of_antitone {n : ℕ}
    (IH : ∀ x y : Fin n → ℝ, VectorMajorized x y →
      ∃ O ∈ orthogonalGroup (Fin n) ℝ, ∀ i, x i = ∑ j, O i j ^ 2 * y j)
    {x y : Fin (n + 1) → ℝ} (hx : Antitone x) (hy : Antitone y)
    (hpre : ∀ k ≤ n + 1, vectorPrefix x k ≤ vectorPrefix y k) (hsum : ∑ i, x i = ∑ i, y i) :
    ∃ O ∈ orthogonalGroup (Fin (n + 1)) ℝ, ∀ i, x i = ∑ j, O i j ^ 2 * y j := by
  classical
  cases n with
  | zero =>
    refine ⟨1, one_mem _, fun i ↦ ?_⟩
    fin_cases i
    simpa [Matrix.one_apply] using hsum
  | succ m =>
  -- The first coordinates and the last coordinate of `y`.
  have h1 : x 0 ≤ y 0 := by
    have := hpre 1 (by omega)
    simpa [vectorPrefix_succ] using this
  have hlast : y (Fin.last (m + 1)) ≤ x 0 := by
    have hyl : ∑ i, y (Fin.last (m + 1)) ≤ ∑ i, y i :=
      Finset.sum_le_sum fun i _ ↦ hy (Fin.le_last i)
    have hx0 : ∑ i, x i ≤ ∑ i : Fin (m + 2), x 0 :=
      Finset.sum_le_sum fun i _ ↦ hx (Fin.zero_le i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hyl hx0
    have hpos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
    nlinarith
  -- The first index with `y j ≤ x₀`, moved off `0`.
  let S := Finset.univ.filter (fun i : Fin (m + 2) ↦ y i ≤ x 0)
  have hS : S.Nonempty := ⟨Fin.last (m + 1), by simp [S, hlast]⟩
  let j0 := S.min' hS
  have hj0S : y j0 ≤ x 0 := (Finset.mem_filter.mp (S.min'_mem hS)).2
  let j : Fin (m + 2) := if j0 = 0 then 1 else j0
  have hj : j ≠ 0 := by
    dsimp only [j]; split_ifs with h
    · exact Fin.zero_lt_one.ne'
    · exact h
  have hyj : y j ≤ x 0 := by
    dsimp only [j]; split_ifs with h
    · rw [h] at hj0S; exact (hy (Fin.zero_le 1)).trans hj0S
    · exact hj0S
  have hbelow : ∀ i : Fin (m + 2), 0 < i → i < j → x 0 ≤ y i := by
    intro i hi0 hij
    dsimp only [j] at hij
    split_ifs at hij with h
    · exact absurd hij (not_lt.mpr (Fin.one_le_of_ne_zero hi0.ne'))
    · by_contra hlt
      have hmem : i ∈ S := by simp [S, le_of_lt (not_le.mp hlt)]
      exact absurd (S.min'_le i hmem) (not_le.mpr hij)
  -- The rotation parameter.
  let c : ℝ := if y 0 = y j then 1 else (x 0 - y j) / (y 0 - y j)
  have hyj0 : y j ≤ y 0 := hyj.trans h1
  have hc : 0 ≤ c ∧ c ≤ 1 ∧ c * y 0 + (1 - c) * y j = x 0 := by
    dsimp only [c]
    split_ifs with h
    · refine ⟨by norm_num, le_rfl, ?_⟩; linarith
    · have hd : 0 < y 0 - y j := sub_pos.mpr (lt_of_le_of_ne hyj0 (Ne.symm h))
      refine ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).mpr (by linarith), ?_⟩
      field_simp
      ring
  obtain ⟨hc0, hc1, hcx⟩ := hc
  -- The reduced vector.
  let z : Fin (m + 1) → ℝ := fun k ↦ if k.succ = j then y 0 + y j - x 0 else y k.succ
  have hz : ∀ k, z k = y k.succ + if k = j.pred hj then y 0 - x 0 else 0 := by
    intro k
    simp only [z]
    by_cases hk : k = j.pred hj
    · subst hk; simp only [Fin.succ_pred, ite_true]; ring
    · have : k.succ ≠ j := fun h ↦ hk (Fin.ext (by
        have h' := congrArg Fin.val h
        simp only [Fin.val_succ] at h'
        simp only [Fin.val_pred]
        omega))
      simp [this, hk]
  have hzsum : ∑ k, z k = ∑ k : Fin (m + 1), y k.succ + (y 0 - x 0) := by
    simp only [hz, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hxs : Antitone (x ∘ Fin.succ) := hx.comp_monotone (Fin.strictMono_succ.monotone)
  have hmaj : VectorMajorized (x ∘ Fin.succ) z := by
    refine ⟨fun t ht ↦ ?_, ?_⟩
    · rw [decreasingSort_eq_self hxs]
      let T := Finset.univ.filter (fun k : Fin (m + 1) ↦ k.val < t)
      have hTcard : T.card = t := by
        simpa [T, Nat.min_eq_right ht] using (Fin.card_filter_val_lt (n := m + 1) (m := t))
      have hT := sum_le_vectorPrefix_decreasingSort z T
      rw [hTcard] at hT
      refine le_trans ?_ hT
      have hxT : vectorPrefix (x ∘ Fin.succ) t = ∑ k ∈ T, x k.succ := rfl
      rw [hxT]
      by_cases hjt : t < j.val
      · refine Finset.sum_le_sum fun k hk ↦ ?_
        have hkt : k.val < t := (Finset.mem_filter.mp hk).2
        have hkj : k.succ < j := by
          change k.val + 1 < j.val; omega
        have hne : k.succ ≠ j := hkj.ne
        simp only [z, hne, ite_false]
        exact (hx (Fin.zero_le _)).trans (hbelow _ (Fin.succ_pos k) hkj)
      · have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun h ↦ hj (Fin.ext h))
        have hmem : j.pred hj ∈ T := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [Fin.val_pred]
          omega
        have hzT : ∑ k ∈ T, z k = ∑ k ∈ T, y k.succ + (y 0 - x 0) := by
          simp only [hz, Finset.sum_add_distrib, Finset.sum_ite_eq', hmem, ite_true]
        have hyT : vectorPrefix (y ∘ Fin.succ) t = ∑ k ∈ T, y k.succ := rfl
        have hp := hpre (t + 1) (by omega)
        rw [vectorPrefix_succ, vectorPrefix_succ, hxT, hyT] at hp
        rw [hzT]
        linarith
    · simp only [Function.comp_apply]
      rw [hzsum]
      have hx' := Fin.sum_univ_succ x
      have hy' := Fin.sum_univ_succ y
      linarith
  obtain ⟨O', hO', hx'⟩ := IH _ _ hmaj
  -- Assemble the orthogonal matrix.
  let B := blockOne O'
  let R := planeRotation j c
  refine ⟨B * R, mul_mem (blockOne_mem_orthogonalGroup hO')
    (planeRotation_mem_orthogonalGroup hj hc0 hc1), fun i ↦ ?_⟩
  rw [← mul_diagonal_mul_transpose_apply_self]
  have hconj : B * R * diagonal y * (B * R)ᵀ = B * (R * diagonal y * Rᵀ) * Bᵀ := by
    rw [transpose_mul]; simp only [Matrix.mul_assoc]
  rw [hconj]
  obtain ⟨hA0, hA⟩ := planeRotation_conj_diagonal hj hc0 hc1 y
  set A := R * diagonal y * Rᵀ with hAdef
  have hAs : ∀ a b : Fin (m + 1), A a.succ b.succ = if a = b then z a else 0 := by
    intro a b
    rw [hA a.succ b.succ (Fin.succ_ne_zero a) (Fin.succ_ne_zero b)]
    by_cases hab : a = b
    · subst hab
      simp only [ite_true, z]
      split_ifs <;> linarith
    · simp [hab, Fin.succ_inj]
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · simp only [mul_apply, transpose_apply, Fin.sum_univ_succ, B, blockOne_zero_zero,
      blockOne_zero_succ, zero_mul, Finset.sum_const_zero, add_zero, one_mul, mul_one, mul_zero]
    rw [hA0, hcx]
  · have hexp : (B * A * Bᵀ) k.succ k.succ =
        ∑ b : Fin (m + 1), (∑ a : Fin (m + 1), O' k a * A a.succ b.succ) * O' k b := by
      simp only [mul_apply, transpose_apply]
      rw [Fin.sum_univ_succ]
      simp only [B, blockOne_succ_zero, mul_zero, zero_add, blockOne_succ_succ]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [Fin.sum_univ_succ]
      simp only [blockOne_succ_zero, zero_mul, zero_add, blockOne_succ_succ]
    rw [hexp]
    simp only [hAs, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hk := hx' k
    simp only [Function.comp_apply] at hk
    rw [hk]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    ring

/-- **Horn's theorem.** If `x ≺ y`, then `xᵢ = ∑ⱼ Oᵢⱼ² yⱼ` for a real orthogonal matrix `O`.
Wolf, Theorem 8.4, clause 3. -/
theorem VectorMajorized.exists_orthostochastic :
    ∀ {d : ℕ} {x y : Fin d → ℝ}, VectorMajorized x y →
      ∃ O ∈ orthogonalGroup (Fin d) ℝ, ∀ i, x i = ∑ j, O i j ^ 2 * y j := by
  intro d
  induction d with
  | zero => intro x y _; exact ⟨1, one_mem _, fun i ↦ i.elim0⟩
  | succ n ih =>
    intro x y hxy
    let σ := decreasingPerm x
    let τ := decreasingPerm y
    have hmaj : VectorMajorized (decreasingSort x) (decreasingSort y) :=
      (vectorMajorized_comp_perm_iff x y σ τ).mpr hxy
    have hxs := antitone_decreasingSort x
    have hys := antitone_decreasingSort y
    obtain ⟨O, hO, hOx⟩ := exists_orthostochastic_of_antitone (fun x y h ↦ ih h) hxs hys
      (by simpa [decreasingSort_eq_self hxs, decreasingSort_eq_self hys] using hmaj.1) hmaj.2
    refine ⟨O.submatrix σ.symm τ.symm, submatrix_mem_orthogonalGroup hO _ _, fun i ↦ ?_⟩
    have h := hOx (σ.symm i)
    simp only [decreasingSort, Function.comp_apply, σ, Equiv.apply_symm_apply] at h
    rw [h]
    refine (Fintype.sum_equiv τ.symm _ _ (fun j ↦ ?_)).symm
    simp [submatrix_apply, σ, τ]

/-- **Wolf's Theorem 8.4, clause 3.** For real vectors, `x ≺ y` holds exactly when
`xᵢ = ∑ⱼ Oᵢⱼ² yⱼ` for some real orthogonal matrix `O`. Wolf, Chapter 8, Theorem 8.4; local source
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 220--251. -/
theorem vectorMajorized_iff_exists_orthostochastic (x y : Fin d → ℝ) :
    VectorMajorized x y ↔
      ∃ O ∈ orthogonalGroup (Fin d) ℝ, ∀ i, x i = ∑ j, O i j ^ 2 * y j := by
  refine ⟨VectorMajorized.exists_orthostochastic, ?_⟩
  rintro ⟨O, hO, hx⟩
  have hrow : O * Oᵀ = 1 := (mem_orthogonalGroup_iff (Fin d) ℝ).mp hO
  have hcol : Oᵀ * O = 1 := (mem_orthogonalGroup_iff' (Fin d) ℝ).mp hO
  refine (vectorMajorized_iff_exists_doublyStochastic x y).mpr ⟨Matrix.of fun i j ↦ O i j ^ 2,
    ?_, ?_⟩
  · rw [mem_doublyStochastic]
    refine ⟨fun i j ↦ sq_nonneg _, ?_, ?_⟩
    · ext i
      have h := congrFun (congrFun hrow i) i
      simp only [mul_apply, transpose_apply, one_apply_eq] at h
      simpa [mulVec, dotProduct, sq] using h
    · ext j
      have h := congrFun (congrFun hcol j) j
      simp only [mul_apply, transpose_apply, one_apply_eq] at h
      simpa [vecMul, dotProduct, sq, mul_comm] using h
  · ext i
    simp [hx i, mulVec, dotProduct]

end TNLean
