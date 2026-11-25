/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.Permutation.CommutantDimension

/-!
# Operators on single copies and tensor powers

On the `k`-th tensor power of `ℂ^Ω`, with basis indexed by `Fin k → Ω`, this file defines the
operator `⊗_{j ∈ s} A_j` acting by `A_j` on the copies `j ∈ s`, the operator `A^{(j)}` acting by
`A` on the `j`-th copy, the tensor power `A^{⊗k}` and the diagonal action `Δ(A) = ∑_j A^{(j)}`,
with their entries, products and adjoints. Tensor powers commute with the copy permutations.

## Main declarations

* `TensorPower.partialTensor`, `TensorPower.siteOp`, `TensorPower.tensorPow`,
  `TensorPower.diagOp` — the operators `⊗_{j ∈ s} A_j`, `A^{(j)}`, `A^{⊗k}`, `Δ(A)`.
* `TensorPower.tensorPow_mul`, `TensorPower.conjTranspose_tensorPow` — tensor powers are
  multiplicative and commute with the adjoint.
* `TensorPower.commute_permOp_copyPerm_tensorPow` — tensor powers commute with the copy
  permutations.
-/

open Finset Matrix PermutationRepresentation

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}

/-- The operator `⊗_{j ∈ s} A_j`, acting by `A_j` on the copies `j ∈ s` and by the identity
on the others. -/
def partialTensor (s : Finset (Fin k)) (A : Fin k → Matrix Ω Ω ℂ) :
    Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
  fun x y => if ∀ i ∉ s, x i = y i then ∏ j ∈ s, A j (x j) (y j) else 0

omit [Fintype Ω] in
theorem partialTensor_apply (s : Finset (Fin k)) (A : Fin k → Matrix Ω Ω ℂ)
    (x y : Fin k → Ω) :
    partialTensor s A x y = if ∀ i ∉ s, x i = y i then ∏ j ∈ s, A j (x j) (y j) else 0 :=
  rfl

omit [Fintype Ω] in
@[simp]
theorem partialTensor_univ_apply (A : Fin k → Matrix Ω Ω ℂ) (x y : Fin k → Ω) :
    partialTensor univ A x y = ∏ j, A j (x j) (y j) := by
  simp [partialTensor_apply]

omit [Fintype Ω] in
@[simp]
theorem partialTensor_empty (A : Fin k → Matrix Ω Ω ℂ) : partialTensor ∅ A = 1 := by
  ext x y
  simp only [partialTensor_apply, notMem_empty, not_false_eq_true, forall_const,
    prod_empty, one_apply]
  by_cases h : x = y
  · simp [h]
  · have h' : ¬∀ i, x i = y i := fun h' => h (funext h')
    simp [h, h']

omit [Fintype Ω] in
theorem partialTensor_congr {s : Finset (Fin k)} {A B : Fin k → Matrix Ω Ω ℂ}
    (h : ∀ j ∈ s, A j = B j) : partialTensor s A = partialTensor s B := by
  ext x y
  simp only [partialTensor_apply]
  rw [prod_congr rfl fun j hj => by rw [h j hj]]

/-- Tensor products over disjoint sets of copies multiply. -/
theorem partialTensor_mul_partialTensor {s t : Finset (Fin k)} (hst : Disjoint s t)
    (A B : Fin k → Matrix Ω Ω ℂ) :
    partialTensor s A * partialTensor t B =
      partialTensor (s ∪ t) (fun j => if j ∈ s then A j else B j) := by
  ext x z
  rw [mul_apply]
  -- the only contributing intermediate configuration
  set y : Fin k → Ω := fun i => if i ∈ s then z i else x i with hy
  rw [Finset.sum_eq_single y]
  · simp only [partialTensor_apply]
    by_cases hxz : ∀ i ∉ s ∪ t, x i = z i
    · have h1 : ∀ i ∉ s, x i = y i := fun i hi => by simp [hy, hi]
      have h2 : ∀ i ∉ t, y i = z i := by
        intro i hi
        by_cases his : i ∈ s
        · simp [hy, his]
        · simp only [hy, his, ite_false]
          exact hxz i (by simp [his, hi])
      rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left hxz, prod_union hst]
      congr 1
      · refine prod_congr rfl fun j hj => ?_
        simp [hj, hy]
      · refine prod_congr rfl fun j hj => ?_
        have hjs : j ∉ s := disjoint_right.mp hst hj
        simp [hjs, hy]
    · rw [ite_eq_right hxz]
      push Not at hxz
      obtain ⟨i, hi, hne⟩ := hxz
      simp only [mem_union, not_or] at hi
      by_cases h2 : ∀ i ∉ t, y i = z i
      · exact absurd (by simpa [hy, hi.1] using h2 i hi.2) hne
      · rw [ite_eq_right h2, mul_zero]
  · intro y' _ hy'
    simp only [partialTensor_apply]
    by_cases h1 : ∀ i ∉ s, x i = y' i
    · by_cases h2 : ∀ i ∉ t, y' i = z i
      · exfalso
        apply hy'
        funext i
        by_cases his : i ∈ s
        · simp only [hy, his, ite_true]
          exact h2 i (disjoint_left.mp hst his)
        · simp only [hy, his, ite_false]
          exact (h1 i his).symm
      · rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]
  · simp

/-- Tensor products over disjoint sets of copies commute. -/
theorem commute_partialTensor {s t : Finset (Fin k)} (hst : Disjoint s t)
    (A B : Fin k → Matrix Ω Ω ℂ) : Commute (partialTensor s A) (partialTensor t B) := by
  rw [Commute, SemiconjBy, partialTensor_mul_partialTensor hst,
    partialTensor_mul_partialTensor hst.symm, union_comm]
  refine partialTensor_congr fun j hj => ?_
  by_cases hjs : j ∈ s
  · simp [hjs, disjoint_left.mp hst hjs]
  · have hjt : j ∈ t := by simpa [hjs] using hj
    simp [hjs, hjt]

/-- The operator `A^{(j)}`: `A` acting on the `j`-th copy. -/
def siteOp (j : Fin k) (A : Matrix Ω Ω ℂ) : Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
  partialTensor {j} fun _ => A

/-- The operator `A^{⊗k}`. -/
def tensorPow (A : Matrix Ω Ω ℂ) : Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
  partialTensor univ fun _ => A

/-- The diagonal action `Δ(A) = ∑_j A^{(j)}`. -/
def diagOp (A : Matrix Ω Ω ℂ) : Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
  ∑ j, siteOp j A

omit [Fintype Ω] in
theorem siteOp_apply (j : Fin k) (A : Matrix Ω Ω ℂ) (x y : Fin k → Ω) :
    siteOp j A x y = if ∀ i, i ≠ j → x i = y i then A (x j) (y j) else 0 := by
  simp [siteOp, partialTensor_apply]

theorem siteOp_mul_siteOp (j : Fin k) (A B : Matrix Ω Ω ℂ) :
    siteOp j A * siteOp j B = siteOp j (A * B) := by
  ext x z
  rw [mul_apply, siteOp_apply, mul_apply]
  have hsupp : ∀ y ∈ (univ : Finset (Fin k → Ω)), y ∉ univ.image (Function.update x j) →
      siteOp j A x y * siteOp j B y z = 0 := by
    intro y _ hy
    rw [siteOp_apply, ite_eq_right, zero_mul]
    intro h
    apply hy
    refine mem_image.mpr ⟨y j, mem_univ _, ?_⟩
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, h i hij]
  rw [← sum_subset (subset_univ _) hsupp,
    sum_image (fun a _ b _ h => by simpa using congrFun h j)]
  by_cases hxz : ∀ i, i ≠ j → x i = z i
  · rw [ite_eq_left hxz]
    refine sum_congr rfl fun a _ => ?_
    rw [siteOp_apply, siteOp_apply, ite_eq_left, ite_eq_left]
    · simp
    · intro i hij; simp [hij, hxz i hij]
    · intro i hij; simp [hij]
  · rw [ite_eq_right hxz]
    refine sum_eq_zero fun a _ => ?_
    push Not at hxz
    obtain ⟨i, hij, hne⟩ := hxz
    rw [siteOp_apply j B, ite_eq_right, mul_zero]
    intro h
    exact hne (by simpa [hij] using h i hij)

omit [Fintype Ω] in
@[simp]
theorem siteOp_one (j : Fin k) : siteOp j (1 : Matrix Ω Ω ℂ) = 1 := by
  ext x y
  rw [siteOp_apply, one_apply, one_apply]
  by_cases h : x = y
  · simp [h]
  · by_cases h' : ∀ i, i ≠ j → x i = y i
    · have hj : x j ≠ y j := fun hj => h (funext fun i => by
        by_cases hij : i = j
        · subst hij; exact hj
        · exact h' i hij)
      simp [h, hj]
    · simp [h, h']

theorem siteOp_pow (j : Fin k) (A : Matrix Ω Ω ℂ) (m : ℕ) :
    siteOp j A ^ m = siteOp j (A ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, siteOp_mul_siteOp, ← pow_succ]

theorem commute_siteOp (i j : Fin k) (A : Matrix Ω Ω ℂ) :
    Commute (siteOp i A) (siteOp j A) := by
  by_cases hij : i = j
  · rw [hij]
  · exact commute_partialTensor (disjoint_singleton.mpr hij) _ _

omit [Fintype Ω] in
theorem diagOp_apply (A : Matrix Ω Ω ℂ) (x y : Fin k → Ω) :
    diagOp A x y = ∑ j, if ∀ i, i ≠ j → x i = y i then A (x j) (y j) else 0 := by
  simp only [diagOp, Matrix.sum_apply, siteOp_apply]

omit [Fintype Ω] in
theorem tensorPow_apply (A : Matrix Ω Ω ℂ) (x y : Fin k → Ω) :
    tensorPow A x y = ∏ j, A (x j) (y j) := by
  simp [tensorPow]

theorem tensorPow_mul (A B : Matrix Ω Ω ℂ) :
    tensorPow (k := k) (A * B) = tensorPow A * tensorPow B := by
  ext x y
  simp only [tensorPow_apply, mul_apply]
  rw [Finset.prod_univ_sum]
  exact Fintype.sum_congr _ _ fun z => Finset.prod_mul_distrib

omit [Fintype Ω] in
theorem tensorPow_one : tensorPow (k := k) (1 : Matrix Ω Ω ℂ) = 1 := by
  ext x y
  rw [tensorPow_apply]
  by_cases h : x = y
  · subst h; simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), one_apply_ne h]

omit [Fintype Ω] in
theorem conjTranspose_tensorPow (A : Matrix Ω Ω ℂ) :
    (tensorPow (k := k) A)ᴴ = tensorPow Aᴴ := by
  ext x y
  simp [tensorPow_apply, conjTranspose_apply, star_prod]

/-- Tensor powers commute with the copy permutations. -/
theorem commute_permOp_copyPerm_tensorPow (A : Matrix Ω Ω ℂ) (σ : Equiv.Perm (Fin k)) :
    Commute (permOp (copyPerm Ω k) σ) (tensorPow A) := by
  refine commute_permOp_of_apply_eq _ σ fun x y => ?_
  simp only [tensorPow_apply, copyPerm_apply]
  exact Fintype.prod_equiv σ⁻¹ _ _ fun j => rfl

end TensorPower
