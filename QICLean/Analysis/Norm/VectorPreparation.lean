/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Norm.MatrixKroneckerContraction

/-!
# Preparing a vector on a fresh factor, and contracting a factor with a bra

The preparation `prepMatrix e v` of a vector `v ∈ ℂ^α` is the matrix from `ℂ^n` to `ℂ^m` that
maps `|x⟩` to `v ⊗ |x⟩`, the basis of `m` read as `α × n` through the equivalence `e`. Appending
`v` behind the input is the preparation along `Equiv.prodComm`, and a matrix `G` followed by
appending `v` is `prepMatrix (Equiv.prodComm _ _) v * G`. A preparation is `‖v‖` times an
isometry.

The effect `effectMatrix η S` is the bra `⟨η| ⊗ 1` from `ℂ^{ι × S}` to `ℂ^S`; it is the adjoint
of the preparation of `η` in front (`effectMatrix_eq_conjTranspose`).

## Main definitions

* `Matrix.prepMatrix` — the preparation of a vector on a fresh factor.
* `Matrix.effectMatrix` — the contraction of the first factor with a bra.

## Main results

* `Matrix.prepMatrix_mul_apply`, `Matrix.toEuclideanLin_prepMatrix_prodComm` — entries and the
  action on vectors.
* `Matrix.reindex_symm_prepMatrix` — a preparation with its rows relabelled.
* `Matrix.conjTranspose_mul_prepMatrix`, `Matrix.norm_prepMatrix_le`, `Matrix.norm_prepMatrix` —
  a preparation is `‖v‖` times an isometry.
* `Matrix.effectMatrix_eq_conjTranspose`, `Matrix.conjTranspose_prepMatrix`,
  `Matrix.toEuclideanLin_effectMatrix_vecKron`, `Matrix.norm_effectMatrix_le` — effects.
-/

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace Matrix

/-! ### Preparations -/

section Prep

variable {m n α : Type*} [DecidableEq n]

/-- The preparation of the vector `v ∈ ℂ^α` on a fresh factor: the matrix from `ℂ^n` to `ℂ^m`
that maps `|x⟩` to `v ⊗ |x⟩`, the basis of `m` read as `α × n` through `e`. -/
def prepMatrix (e : m ≃ α × n) (v : EuclideanSpace ℂ α) : Matrix m n ℂ :=
  Matrix.of fun y x ↦ if (e y).2 = x then v (e y).1 else 0

/-- The entries of a preparation. -/
@[simp] theorem prepMatrix_apply (e : m ≃ α × n) (v : EuclideanSpace ℂ α) (y : m) (x : n) :
    prepMatrix e v y x = if (e y).2 = x then v (e y).1 else 0 :=
  rfl

/-- A matrix followed by a preparation: the entry at `y` is the coefficient of the fresh part
of `y` times the entry of the matrix at the old part. -/
theorem prepMatrix_mul_apply {k : Type*} [Fintype n] (e : m ≃ α × n) (v : EuclideanSpace ℂ α)
    (A : Matrix n k ℂ) (y : m) (z : k) :
    (prepMatrix e v * A) y z = v (e y).1 * A (e y).2 z := by
  simp [mul_apply, ite_mul, zero_mul, Finset.sum_ite_eq]

/-- A matrix followed by appending `v` behind its output: the entry at `(y, w)` is
`v w * A y z`. -/
@[simp] theorem prepMatrix_prodComm_mul_apply {k : Type*} [Fintype n] (v : EuclideanSpace ℂ α)
    (A : Matrix n k ℂ) (x : n × α) (z : k) :
    (prepMatrix (Equiv.prodComm n α) v * A) x z = v x.2 * A x.1 z :=
  prepMatrix_mul_apply _ v A x z

/-- A preparation is the preparation along the identity of `α × n`, its rows read through
`e`. -/
theorem prepMatrix_eq_submatrix (e : m ≃ α × n) (v : EuclideanSpace ℂ α) :
    prepMatrix e v = (prepMatrix (Equiv.refl (α × n)) v).submatrix e id :=
  rfl

/-- A preparation with its rows read along `e` is the preparation along `e` followed by the
reading `f` of the basis. -/
theorem reindex_symm_prepMatrix {l : Type*} (e : l ≃ m) (f : m ≃ α × n)
    (v : EuclideanSpace ℂ α) :
    reindex e.symm (Equiv.refl n) (prepMatrix f v) = prepMatrix (e.trans f) v :=
  rfl

/-- Appending a vector behind the input sends `u` to `u ⊗ v`. -/
theorem toEuclideanLin_prepMatrix_prodComm [Fintype n] (v : EuclideanSpace ℂ α)
    (u : EuclideanSpace ℂ n) :
    toEuclideanLin (prepMatrix (Equiv.prodComm n α) v) u = EuclideanSpace.vecKron u v := by
  ext ⟨x, a⟩
  simp only [EuclideanSpace.vecKron, mul_comm]
  simp only [toLpLin_apply, mulVec, dotProduct, prepMatrix_apply, Equiv.prodComm_apply,
    Prod.fst_swap, Prod.snd_swap, PiLp.toLp_apply]
  rw [Fintype.sum_eq_single x fun i hi ↦ by simp [Ne.symm hi]]
  simp

variable [Fintype m] [Fintype n] [Fintype α]

omit [Fintype n] in
/-- A preparation is `‖v‖` times an isometry. -/
theorem conjTranspose_mul_prepMatrix (e : m ≃ α × n) (v : EuclideanSpace ℂ α) :
    (prepMatrix e v)ᴴ * prepMatrix e v = ((‖v‖ ^ 2 : ℝ) : ℂ) • 1 := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
  · have : IsEmpty m := e.isEmpty
    rw [Subsingleton.elim v 0, norm_zero]
    ext x x'
    simp [mul_apply]
  let : Fintype n := Fintype.ofInjective (fun x ↦ e.symm (a₀, x)) fun _ _ h ↦ by simpa using h
  ext x x'
  rw [mul_apply, ← e.symm.sum_comp, Fintype.sum_prod_type, Matrix.smul_apply, one_apply]
  split_ifs with h
  · subst h
    simp only [conjTranspose_apply, prepMatrix_apply, Equiv.apply_symm_apply, apply_ite star,
      star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, smul_eq_mul, mul_one, EuclideanSpace.norm_sq_eq, Complex.ofReal_sum,
      Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Complex.conj_mul', Complex.star_def]
  · simp only [conjTranspose_apply, prepMatrix_apply, Equiv.apply_symm_apply, apply_ite star,
      star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, smul_zero]
    exact Finset.sum_eq_zero fun a _ ↦ ite_eq_right_iff.mpr fun h' ↦ absurd h'.symm h

omit [Fintype m] [Fintype α] in
/-- The identity matrix has operator norm at most `1`, and `0` on an empty basis. -/
private theorem norm_one_le_one : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (1 : Matrix n n ℂ)
  rw [conjTranspose_one, Matrix.one_mul] at h
  nlinarith [norm_nonneg (1 : Matrix n n ℂ)]

/-- A preparation of `v` has operator norm at most `‖v‖`. -/
theorem norm_prepMatrix_le (e : m ≃ α × n) (v : EuclideanSpace ℂ α) :
    ‖prepMatrix e v‖ ≤ ‖v‖ := by
  have h := l2_opNorm_conjTranspose_mul_self (prepMatrix e v)
  rw [conjTranspose_mul_prepMatrix, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)] at h
  have h1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := norm_one_le_one
  by_contra hlt
  have hlt' := mul_lt_mul'' (not_le.mp hlt) (not_le.mp hlt) (norm_nonneg v) (norm_nonneg v)
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖v‖)]

/-- A preparation of `v` on a nonempty basis has operator norm `‖v‖`. -/
theorem norm_prepMatrix [Nonempty n] (e : m ≃ α × n) (v : EuclideanSpace ℂ α) :
    ‖prepMatrix e v‖ = ‖v‖ := by
  have h := l2_opNorm_conjTranspose_mul_self (prepMatrix e v)
  rw [conjTranspose_mul_prepMatrix, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _), norm_one, mul_one] at h
  nlinarith [norm_nonneg (prepMatrix e v), norm_nonneg v]

end Prep

/-! ### Effects -/

section Effect

variable {ι S m : Type*} [DecidableEq S]

/-- The effect `⟨η| ⊗ 1 : ℂ^{ι × S} → ℂ^S`: its entry at `(s, (i, s'))` is `conj (η i)` when
`s = s'` and `0` otherwise. -/
def effectMatrix (η : EuclideanSpace ℂ ι) (S : Type*) [DecidableEq S] : Matrix S (ι × S) ℂ :=
  Matrix.of fun s x ↦ if s = x.2 then star (η x.1) else 0

/-- The entries of an effect. -/
@[simp] theorem effectMatrix_apply (η : EuclideanSpace ℂ ι) (s : S) (x : ι × S) :
    effectMatrix η S s x = if s = x.2 then star (η x.1) else 0 :=
  rfl

/-- The effect is the adjoint of the preparation of `η` in front. -/
theorem effectMatrix_eq_conjTranspose (η : EuclideanSpace ℂ ι) :
    effectMatrix η S = (prepMatrix (Equiv.refl (ι × S)) η)ᴴ := by
  ext s ⟨i, s'⟩
  by_cases h : s = s'
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- The adjoint of a preparation is the effect, its columns read through `e`. -/
theorem conjTranspose_prepMatrix (e : m ≃ ι × S) (η : EuclideanSpace ℂ ι) :
    (prepMatrix e η)ᴴ = (effectMatrix η S).submatrix id e := by
  rw [prepMatrix_eq_submatrix, conjTranspose_submatrix, effectMatrix_eq_conjTranspose]

/-- The effect sends a product vector `h ⊗ v` to `⟪η, h⟫ v`. -/
theorem toEuclideanLin_effectMatrix_vecKron [Fintype ι] [DecidableEq ι] [Fintype S]
    (η h : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ S) :
    toEuclideanLin (effectMatrix η S) (EuclideanSpace.vecKron h v) = ⟪η, h⟫_ℂ • v := by
  ext s
  simp only [EuclideanSpace.vecKron, toLpLin_toLp, toLin'_apply, mulVec, dotProduct,
    effectMatrix_apply, RCLike.star_def, mul_comm, mul_ite, zero_mul, Fintype.sum_prod_type,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, PiLp.inner_apply, RCLike.inner_apply,
    PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- An effect with a unit vector is a contraction. -/
theorem norm_effectMatrix_le [Fintype ι] [DecidableEq ι] [Fintype S] {η : EuclideanSpace ℂ ι}
    (hη : ‖η‖ = 1) :
    ‖effectMatrix η S‖ ≤ 1 := by
  rw [effectMatrix_eq_conjTranspose, l2_opNorm_conjTranspose]
  exact (norm_prepMatrix_le _ _).trans hη.le

end Effect

end Matrix
