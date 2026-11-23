/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Matrix.PEquiv
import QICLean.Analysis.Norm.MatrixL2Contraction
import QICLean.Analysis.Norm.KroneckerOperatorNorm

/-!
# Kronecker products, relabellings and the `L²` operator norm

Elementary facts about Kronecker products of complex matrices and vectors, and about relabelling
their coordinates along equivalences, used when two copies of a system are rearranged.

## Main declarations

* `Matrix.kronecker_kronecker_eq_submatrix`: `(A₁ ⊗ B₁) ⊗ (A₂ ⊗ B₂)` is `(A₁ ⊗ A₂) ⊗ (B₁ ⊗ B₂)`
  in the coordinates `Equiv.prodProdProdComm`.
* `Matrix.l2_opNorm_kronecker_le_one`: the Kronecker product of two contractions is a
  contraction, from `Matrix.l2_opNorm_kronecker_le`.
* `Matrix.l2_opNorm_toMatrix_toPEquiv_le`: the matrix of a bijection of coordinates is a
  contraction.
* `Matrix.norm_submatrix_equiv_le`, `Commute.submatrix_equiv`: relabelling both coordinates of a
  square matrix along one equivalence.
* `EuclideanSpace.vecKron`, `EuclideanSpace.norm_vecKron`: the product vector `x ⊗ y` and
  `‖x ⊗ y‖ = ‖x‖ ‖y‖`.
* `EuclideanSpace.pairSwap`, `EuclideanSpace.pairMap`, `EuclideanSpace.norm_pairMap_le`: a pair
  vector with its factors exchanged, and transformed by `A ⊗ B`; contractions do not increase
  its norm.

Moved from TNLean, `TNLean/Algebra/MatrixKroneckerContraction.lean` at commit
`49b78ed821` (Apache-2.0).
-/

open scoped Kronecker Matrix.Norms.L2Operator

namespace Matrix

section Shuffle

variable {α β γ δ α' β' γ' δ' : Type*}

/-- `(A₁ ⊗ B₁) ⊗ (A₂ ⊗ B₂)` is `(A₁ ⊗ A₂) ⊗ (B₁ ⊗ B₂)` in shuffled coordinates. -/
theorem kronecker_kronecker_eq_submatrix (A₁ : Matrix α α' ℂ) (B₁ : Matrix β β' ℂ)
    (A₂ : Matrix γ γ' ℂ) (B₂ : Matrix δ δ' ℂ) :
    (A₁ ⊗ₖ B₁) ⊗ₖ (A₂ ⊗ₖ B₂) =
      ((A₁ ⊗ₖ A₂) ⊗ₖ (B₁ ⊗ₖ B₂)).submatrix (Equiv.prodProdProdComm α β γ δ)
        (Equiv.prodProdProdComm α' β' γ' δ') := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩
  simp only [kroneckerMap_apply, submatrix_apply, Equiv.prodProdProdComm, Equiv.coe_fn_mk]
  ring

end Shuffle

section Norms

variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq m]
  [DecidableEq n] [DecidableEq m'] [DecidableEq n']

omit [DecidableEq m'] [DecidableEq n'] in
/-- The Kronecker product of two contractions is a contraction. -/
theorem l2_opNorm_kronecker_le_one {A : Matrix m' m ℂ} {B : Matrix n' n ℂ} (hA : ‖A‖ ≤ 1)
    (hB : ‖B‖ ≤ 1) : ‖A ⊗ₖ B‖ ≤ 1 :=
  (l2_opNorm_kronecker_le A B).trans (by nlinarith [norm_nonneg A, norm_nonneg B])

omit [DecidableEq m] in
/-- The matrix of a bijection of coordinates is a contraction. -/
theorem l2_opNorm_toMatrix_toPEquiv_le (f : m ≃ n) :
    ‖(f.toPEquiv.toMatrix : Matrix m n ℂ)‖ ≤ 1 := by
  have h : (f.toPEquiv.toMatrix : Matrix m n ℂ) = reindex f.symm (Equiv.refl n) 1 := by
    rw [← Matrix.mul_one (f.toPEquiv.toMatrix : Matrix m n ℂ), PEquiv.toMatrix_toPEquiv_mul]
    rfl
  rw [h]
  exact (l2_opNorm_reindex_le _ _ _).trans (IsStarProjection.one _).norm_le

/-- Relabelling both coordinates of a square matrix along one equivalence does not increase
the operator norm. -/
theorem norm_submatrix_equiv_le (M : Matrix n n ℂ) (e : m ≃ n) : ‖M.submatrix e e‖ ≤ ‖M‖ :=
  l2_opNorm_reindex_le e.symm e.symm M

end Norms

section Relabel

variable {m n m' n' : Type*}

/-- The matrix of a product of bijections is the Kronecker product of their matrices. -/
theorem toMatrix_toPEquiv_prodCongr [DecidableEq m'] [DecidableEq n'] (f : m ≃ m')
    (g : n ≃ n') :
    ((f.prodCongr g).toPEquiv.toMatrix : Matrix (m × n) (m' × n') ℂ) =
      (f.toPEquiv.toMatrix : Matrix m m' ℂ) ⊗ₖ (g.toPEquiv.toMatrix : Matrix n n' ℂ) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    kroneckerMap_apply, Equiv.prodCongr_apply, Prod.map, Prod.mk.injEq]
  by_cases h₁ : f i = k <;> by_cases h₂ : g j = l <;> simp [h₁, h₂]

/-- Relabelling the coordinates of the matrix of a bijection. -/
theorem toMatrix_toPEquiv_submatrix [DecidableEq n] {l l' : Type*} [DecidableEq l'] (f : m ≃ n)
    (e₁ : l ≃ m) (e₂ : l' ≃ n) :
    (f.toPEquiv.toMatrix : Matrix m n ℂ).submatrix e₁ e₂ =
      ((e₁.trans (f.trans e₂.symm)).toPEquiv.toMatrix : Matrix l l' ℂ) := by
  ext i j
  simp only [submatrix_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.trans_apply,
    Option.mem_some_iff, Equiv.symm_apply_eq]

/-- Relabelling along `e` and then along `e.symm` is the identity. -/
theorem submatrix_symm_submatrix (X : Matrix n n ℂ) (e : m ≃ n) :
    (X.submatrix e e).submatrix e.symm e.symm = X := by
  simp [submatrix_submatrix]

end Relabel

end Matrix

/-- Commuting square matrices commute in all coordinates. -/
theorem Commute.submatrix_equiv {m n : Type*} [Fintype m] [Fintype n] {X Y : Matrix n n ℂ}
    (h : Commute X Y) (e : m ≃ n) : Commute (X.submatrix e e) (Y.submatrix e e) := by
  change X.submatrix e e * Y.submatrix e e = Y.submatrix e e * X.submatrix e e
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h.eq]

namespace EuclideanSpace

variable {m n : Type*}

/-- Relabelling the coordinates of a vector does not change its norm. -/
theorem norm_toLp_comp_equiv [Fintype m] [Fintype n] (e : m ≃ n) (f : n → ℂ) :
    ‖(WithLp.toLp 2 (f ∘ e) : EuclideanSpace ℂ m)‖ = ‖(WithLp.toLp 2 f : EuclideanSpace ℂ n)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact e.sum_comp fun j => ‖f j‖ ^ 2

/-- The product vector `x ⊗ y`. -/
noncomputable def vecKron (x : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n) :
    EuclideanSpace ℂ (m × n) :=
  WithLp.toLp 2 fun p => x p.1 * y p.2

theorem vecKron_sub_left (x x' : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n) :
    vecKron x y - vecKron x' y = vecKron (x - x') y := by
  ext ⟨i, j⟩
  simp [vecKron, sub_mul]

theorem vecKron_sub_right (x : EuclideanSpace ℂ m) (y y' : EuclideanSpace ℂ n) :
    vecKron x y - vecKron x y' = vecKron x (y - y') := by
  ext ⟨i, j⟩
  simp [vecKron, mul_sub]

variable [Fintype m] [Fintype n]

/-- `‖x ⊗ y‖ = ‖x‖ ‖y‖`. -/
theorem norm_vecKron (x : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n) :
    ‖vecKron x y‖ = ‖x‖ * ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  congr 1
  simp only [vecKron, Fintype.sum_prod_type, norm_mul, mul_pow, Finset.sum_mul_sum]

/-- `‖x ⊗ x - y ⊗ y‖ ≤ ‖x - y‖ (‖x‖ + ‖y‖)`. -/
theorem norm_vecKron_self_sub_le (x y : EuclideanSpace ℂ m) :
    ‖vecKron x x - vecKron y y‖ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) := by
  have h : vecKron x x - vecKron y y = vecKron (x - y) x + vecKron y (x - y) := by
    rw [← vecKron_sub_left, ← vecKron_sub_right]
    abel
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_vecKron, norm_vecKron]
  linarith [mul_comm ‖y‖ ‖x - y‖]

section Pair

variable {α β α' β' : Type*}

/-- A pair vector with its two factors exchanged: its coefficient at `(b, a)` is the coefficient
of `η` at `(a, b)`. -/
noncomputable def pairSwap (η : EuclideanSpace ℂ (α × β)) : EuclideanSpace ℂ (β × α) :=
  WithLp.toLp 2 fun x => η x.swap

/-- The coefficients of a pair vector with its factors exchanged. -/
@[simp] theorem pairSwap_apply (η : EuclideanSpace ℂ (α × β)) (b : β) (a : α) :
    pairSwap η (b, a) = η (a, b) :=
  rfl

/-- Exchanging the two factors of a pair vector keeps its norm. -/
@[simp] theorem norm_pairSwap [Fintype α] [Fintype β] (η : EuclideanSpace ℂ (α × β)) :
    ‖pairSwap η‖ = ‖η‖ :=
  norm_toLp_comp_equiv (Equiv.prodComm β α) fun x => η x

/-- The pair vector `η` transformed by `A ⊗ B`, the map `A` on the first factor and `B` on the
second. -/
noncomputable def pairMap [Fintype α] [Fintype β] (A : Matrix α' α ℂ) (B : Matrix β' β ℂ)
    (η : EuclideanSpace ℂ (α × β)) : EuclideanSpace ℂ (α' × β') :=
  WithLp.toLp 2 (Matrix.mulVec (A ⊗ₖ B) fun x => η x)

/-- Transforming a pair vector by two contractions does not increase its norm. -/
theorem norm_pairMap_le [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Fintype α']
    [Fintype β'] {A : Matrix α' α ℂ} {B : Matrix β' β ℂ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (η : EuclideanSpace ℂ (α × β)) : ‖pairMap A B η‖ ≤ ‖η‖ :=
  (Matrix.l2_opNorm_mulVec (A ⊗ₖ B) η).trans
    (mul_le_of_le_one_left (norm_nonneg _) (Matrix.l2_opNorm_kronecker_le_one hA hB))

end Pair

end EuclideanSpace
