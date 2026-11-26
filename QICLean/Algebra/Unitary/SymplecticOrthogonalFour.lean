/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# A four-dimensional symplectic congruence

Let `Y = [[0,1],[-1,0]]`. The matrix
`R = (1-i)/2 * (I₄ + i (Y ⊗ Y))` is unitary and carries `Y ⊗ Y` to the
identity by transpose congruence. These are the explicit matrix identities in
arXiv:1703.09188, `paper_v2.tex` lines 1165--1185, used in the reduction of
the symplectic case of the conjugation classification to orthogonal unitaries.

Moved from TNLean, `TNLean/Algebra/SymplecticOrthogonalFour.lean`
at commit `49b78ed821` (Apache-2.0).

Moved from TNLean, `TNLean/Algebra/OrthogonalSymplecticKroneckerDeterminant.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

open scoped Kronecker

namespace Matrix

/-- The two-dimensional skew-symmetric matrix `Y` of arXiv:1703.09188,
`paper_v2.tex` lines 1115--1123 and 1172--1178. -/
def symplecticY : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The four-dimensional matrix `R = (1-i)/2 (I₄ + i(Y ⊗ Y))` of
arXiv:1703.09188, `paper_v2.tex` lines 1172--1181. The product coordinates
follow the order of the Kronecker factors in that formula. -/
noncomputable def symplecticOrthogonalR : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((1 - Complex.I) / 2) • (1 + Complex.I • (symplecticY ⊗ₖ symplecticY))

/-- The explicit matrix `R` is unitary and satisfies the transpose congruence
`Rᵀ (Y ⊗ Y) R = I₄`; see arXiv:1703.09188, `paper_v2.tex` lines 1172--1185. -/
lemma symplecticOrthogonalR_identities :
    symplecticOrthogonalRᴴ * symplecticOrthogonalR = 1 ∧
      symplecticOrthogonalRᵀ * (symplecticY ⊗ₖ symplecticY) *
        symplecticOrthogonalR = 1 := by
  constructor
  · ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      norm_num [symplecticOrthogonalR, symplecticY, Matrix.mul_apply,
        Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
      ring_nf <;> norm_num [Complex.I_sq]
  · ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      norm_num [symplecticOrthogonalR, symplecticY, Matrix.mul_apply,
        Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
      ring_nf <;> norm_num [Complex.I_sq] <;> ring

end Matrix

section

open scoped Kronecker

namespace Matrix

variable {m n R : Type*}

variable [Fintype m] [DecidableEq m] [CommRing R]

/-- The determinant of an orthogonal matrix has square one. -/
private theorem det_sq_eq_one_of_mem_orthogonalGroup (A : Matrix m m R)
    (hA : A ∈ orthogonalGroup m R) : A.det ^ 2 = 1 := by
  have hA' : A * Aᵀ = 1 := (mem_orthogonalGroup_iff (n := m) (R := R)).mp hA
  have hdet := congrArg det hA'
  simpa only [det_mul, det_transpose, det_one, pow_two] using hdet

/-- An orthogonal matrix over a domain has determinant (1) or (-1).

This is the determinant assertion used in arXiv:1703.09188, lines
1469--1477. -/
theorem det_eq_one_or_neg_one_of_mem_orthogonalGroup [NoZeroDivisors R]
    (A : Matrix m m R) (hA : A ∈ orthogonalGroup m R) :
    A.det = 1 ∨ A.det = -1 := by
  exact sq_eq_one_iff.mp (det_sq_eq_one_of_mem_orthogonalGroup A hA)

/-- Every even power of the determinant of an orthogonal matrix is one.
No assumption on the coefficient ring being a domain is needed. -/
theorem det_pow_eq_one_of_mem_orthogonalGroup_of_even (A : Matrix m m R)
    (hA : A ∈ orthogonalGroup m R) {k : ℕ} (hk : Even k) :
    A.det ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  simp only [← two_mul, pow_mul, det_sq_eq_one_of_mem_orthogonalGroup A hA,
    one_pow]

/-- The Kronecker product of orthogonal matrices of even dimensions has
determinant one, including when either index type is empty.

Source: arXiv:1703.09188, lines 1473--1477. -/
theorem det_kronecker_eq_one_of_mem_orthogonalGroup
    [Fintype n] [DecidableEq n]
    (A : Matrix m m R) (B : Matrix n n R)
    (hA : A ∈ orthogonalGroup m R) (hB : B ∈ orthogonalGroup n R)
    (hm : Even (Fintype.card m)) (hn : Even (Fintype.card n)) :
    (A ⊗ₖ B).det = 1 := by
  rw [det_kronecker,
    det_pow_eq_one_of_mem_orthogonalGroup_of_even A hA hn,
    det_pow_eq_one_of_mem_orthogonalGroup_of_even B hB hm,
    one_mul]

/-- A Kronecker product of symplectic matrices has determinant one, with no
parity or nonemptiness hypothesis beyond their symplectic index types.

Source: arXiv:1703.09188, lines 1473--1477. -/
theorem det_kronecker_eq_one_of_mem_symplecticGroup
    {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (A : Matrix (p ⊕ p) (p ⊕ p) R)
    (B : Matrix (q ⊕ q) (q ⊕ q) R)
    (hA : A ∈ symplecticGroup p R) (hB : B ∈ symplecticGroup q R) :
    (A ⊗ₖ B).det = 1 := by
  rw [det_kronecker, SymplecticGroup.det_eq_one hA,
    SymplecticGroup.det_eq_one hB]
  simp

end Matrix

end
