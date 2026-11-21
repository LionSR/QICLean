/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixUnitaryBetween
import Mathlib.Algebra.Star.StarAlgHom
import QICLean.Algebra.SkolemNoetherUnitary
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Star-algebra equivalences of full matrix algebras and rectangular unitaries

A matrix unitary between two finite coordinate spaces induces a
star-algebra equivalence of their full matrix algebras by conjugation
(`Matrix.IsUnitaryBetween.conjStarAlgEquiv`); the index types need not be equal.
Conversely, every star-algebra equivalence between full complex matrix algebras on two
nonempty finite coordinate types is conjugation by such a unitary
(`Matrix.exists_unitary_conj_of_starAlgEquiv_matrix_between`).

Moved from TNLean, `TNLean/Algebra/RectangularUnitaryConjugation.lean` and
`TNLean/Algebra/MatrixStarEquivSpatial.lean` at commit `49b78ed821` (Apache-2.0),
merged into one file.

## Conjugation by a rectangular unitary
-/

open scoped Matrix

namespace Matrix.IsUnitaryBetween

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Conjugation by a unitary between finite coordinate spaces, as an
actual star-algebra equivalence of their full matrix algebras. -/
noncomputable def conjStarAlgEquiv (U : Matrix m n ℂ) (hU : U.IsUnitaryBetween) :
    Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix m m ℂ where
  toFun A := U * A * Uᴴ
  invFun B := Uᴴ * B * U
  left_inv A := by
    change Uᴴ * (U * A * Uᴴ) * U = A
    have h : Uᴴ * (U * A * Uᴴ) * U = (Uᴴ * U) * A * (Uᴴ * U) := by
      simp only [Matrix.mul_assoc]
    rw [h, hU.1, Matrix.one_mul, Matrix.mul_one]
  right_inv B := by
    change U * (Uᴴ * B * U) * Uᴴ = B
    have h : U * (Uᴴ * B * U) * Uᴴ = (U * Uᴴ) * B * (U * Uᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [h, hU.2, Matrix.one_mul, Matrix.mul_one]
  map_mul' A B := by
    have h : U * (A * B) * Uᴴ = U * A * (Uᴴ * U) * B * Uᴴ := by
      rw [hU.1]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    rw [h]; simp only [Matrix.mul_assoc]
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_star' A := by simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  map_smul' c A := by simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- The coordinate formula for this star-algebra equivalence. -/
@[simp] theorem conjStarAlgEquiv_apply (U : Matrix m n ℂ) (hU : U.IsUnitaryBetween)
    (A : Matrix n n ℂ) : conjStarAlgEquiv U hU A = U * A * Uᴴ := rfl

end Matrix.IsUnitaryBetween

/-!
## Spatial implementation between finite full matrix algebras

A star-algebra equivalence between full complex matrix algebras on two
nonempty finite coordinate types is conjugation by a unitary between the
two coordinate spaces. Equality of their dimensions is derived from the
algebra equivalence. The same-index Skolem--Noether theorem is reused
after an explicit coordinate equivalence.

This is the finite spatial step in Schumacher--Werner,
arXiv:quant-ph/0405174, equations bruleU and bruleV, lines 980--1001.
The input is a star-algebra equivalence of full matrix algebras.
-/

open scoped Matrix

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
private theorem reindexed_conjugation (e : m ≃ n) (U : Matrix n n ℂ)
    (A : Matrix m m ℂ) :
    let W := Matrix.reindex (Equiv.refl n) e.symm U
    W * A * Wᴴ = U * Matrix.reindex e e A * Uᴴ := by
  intro W
  let B := Matrix.reindex e e A
  have hA : A = Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm B := by
    ext i j
    simp [B]
  have hstar : Wᴴ = Matrix.reindexLinearEquiv ℂ ℂ e.symm (Equiv.refl n) Uᴴ := by
    simp only [W, Matrix.conjTranspose_reindex]
    rfl
  calc
    W * A * Wᴴ =
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl n) e.symm U *
          Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm B *
            Matrix.reindexLinearEquiv ℂ ℂ e.symm (Equiv.refl n) Uᴴ := by
      rw [hstar, hA]
      rfl
    _ = Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl n) (Equiv.refl n) (U * B * Uᴴ) := by
      rw [Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
        (Equiv.refl n) e.symm e.symm,
        Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
          (Equiv.refl n) e.symm (Equiv.refl n)]
    _ = U * Matrix.reindex e e A * Uᴴ := rfl

/-- Every star-algebra equivalence of two nonzero finite full complex
matrix algebras is implemented by an actual rectangular unitary.
Its coordinate spaces need not have the same index type. Their equal
cardinalities and the implementing unitary are both derived.
Source: Schumacher--Werner, bruleU and bruleV, lines 980--1001;
Skolem--Noether in CPSV16, Appendix C.4. -/
theorem exists_unitary_conj_of_starAlgEquiv_matrix_between [Nonempty m] [Nonempty n]
    (f : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    ∃ U : Matrix n m ℂ, U.IsUnitaryBetween ∧
      ∀ A : Matrix m m ℂ, f A = U * A * Uᴴ := by
  classical
  have hdim : Fintype.card m * Fintype.card m = Fintype.card n * Fintype.card n := by
    simpa only [Module.finrank_matrix, Module.finrank_self, mul_one] using
      f.toAlgEquiv.toLinearEquiv.finrank_eq
  have hcard : Fintype.card m = Fintype.card n := by nlinarith
  let e : m ≃ n := Fintype.equivOfCardEq hcard
  let E := Matrix.matrixReindexStarAlgEquiv e
  let g := E.symm.trans f
  obtain ⟨V, hV⟩ := Matrix.exists_unitary_conj_of_starAlgEquiv_matrix g
  let W : Matrix n m ℂ := Matrix.reindex (Equiv.refl n) e.symm (V : Matrix n n ℂ)
  have hW : W.IsUnitaryBetween :=
    ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr V.prop).reindex _
      (Equiv.refl n) e.symm
  refine ⟨W, hW, ?_⟩
  intro A
  calc
    f A = g (E A) := by
      change f A = f (E.symm (E A))
      rw [StarAlgEquiv.symm_apply_apply]
    _ = (V : Matrix n n ℂ) * E A * (V : Matrix n n ℂ)ᴴ := hV (E A)
    _ = W * A * Wᴴ := (reindexed_conjugation e (V : Matrix n n ℂ) A).symm

end Matrix
