/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Entrywise images of matrices over a ring embedded in the complex numbers

Identities between explicit matrices can be verified by deciding them over a commutative ring
with decidable equality, such as the integers or a ring of algebraic integers, and then
transported to the complex matrices by applying a ring homomorphism `f : R →+* ℂ` to each entry.
The entrywise image preserves matrix arithmetic, finite sums, matrix units, submatrices,
transposes and block-diagonal matrices, and it is injective when `f` is.

Moved from TNLean, `TNLean/Algebra/ComplexOfRing.lean` at commit `0dab608b96` (Apache-2.0).
Changes: the declarations live in the namespace `Matrix` instead of `MPSTensor`, and
`complexOfRing_injective` is not restated, being `Matrix.map_injective`.

## Main definitions

* `Matrix.complexOfRing`: the entrywise image of a matrix along a ring homomorphism into the
  complex numbers.

## Main results

* `Matrix.complexOfRing_mul`, `Matrix.complexOfRing_one`: the entrywise image is multiplicative
  and preserves the identity matrix.
* `Matrix.complexOfRing_mul_eq_one`: the entrywise images of two matrices whose product is the
  identity multiply to the identity.
* `Matrix.complexOfRing_single`: the entrywise image of a matrix unit is the corresponding complex
  matrix unit.
* `Matrix.complexOfRing_ne_zero`: the entrywise image along an injective ring homomorphism of a
  nonzero matrix is nonzero; injectivity itself is `Matrix.map_injective`.
-/

open scoped Matrix

namespace Matrix

variable {R : Type*} [CommRing R] (f : R →+* ℂ)

/-- The entrywise image of a matrix over `R` along a ring homomorphism `f : R →+* ℂ`. -/
def complexOfRing {m n : Type*} (X : Matrix m n R) : Matrix m n ℂ :=
  X.map f

@[simp] theorem complexOfRing_apply {m n : Type*} (X : Matrix m n R) (i : m) (j : n) :
    complexOfRing f X i j = f (X i j) := rfl

theorem complexOfRing_mul {m n o : Type*} [Fintype n] (X : Matrix m n R) (Y : Matrix n o R) :
    complexOfRing f (X * Y) = complexOfRing f X * complexOfRing f Y :=
  Matrix.map_mul

theorem complexOfRing_one {n : Type*} [DecidableEq n] :
    complexOfRing f (1 : Matrix n n R) = 1 :=
  Matrix.map_one f (map_zero f) (map_one f)

theorem complexOfRing_zero {m n : Type*} : complexOfRing f (0 : Matrix m n R) = 0 :=
  Matrix.map_zero f (map_zero f)

theorem complexOfRing_add {m n : Type*} (X Y : Matrix m n R) :
    complexOfRing f (X + Y) = complexOfRing f X + complexOfRing f Y :=
  Matrix.map_add f (map_add f) X Y

theorem complexOfRing_neg {m n : Type*} (X : Matrix m n R) :
    complexOfRing f (-X) = -complexOfRing f X :=
  Matrix.map_neg f (map_neg f) X

theorem complexOfRing_sub {m n : Type*} (X Y : Matrix m n R) :
    complexOfRing f (X - Y) = complexOfRing f X - complexOfRing f Y :=
  Matrix.map_sub f (map_sub f) X Y

theorem complexOfRing_smul {m n : Type*} (c : R) (X : Matrix m n R) :
    complexOfRing f (c • X) = f c • complexOfRing f X :=
  Matrix.map_smulₛₗ f f c (fun a => map_mul f c a) X

theorem complexOfRing_sum {m n κ : Type*} (t : Finset κ) (g : κ → Matrix m n R) :
    complexOfRing f (∑ x ∈ t, g x) = ∑ x ∈ t, complexOfRing f (g x) :=
  map_sum (f.toAddMonoidHom.mapMatrix (m := m) (n := n)) g t

theorem complexOfRing_single {m n : Type*} [DecidableEq m] [DecidableEq n] (i : m) (j : n) :
    complexOfRing f (Matrix.single i j (1 : R)) = Matrix.single i j (1 : ℂ) := by
  ext a b
  simp only [complexOfRing_apply, Matrix.single_apply]
  split <;> simp

theorem complexOfRing_submatrix {m n m' n' : Type*} (X : Matrix m n R) (g : m' → m)
    (h : n' → n) : complexOfRing f (X.submatrix g h) = (complexOfRing f X).submatrix g h := rfl

theorem complexOfRing_transpose {m n : Type*} (X : Matrix m n R) :
    complexOfRing f Xᵀ = (complexOfRing f X)ᵀ := rfl

theorem complexOfRing_blockDiagonal' {o : Type*} [DecidableEq o] {m' : o → Type*}
    (M : ∀ k, Matrix (m' k) (m' k) R) :
    complexOfRing f (Matrix.blockDiagonal' M) =
      Matrix.blockDiagonal' fun k => complexOfRing f (M k) :=
  Matrix.blockDiagonal'_map M f (map_zero f)

/-- The entrywise images of two matrices whose product is the identity multiply to the
identity. -/
theorem complexOfRing_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n] {G H : Matrix n n R}
    (h : G * H = 1) : complexOfRing f G * complexOfRing f H = 1 := by
  rw [← complexOfRing_mul, h, complexOfRing_one]

variable {f} in
theorem complexOfRing_ne_zero (hf : Function.Injective f) {m n : Type*} {X : Matrix m n R}
    (hX : X ≠ 0) : complexOfRing f X ≠ 0 :=
  fun h => hX (Matrix.map_injective hf (h.trans (complexOfRing_zero f).symm))

end Matrix
