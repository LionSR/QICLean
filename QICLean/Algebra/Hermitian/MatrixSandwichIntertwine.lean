/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Sandwich transport along an intertwiner of Hermitian matrices

A common rectangular intertwiner of two Hermitian matrices transports their
sandwiches on arbitrary matrix directions. This algebraic identity is used
with the resolvents and normalization factors in OpenAI's area-law manuscript,
Lemma 7.2, 06-transport.tex, lines 157–172, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

namespace Matrix

variable {α n m : Type*} [NonUnitalSemiring α] [StarRing α]
variable [Fintype n] [Fintype m]

/-- Taking adjoints reverses an intertwining equation for Hermitian matrices.
Auxiliary to OpenAI's area-law manuscript, Lemma 7.2,
06-transport.tex, lines 157–172, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem IsHermitian.conjTranspose_intertwine
    {L₁ : Matrix n n α} {L₂ : Matrix m m α}
    (hL₁ : L₁.IsHermitian) (hL₂ : L₂.IsHermitian)
    (J : Matrix n m α) (hJ : L₁ * J = J * L₂) :
    L₂ * Jᴴ = Jᴴ * L₁ := by
  simpa only [conjTranspose_mul, hL₁.eq, hL₂.eq] using
    (congrArg Matrix.conjTranspose hJ).symm

/-- Hermitian intertwining transports a sandwich on every direction.
Auxiliary to OpenAI's area-law manuscript, Lemma 7.2,
06-transport.tex, lines 157–172, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem IsHermitian.sandwich_intertwine
    {L₁ : Matrix n n α} {L₂ : Matrix m m α}
    (hL₁ : L₁.IsHermitian) (hL₂ : L₂.IsHermitian)
    (J : Matrix n m α) (hJ : L₁ * J = J * L₂)
    (H : Matrix m m α) :
    L₁ * (J * H * Jᴴ) * L₁ = J * (L₂ * H * L₂) * Jᴴ := by
  have hstar : Jᴴ * L₁ = L₂ * Jᴴ :=
    (hL₁.conjTranspose_intertwine hL₂ J hJ).symm
  simp only [← Matrix.mul_assoc, hJ]
  simp only [Matrix.mul_assoc, hstar]

end Matrix
