/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Sandwich transport along an intertwiner of Hermitian matrices

A common rectangular intertwiner of two Hermitian matrices transports their
sandwiches on arbitrary matrix directions. This algebraic identity is used
with the resolvents and normalization factors in OpenAI's area-law manuscript,
Lemma 7.2, 06-transport.tex, lines 157–172, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a.

Moved from TNLean, `TNLean/MPS/MPU/Symmetry/TimeReversal/TimeReversalTraceGauge.lean` at commit
`021ba0bd19` (Apache-2.0).
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

section

open scoped Matrix

namespace Matrix

/-- A trace pairing is unchanged by an intertwining pair of changes of basis.
The identities `S L = R S` and `K R = I` give
`tr(S L M K) = tr(S M)` by cyclicity.

This is the final trace step in arXiv:1703.09188, Proposition
`prop:sigma-well-defined`, lines 1624--1630. -/
lemma trace_mul_mul_eq_of_intertwine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S L R K M : Matrix ι ι ℂ) (hSL : S * L = R * S) (hKR : K * R = 1) :
    Matrix.trace (S * (L * M * K)) = Matrix.trace (S * M) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hSL, Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc K R, hKR, Matrix.one_mul]

end Matrix

end
