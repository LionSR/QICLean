/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import QICLean.Entropy.ConditionalMovement.LogCompression

/-!
# Identity extensions of invariant operators

Let P be an orthogonal projection. For an operator A commuting with P,
the operator P A P + (1 - P) agrees with A on the range of P and with the
identity on its orthogonal complement. Products and real functional calculus
have the same restriction. Consequently, commutation on the range of P
implies commutation of the identity extensions. A positive definite operator
has a positive definite identity extension.

These identities apply to the symmetric-subspace commutation in the transport
argument of the area-law manuscript. Operator lower bounds remain separate
assertions: the eigenvalue on the complementary subspace is one.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, `06-transport.tex`, lines 273–276 and `transport:mean-def`, at manuscript
  commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* The symmetric-subspace restriction is recorded in
  https://github.com/LionSR/QICLean/blob/main/docs/paper-gaps/oai26_transport_crossband_commutation.tex.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Completing an invariant-subspace operator agrees with that operator on
the subspace. OpenAI area-law manuscript, `06-transport.tex`, lines 273–276. -/
theorem compression_add_one_sub_mul_projection
    {P A : Matrix n n ℂ} (hP : IsStarProjection P) (hPA : Commute P A) :
    (P * A * P + (1 - P)) * P = A * P := by
  simp only [add_mul, hP.one_sub_mul_self, add_zero,
    hP.isIdempotentElem.mul_mul_self, hPA.eq]

/-- Products of identity extensions agree with the original products on the
invariant subspace. OpenAI area-law manuscript, `06-transport.tex`, lines 273–276. -/
theorem compression_add_one_sub_mul_compression_add_one_sub
    {P A B : Matrix n n ℂ} (hP : IsStarProjection P)
    (hPA : Commute P A) (hPB : Commute P B) :
    (P * A * P + (1 - P)) * (P * B * P + (1 - P)) =
      A * B * P + (1 - P) := by
  simp only [add_mul, mul_add, mul_sub, sub_mul, mul_one, one_mul,
    mul_assoc, ← hPA.eq, ← hPB.eq, hP.isIdempotentElem.mul_self_mul]
  simp only [hP.isIdempotentElem.eq, sub_self, add_zero, ← mul_assoc,
    hPA.eq, hP.isIdempotentElem.mul_mul_self, add_sub_cancel_left]

/-- The identity extension of a positive definite invariant operator is
positive definite. Auxiliary to the symmetric-subspace metrics of OpenAI's
area-law manuscript, `06-transport.tex`, lines 273–276. -/
theorem PosDef.compression_add_one_sub
    {P A : Matrix n n ℂ} (hA : A.PosDef) (hP : IsStarProjection P)
    (hPA : Commute P A) : (P * A * P + (1 - P)).PosDef := by
  let := hA.isUnit.invertible
  have hPAP : (P * A * P).PosSemidef := by
    simpa only [hP.isSelfAdjoint.isHermitian.eq] using
      hA.posSemidef.conjTranspose_mul_mul_same P
  apply (hPAP.add (nonneg_iff_posSemidef.mp hP.one_sub.nonneg)).posDef_iff_isUnit.mpr
  refine isUnit_iff_exists_inv.mpr ⟨P * ⅟A * P + (1 - P), ?_⟩
  rw [compression_add_one_sub_mul_compression_add_one_sub hP hPA hPA.invOf_right]
  simp only [mul_invOf_self, one_mul, ← add_sub_assoc, add_sub_cancel_left]

/-- Commutation on an invariant subspace yields commutation of its identity
extensions. OpenAI area-law manuscript, `06-transport.tex`, lines 273–276. -/
theorem commute_compression_add_one_sub_of_mul_projection_eq
    {P A B : Matrix n n ℂ} (hP : IsStarProjection P)
    (hPA : Commute P A) (hPB : Commute P B)
    (hAB : A * B * P = B * A * P) :
    Commute (P * A * P + (1 - P)) (P * B * P + (1 - P)) := by
  change (P * A * P + (1 - P)) * (P * B * P + (1 - P)) =
    (P * B * P + (1 - P)) * (P * A * P + (1 - P))
  rw [compression_add_one_sub_mul_compression_add_one_sub hP hPA hPB,
    compression_add_one_sub_mul_compression_add_one_sub hP hPB hPA, hAB]

/-- Functional calculus of an identity extension agrees with the original
functional calculus on the invariant subspace. OpenAI area-law manuscript,
`06-transport.tex`, lines 273–276 and `transport:mean-def`. -/
theorem cfc_compression_add_one_sub_mul_projection
    {P A : Matrix n n ℂ} (hP : IsStarProjection P) (hA : A.IsHermitian)
    (hPA : Commute P A) (f : ℝ → ℝ) :
    cfc f (P * A * P + (1 - P)) * P = P * cfc f A := by
  have hE : (P * A * P + (1 - P)).IsHermitian := by
    simpa only [hP.isSelfAdjoint.isHermitian.eq] using
      (isHermitian_mul_mul_conjTranspose P hA).add hP.one_sub.isSelfAdjoint.isHermitian
  exact ConditionalMovement.QuantumSSA.cfc_intertwine hE hA P
    ((compression_add_one_sub_mul_projection hP hPA).trans hPA.eq.symm) f

end Matrix
