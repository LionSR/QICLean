/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtBounds

/-!
# Elementary product bounds for operator Schmidt rank

An elementary Kronecker product has operator Schmidt rank at most one,
as does the identity. Empty local index types are included. These are the
product-rank base cases in AKLV, arXiv:1301.1162v1, Lemma 4.2, lines
626--657, and the physical parity-product bound in ALVV,
arXiv:1602.08828v2, `thm:FF-tH`, lines 1543--1568.
-/

open scoped Kronecker

namespace Matrix

/-- An elementary Kronecker product has operator Schmidt rank at most one.
AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 626--657. -/
theorem operatorSchmidtRank_kronecker_le_one {a b : Type*} [Fintype a] [Finite b]
    (A : Matrix a a ℂ) (B : Matrix b b ℂ) : operatorSchmidtRank (A ⊗ₖ B) ≤ 1 := by
  exact operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    ⟨fun _ : Fin 1 ↦ A, fun _ : Fin 1 ↦ B, by simp⟩

/-- The identity has operator Schmidt rank at most one, including empty
local factors. This is the empty-product case of the parity-rank bound
in ALVV, arXiv:1602.08828v2, `thm:FF-tH`, lines 1543--1568. -/
theorem operatorSchmidtRank_one_le {a b : Type*} [Fintype a] [DecidableEq a]
    [Finite b] [DecidableEq b] :
    operatorSchmidtRank (1 : Matrix (a × b) (a × b) ℂ) ≤ 1 := by
  simpa only [one_kronecker_one] using
    operatorSchmidtRank_kronecker_le_one (1 : Matrix a a ℂ) (1 : Matrix b b ℂ)

end Matrix
