/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Topology.Instances.Matrix
import QICLean.Analysis.FunctionalCalculus.MatrixSqrt
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The functional calculus under unitary conjugation

For a unitary `x` and Hermitian matrices `A` and `B = x A xᴴ`, the Hermitian functional calculus
satisfies `f(B) = x f(A) xᴴ`; in particular the inverse square root on the support transforms the
same way. These identities compare the normalization matrices of two compact decompositions of
one matrix (arXiv:1703.09188, lines 479--502). The file also records the cancellation
`A z† (z B) = A B` of a unitary `z` between two rectangular factors.

Moved from TNLean, `TNLean/Algebra/MatrixUnitaryConjCFC.lean` and
`TNLean/Algebra/UnitaryContraction.lean` at commit `49b78ed821` (Apache-2.0), merged into one file.
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian functional calculus commutes with unitary conjugation:
if $B=xAx^\dagger$ then $f(B)=xf(A)x^\dagger$. -/
theorem IsHermitian.cfc_eq_of_eq_unitary_conj {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (x : unitaryGroup n ℂ)
    (h : B = (x : Matrix n n ℂ) * A * (x : Matrix n n ℂ)ᴴ) (f : ℝ → ℝ) :
    hB.cfc f = (x : Matrix n n ℂ) * hA.cfc f * (x : Matrix n n ℂ)ᴴ := by
  rw [← hB.cfc_eq, ← hA.cfc_eq, h]
  have hφ : Continuous (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) x) := by
    change Continuous fun a : Matrix n n ℂ ↦ (x : Matrix n n ℂ) * a * star (x : Matrix n n ℂ)
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have := StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) x) f A
    (A.finite_real_spectrum.continuousOn f) hφ hA.isSelfAdjoint
  simpa [Matrix.star_eq_conjTranspose] using this.symm

/-- The support inverse square root commutes with unitary conjugation. -/
theorem PosSemidef.supportInvSqrt_eq_of_eq_unitary_conj {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (x : unitaryGroup n ℂ)
    (h : B = (x : Matrix n n ℂ) * A * (x : Matrix n n ℂ)ᴴ) :
    hB.supportInvSqrt = (x : Matrix n n ℂ) * hA.supportInvSqrt * (x : Matrix n n ℂ)ᴴ :=
  hA.isHermitian.cfc_eq_of_eq_unitary_conj hB.isHermitian x h _

/-- A unitary satisfies $x^\dagger x=1$. -/
theorem conjTranspose_mul_unitary (x : unitaryGroup n ℂ) :
    (x : Matrix n n ℂ)ᴴ * (x : Matrix n n ℂ) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp x.2

end Matrix

namespace Matrix

/-- A unitary and its adjoint cancel between rectangular matrix factors. -/
theorem mul_unitary_adjoint_mul_cancel {ι κ n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] [StarRing R]
    (A : Matrix ι n R) (B : Matrix n κ R) (z : unitaryGroup n R) :
    (A * (z : Matrix n n R)ᴴ) * ((z : Matrix n n R) * B) = A * B := by
  have hz : (z : Matrix n n R)ᴴ * (z : Matrix n n R) = 1 := z.2.1
  calc
    _ = A * ((z : Matrix n n R)ᴴ * (z : Matrix n n R)) * B := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hz, Matrix.mul_one]

end Matrix
