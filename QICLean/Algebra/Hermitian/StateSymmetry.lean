/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Strong and weak symmetries of a matrix

A matrix `O` is a *strong symmetry* of a matrix `ρ` when `O ρ = c ρ` for a scalar `c`, and a
*weak symmetry* when `O` commutes with `ρ` (`Commute O ρ`). For density operators these are the
two notions of symmetry of mixed states: Sun, arXiv:2504.16985, line 182, for families of matrix product
operators, and de Groot, Turzillo and Schuch, arXiv:2112.04483, for on-site unitaries
(`U ρ = ρ` and `[U, ρ] = 0`).

## Main definitions

* `Matrix.IsStrongSymmetry`: `O ρ = c ρ`; weak symmetry is `Commute O ρ`.

## Main results

* `Matrix.IsStrongSymmetry.commute_of_conjTranspose`: a strong symmetry whose adjoint is
  also a strong symmetry of a Hermitian `ρ` is a weak symmetry, the adjoint-closure proviso of
  the source.
* `Matrix.IsStrongSymmetry.conjTranspose_of_unitary`,
  `Matrix.IsStrongSymmetry.commute_of_unitary`: the unitary case.
* `Matrix.IsStrongSymmetry.norm_eq_one`: a unitary strong symmetry of a nonzero matrix has a
  unimodular eigenvalue.

## References

- [arXiv:2504.16985](https://arxiv.org/abs/2504.16985) -- X.-Q. Sun, *Anomalous matrix
  product operator symmetries and 1D mixed-state phases*
- [arXiv:2112.04483](https://arxiv.org/abs/2112.04483) -- C. de Groot, A. Turzillo,
  N. Schuch, *Symmetry protected topological order in open quantum systems*

Moved from TNLean, `TNLean/MPS/Operator/Fusion/DensityOperatorSymmetry.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

section

open scoped Matrix ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n]

/-- **Strong symmetry at one system size.**

Source: arXiv:2504.16985, line 182: `O ρ = λ ρ` for some scalar `λ`. The scalar is not
required to be a phase; `λ = 0` is allowed. -/
def IsStrongSymmetry (O ρ : Matrix n n ℂ) : Prop :=
  ∃ c : ℂ, O * ρ = c • ρ

/-- A Hermitian matrix whose square vanishes is zero. -/
private theorem IsHermitian.mul_self_ne_zero {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (h0 : ρ ≠ 0) : ρ * ρ ≠ 0 := by
  intro h
  apply h0
  refine self_mul_conjTranspose_eq_zero.mp ?_
  rwa [hρ.eq]

/-- **Strong symmetry implies weak symmetry under adjoint closure.**

Source: arXiv:2504.16985, line 182: strong symmetry is a special case of weak symmetry
provided the conjugate operator `O^†` is also a strong symmetry. For Hermitian `ρ`, the two
eigenvalue equations give `ρ O = \bar μ ρ` and `ρ O ρ = λ ρ² = \bar μ ρ²`, so `λ = \bar μ`
unless `ρ = 0`. -/
theorem IsStrongSymmetry.commute_of_conjTranspose {O ρ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hO : IsStrongSymmetry O ρ) (hOH : IsStrongSymmetry Oᴴ ρ) :
    Commute O ρ := by
  obtain ⟨c, hc⟩ := hO
  obtain ⟨μ, hμ⟩ := hOH
  have hρO : ρ * O = star μ • ρ := by
    have h := congrArg conjTranspose hμ
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, hρ.eq, conjTranspose_smul, hρ.eq] at h
  by_cases h0 : ρ = 0
  · subst h0
    exact Commute.zero_right O
  have hcμ : c = star μ := by
    have h1 : ρ * (O * ρ) = (ρ * O) * ρ := (Matrix.mul_assoc _ _ _).symm
    rw [hc, hρO, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact smul_left_injective ℂ (IsHermitian.mul_self_ne_zero hρ h0) h1
  change O * ρ = ρ * O
  rw [hc, hρO, hcμ]

/-- A strong symmetry `O` with `O^† O = 1` has its adjoint as a strong symmetry: from
`O ρ = c ρ`, `ρ = O^† O ρ = c O^† ρ`. -/
theorem IsStrongSymmetry.conjTranspose_of_unitary [DecidableEq n] {O ρ : Matrix n n ℂ}
    (hU : Oᴴ * O = 1) (hO : IsStrongSymmetry O ρ) : IsStrongSymmetry Oᴴ ρ := by
  obtain ⟨c, hc⟩ := hO
  have h : ρ = c • (Oᴴ * ρ) := by
    rw [← Matrix.mul_smul, ← hc, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  by_cases hc0 : c = 0
  · refine ⟨0, ?_⟩
    rw [hc0, zero_smul] at h
    rw [h, Matrix.mul_zero, smul_zero]
  · refine ⟨c⁻¹, ?_⟩
    conv_rhs => rw [h, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- **Strong implies weak for unitary operators.**

Source: arXiv:2504.16985, line 182, in the unitary case, where the adjoint `O^† = O^{-1}` is a
strong symmetry automatically (`IsStrongSymmetry.conjTranspose_of_unitary`). -/
theorem IsStrongSymmetry.commute_of_unitary [DecidableEq n] {O ρ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hU : Oᴴ * O = 1) (hO : IsStrongSymmetry O ρ) :
    Commute O ρ :=
  hO.commute_of_conjTranspose hρ (hO.conjTranspose_of_unitary hU)

/-- **Unit modulus of a unitary strong eigenvalue.**

Bridge: for `O^† O = 1` and `ρ ≠ 0`, `O ρ = c ρ` forces `|c| = 1`, since
`ρ^† ρ = (O ρ)^† (O ρ) = |c|² ρ^† ρ` and `ρ^† ρ ≠ 0`. This is the modulus of the phase `e^{iθ}`
in the channel-level strong symmetry of arXiv:2112.04483, line 351; the eigenvalue itself
is not determined. -/
theorem IsStrongSymmetry.norm_eq_one [DecidableEq n] {O ρ : Matrix n n ℂ} {c : ℂ}
    (hU : Oᴴ * O = 1) (hc : O * ρ = c • ρ) (h0 : ρ ≠ 0) : ‖c‖ = 1 := by
  have h1 : ρᴴ * ρ = (star c * c) • (ρᴴ * ρ) := by
    calc ρᴴ * ρ = (O * ρ)ᴴ * (O * ρ) := by
          rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Oᴴ, hU, Matrix.one_mul]
      _ = (star c * c) • (ρᴴ * ρ) := by
          rw [hc, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hne : ρᴴ * ρ ≠ 0 := fun h => h0 (conjTranspose_mul_self_eq_zero.mp h)
  have h3 : star c * c = 1 := smul_left_injective ℂ hne (h1.symm.trans (one_smul ℂ _).symm)
  have h4 : (‖c‖ : ℂ) ^ 2 = 1 := by
    rw [← h3, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have h5 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h4
  nlinarith [norm_nonneg c]

end Matrix

end
