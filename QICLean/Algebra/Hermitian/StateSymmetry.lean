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

/-!
# Strong and weak symmetries of matrix product density operators

**Source.** Sun 2025 (arXiv:2504.16985), "Anomalous matrix product operator symmetries and
1D mixed-state phases", `References/2504.16985/main.tex` line 182: a matrix product density
operator `ρ^{(L)}(X,M)` is strongly symmetric under a family of matrix product operators
`O_a^{(L)}` when
`O_a^{(L)} ρ^{(L)} = λ_a^{(L)} ρ^{(L)}` for all `a` and `L`, and weakly symmetric when
`[O_a^{(L)}, ρ^{(L)}] = 0` for all `a` and `L`; strong symmetry is a special case of weak
symmetry provided each `O_a^{(L)}` has its adjoint `O_{ā}^{(L)}` in the family. The on-site
group case, `[U, ρ] = 0` (weak) and `U ρ = ρ` (strong), is recalled in Garre Rubio, Molnár,
Schuch, Verstraete 2026 (arXiv:2603.28349), `References/2603.28349/main.tex` line 362, from
de Groot, Turzillo, Schuch 2022 (arXiv:2112.04483).

**Formalized here.** The two predicates at one system size and along the whole family of
periodic operators; the implication from strong to weak symmetry under the source's
adjoint-closure proviso; the unit modulus of the eigenvalue of a unitary strong symmetry; the
fusion rules satisfied by strong eigenvalues; and the on-site specialization `U_g^{⊗L}`, where
the eigenvalues form a character of the group at each length.

The family predicates permit an arbitrary virtual boundary. The source's
commuting boundaries are the elements of `commutingBoundaryAlgebra M`;
positivity of the resulting operators is `IsMPDOWithBoundary M X`.
Neither commutation nor positivity is required for the symmetry equations
themselves. Density-operator conclusions state positivity where it is used.

## Main definitions

* `Matrix.IsStrongSymmetry`, `Matrix.IsWeakSymmetry`: `O ρ = c ρ` and `[O, ρ] = 0`.
* `MPOTensor.IsStrongMPOSymmetry`, `MPOTensor.IsWeakMPOSymmetry`: the same at every positive
  length along a family of periodic matrix product operators, with length-dependent
  eigenvalues `c a L`.
* `MPOTensor.onSite`: the bond-dimension-one tensor of an on-site operator.
* `MPOTensor.IsStrongOnSiteSymmetry`, `MPOTensor.IsWeakOnSiteSymmetry`: the on-site group case.

## Main results

* `Matrix.IsStrongSymmetry.isWeakSymmetry_of_conjTranspose`,
  `MPOTensor.IsStrongMPOSymmetry.isWeakMPOSymmetry`: strong implies weak under adjoint closure.
* `Matrix.IsStrongSymmetry.norm_eq_one`: a unitary strong symmetry of a nonzero matrix has a
  unimodular eigenvalue.
* `MPOTensor.IsStrongMPOSymmetry.mul_eq_sum`: strong eigenvalues obey the fusion rules.
* `MPOTensor.mpo_onSite`: the periodic operator of `onSite u` is `u^{⊗L}`.
* `MPOTensor.IsStrongOnSiteSymmetry.isWeakOnSiteSymmetry`,
  `MPOTensor.IsStrongOnSiteSymmetry.map_mul`, `MPOTensor.IsStrongOnSiteSymmetry.map_one`.

## References
- [arXiv:2504.16985](https://arxiv.org/abs/2504.16985) -- X.-Q. Sun, *Anomalous matrix
  product operator symmetries and 1D mixed-state phases*
- [arXiv:2112.04483](https://arxiv.org/abs/2112.04483) -- C. de Groot, A. Turzillo,
  N. Schuch, *Symmetry protected topological order in open quantum systems*
- [arXiv:2603.28349](https://arxiv.org/abs/2603.28349) -- J. Garre Rubio, A. Molnár,
  N. Schuch, F. Verstraete, *The local characterization of global tensor network eigenstates*

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

/-- **Weak symmetry at one system size.**

Source: arXiv:2504.16985, line 182: `[O, ρ] = 0`. -/
def IsWeakSymmetry (O ρ : Matrix n n ℂ) : Prop :=
  Commute O ρ

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
theorem IsStrongSymmetry.isWeakSymmetry_of_conjTranspose {O ρ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hO : IsStrongSymmetry O ρ) (hOH : IsStrongSymmetry Oᴴ ρ) :
    IsWeakSymmetry O ρ := by
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
theorem IsStrongSymmetry.isWeakSymmetry_of_unitary [DecidableEq n] {O ρ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hU : Oᴴ * O = 1) (hO : IsStrongSymmetry O ρ) :
    IsWeakSymmetry O ρ :=
  hO.isWeakSymmetry_of_conjTranspose hρ (hO.conjTranspose_of_unitary hU)

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
