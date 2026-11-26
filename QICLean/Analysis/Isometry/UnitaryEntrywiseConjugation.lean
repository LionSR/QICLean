/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import QICLean.Analysis.Isometry.UnitaryKronecker

/-!
# Scalar relations from entrywise conjugates of unitary matrices

This file proves the unitary-matrix algebra behind the gauge signs in
FBC25, equations `eq:defT` and `eq:intro_sigma` (arXiv:2502.20257, lines 1557--1567).
Its self-relation theorem also gives the sign step in the conjugation-symmetry
proposition of arXiv:1703.09188, `paper_v2.tex` lines 1036--1038. The operation on the
second matrix is entrywise complex conjugation `Matrix.map (starRingEnd ℂ)`, not
conjugate transpose.

These results are conditional on the scalar-matrix relations, which are hypotheses here.

The second part shows that a Kronecker identity `conj(x) x ⊗ conj(y) y = 𝟙` between two
unitaries forces one common transpose sign on `x` and `y`.

## Main results

- `Matrix.scalar_mul_star_eq_one_of_mul_map_star_eq_smul_one`: the scalar multiplying the
  identity in a product of unitaries has unit modulus.
- `Matrix.paired_scalars_mul_eq_one_of_mul_map_star_eq_smul_one`: scalars from the two
  oppositely ordered relations are reciprocal.
- `Matrix.scalar_eq_one_or_neg_one_of_mul_map_star_self_eq_smul_one`: the scalar in the
  self relation is a sign.
- `Matrix.exists_common_transpose_sign_of_kronecker_map_star_mul_eq_one`: the
  Kronecker identity produces one sign `σ = ±1` with `x = σ • xᵀ` and
  `y = σ • yᵀ`.
- `Matrix.transpose_eq_self_or_transpose_eq_neg_of_kronecker_map_star_mul_eq_one`:
  the same conclusion in the form "both symmetric or both skew-symmetric".

## References

* [J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, *Matrix product
  unitaries: structure, symmetries, and topological invariants*,
  arXiv:1703.09188, lines 1033--1038][Cirac2017MPU]

Moved from TNLean, `TNLean/Algebra/UnitaryEntrywiseConjugation.lean` and
`TNLean/Algebra/UnitaryConjugationTransposeSign.lean` at commit `49b78ed821` (Apache-2.0),
merged into one file.

Moved from TNLean, `TNLean/MPS/MPU/StandardForm/ConjugationSymmetry.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- If the product of a unitary matrix and the entrywise conjugate of another unitary
matrix is scalar, then the scalar has unit modulus. This is the scalar phase step in
FBC25, equation `eq:intro_sigma` (arXiv:2502.20257, lines 1559--1562). -/
theorem scalar_mul_star_eq_one_of_mul_map_star_eq_smul_one
    (T S : Matrix.unitaryGroup n ℂ) (σ : ℂ)
    (hσ : (T : Matrix n n ℂ) * (S : Matrix n n ℂ).map (starRingEnd ℂ) = σ • 1) :
    σ * starRingEnd ℂ σ = 1 := by
  let i : n := Classical.choice inferInstance
  have hmem : (σ • 1 : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ := by
    rw [← hσ]
    exact (Matrix.unitaryGroup n ℂ).mul_mem T.property
      (Matrix.map_star_mem_unitaryGroup_iff.mpr S.property)
  have hunit := Matrix.mem_unitaryGroup_iff.mp hmem
  have hii := congrFun (congrFun hunit i) i
  simpa [Matrix.mul_apply, Matrix.one_apply] using hii

/-- For two unitary matrices, scalars in the two relations obtained by exchanging the
matrices and entrywise conjugating the second factor are reciprocal. This is the identity
`σ_g σ_{g⁻¹} = 1` following FBC25, equation `eq:intro_sigma`
(arXiv:2502.20257, lines 1559--1563). -/
theorem paired_scalars_mul_eq_one_of_mul_map_star_eq_smul_one
    (T S : Matrix.unitaryGroup n ℂ) (σ τ : ℂ)
    (hσ : (T : Matrix n n ℂ) * (S : Matrix n n ℂ).map (starRingEnd ℂ) = σ • 1)
    (hτ : (S : Matrix n n ℂ) * (T : Matrix n n ℂ).map (starRingEnd ℂ) = τ • 1) :
    σ * τ = 1 := by
  let Sstar := Matrix.UnitaryGroup.map_star S
  have hcomm : (Sstar : Matrix n n ℂ) * (T : Matrix n n ℂ) = σ • 1 := by
    calc
      (Sstar : Matrix n n ℂ) * (T : Matrix n n ℂ) =
          ((((T⁻¹ : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) * T) * Sstar) * T := by simp
      _ = ((T⁻¹ : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) * (T * Sstar) * T := by
        simp only [mul_assoc]
      _ = ((T⁻¹ : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) * (σ • 1) * T := by
        rw [show (T : Matrix n n ℂ) * Sstar = σ • 1 by simpa [Sstar] using hσ]
      _ = σ • 1 := by simp
  have hτstar : (Sstar : Matrix n n ℂ) * (T : Matrix n n ℂ) = starRingEnd ℂ τ • 1 := by
    have h := congrArg (fun M : Matrix n n ℂ ↦ M.map (starRingEnd ℂ)) hτ
    rw [Matrix.map_mul] at h
    ext i j
    have hij := congrFun (congrFun h i) j
    by_cases hij' : i = j <;>
      simpa [Sstar, Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply, Function.comp_apply, hij']
        using hij
  have hστ : σ = starRingEnd ℂ τ := by
    let i : n := Classical.choice inferInstance
    have h := congrFun (congrFun (hcomm.symm.trans hτstar) i) i
    simpa using h
  have hτunit := scalar_mul_star_eq_one_of_mul_map_star_eq_smul_one S T τ hτ
  rw [hστ, mul_comm]
  exact hτunit

/-- In the self relation, the scalar multiplying the identity is `1` or `-1`. This is the
step `𝟙 = xx† = e^{2iφ}𝟙`, hence `e^{iφ} = ±1`, in the conjugation-symmetry proposition of
arXiv:1703.09188, `paper_v2.tex` lines 1036--1038; it is used again as the involution
conclusion after FBC25, equation `eq:intro_sigma` (arXiv:2502.20257, lines 1563--1567). -/
theorem scalar_eq_one_or_neg_one_of_mul_map_star_self_eq_smul_one
    (T : Matrix.unitaryGroup n ℂ) (σ : ℂ)
    (hσ : (T : Matrix n n ℂ) * (T : Matrix n n ℂ).map (starRingEnd ℂ) = σ • 1) :
    σ = 1 ∨ σ = -1 := by
  apply sq_eq_one_iff.mp
  rw [pow_two]
  exact paired_scalars_mul_eq_one_of_mul_map_star_eq_smul_one T T σ σ hσ hσ

end Matrix

/-!
## A common transpose sign for two conjugation factors

Applying a conjugation relation `conj(u) = (x ⊗ y) u` twice leaves the
single Kronecker identity `conj(x) x ⊗ conj(y) y = 𝟙` between the two unitaries `x`
and `y`. This section isolates the purely algebraic consequence drawn from that
identity in arXiv:1703.09188, `paper_v2.tex` lines 1033--1038: the identity is
equivalent to `x = e^{iφ} xᵀ` and `y = e^{-iφ} yᵀ`, and unitarity of `x` forces
`e^{iφ} = ±1`. The two factors therefore carry one common transpose sign: either
both are symmetric, or both are skew-symmetric.

The conjugation appearing in the source relation is entrywise complex
conjugation, `Matrix.map (starRingEnd ℂ)`, not the conjugate transpose.
-/

open scoped Kronecker

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
  [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty m] in
/-- For a unitary matrix, the transpose is a left inverse of the entrywise
conjugate. It permits multiplying `conj(x)x = e^{iφ}𝟙` on the left by `xᵀ` in
arXiv:1703.09188, `paper_v2.tex` lines 1035--1036. -/
theorem transpose_mul_map_star_of_mem_unitaryGroup {x : Matrix m m ℂ}
    (hx : x ∈ unitaryGroup m ℂ) : xᵀ * x.map (starRingEnd ℂ) = 1 := by
  have hstar : xᴴ * x = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hx
  have h := congrArg Matrix.transpose hstar
  rw [Matrix.transpose_mul, Matrix.transpose_one] at h
  have hc : (xᴴ)ᵀ = x.map (starRingEnd ℂ) := by ext i j; simp
  rwa [hc] at h

omit [Nonempty m] in
/-- A unitary matrix whose entrywise conjugate times itself is a scalar matrix
equals that scalar times its own transpose. This is the passage from
`conj(x) x = e^{iφ}𝟙` to `x = e^{iφ} xᵀ` in arXiv:1703.09188, `paper_v2.tex`
lines 1035--1036. -/
theorem eq_smul_transpose_of_map_star_mul_eq_smul_one {x : Matrix m m ℂ}
    (hx : x ∈ unitaryGroup m ℂ) {c : ℂ} (hc : x.map (starRingEnd ℂ) * x = c • 1) :
    x = c • xᵀ := by
  calc x = xᵀ * x.map (starRingEnd ℂ) * x := by
        rw [transpose_mul_map_star_of_mem_unitaryGroup hx, Matrix.one_mul]
    _ = xᵀ * (x.map (starRingEnd ℂ) * x) := Matrix.mul_assoc _ _ _
    _ = xᵀ * (c • (1 : Matrix m m ℂ)) := by rw [hc]
    _ = c • xᵀ := by rw [Matrix.mul_smul, Matrix.mul_one]

/-- **Common transpose sign of the two conjugation factors.** If the entrywise
conjugation relations of two unitary matrices assemble into the Kronecker
identity `conj(x) x ⊗ conj(y) y = 𝟙`, then one sign `σ = ±1` satisfies `x = σ • xᵀ` and
`y = σ • yᵀ`.

This is the algebraic tail of the conjugation-symmetry proposition in
arXiv:1703.09188, `paper_v2.tex` lines 1033--1038: the Kronecker identity splits
into reciprocal scalars `e^{iφ}` and `e^{-iφ}`, and `𝟙 = xx† = e^{2iφ}𝟙` forces
`e^{iφ} = ±1`, so the two reciprocal scalars coincide. -/
theorem exists_common_transpose_sign_of_kronecker_map_star_mul_eq_one
    {x : Matrix m m ℂ} {y : Matrix n n ℂ} (hx : x ∈ unitaryGroup m ℂ)
    (hy : y ∈ unitaryGroup n ℂ)
    (h : (x.map (starRingEnd ℂ) * x) ⊗ₖ (y.map (starRingEnd ℂ) * y) = 1) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ x = σ • xᵀ ∧ y = σ • yᵀ := by
  obtain ⟨c, -, hcx, hcy⟩ := exists_eq_smul_one_of_kronecker_eq_one h
  have hxbar : x.map (starRingEnd ℂ) ∈ unitaryGroup m ℂ :=
    map_star_mem_unitaryGroup_iff.mpr hx
  have hdouble : (x.map (starRingEnd ℂ)).map (starRingEnd ℂ) = x := by ext i j; simp
  have hself : x.map (starRingEnd ℂ) * (x.map (starRingEnd ℂ)).map (starRingEnd ℂ) =
      c • 1 := by rw [hdouble]; exact hcx
  have hsign : c = 1 ∨ c = -1 :=
    scalar_eq_one_or_neg_one_of_mul_map_star_self_eq_smul_one
      (⟨x.map (starRingEnd ℂ), hxbar⟩ : unitaryGroup m ℂ) c hself
  have hcinv : c⁻¹ = c := by rcases hsign with hc | hc <;> rw [hc] <;> norm_num
  exact ⟨c, hsign, eq_smul_transpose_of_map_star_mul_eq_smul_one hx hcx,
    eq_smul_transpose_of_map_star_mul_eq_smul_one hy (by rwa [hcinv] at hcy)⟩

/-- **Both factors symmetric or both skew-symmetric.** The Kronecker identity
`conj(x) x ⊗ conj(y) y = 𝟙` between two unitary matrices leaves exactly two possibilities:
both matrices are symmetric, or both are skew-symmetric. This is the form of
arXiv:1703.09188, `paper_v2.tex` lines 1033--1038 used in the structural
discussion of symmetric and skew-symmetric unitaries that follows it. -/
theorem transpose_eq_self_or_transpose_eq_neg_of_kronecker_map_star_mul_eq_one
    {x : Matrix m m ℂ} {y : Matrix n n ℂ} (hx : x ∈ unitaryGroup m ℂ)
    (hy : y ∈ unitaryGroup n ℂ)
    (h : (x.map (starRingEnd ℂ) * x) ⊗ₖ (y.map (starRingEnd ℂ) * y) = 1) :
    (xᵀ = x ∧ yᵀ = y) ∨ (xᵀ = -x ∧ yᵀ = -y) := by
  obtain ⟨σ, hσ, hxσ, hyσ⟩ :=
    exists_common_transpose_sign_of_kronecker_map_star_mul_eq_one hx hy h
  have hxT : xᵀ = σ • x := by simpa using congrArg Matrix.transpose hxσ
  have hyT : yᵀ = σ • y := by simpa using congrArg Matrix.transpose hyσ
  rcases hσ with hσ | hσ
  · subst hσ
    exact Or.inl ⟨by simpa using hxT, by simpa using hyT⟩
  · subst hσ
    exact Or.inr ⟨by simpa using hxT, by simpa using hyT⟩

end Matrix

section

open scoped Matrix Kronecker BigOperators

namespace Matrix

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b]

/-- Entrywise conjugation preserves both unitary identities of a rectangular
gate, as used for the conjugate comparison in arXiv:1703.09188,
`prop1conj`, lines 1030–1033. -/
theorem IsUnitaryBetween.map_star {A : Matrix a b ℂ} (hA : A.IsUnitaryBetween) :
    (A.map (starRingEnd ℂ)).IsUnitaryBetween := by
  have hstar : (A.map (starRingEnd ℂ))ᴴ = Aᴴ.map (starRingEnd ℂ) :=
    (Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj])).symm
  constructor
  · change (A.map (starRingEnd ℂ))ᴴ * A.map (starRingEnd ℂ) = 1
    rw [hstar, ← Matrix.map_mul, hA.1]
    simp
  · change A.map (starRingEnd ℂ) * (A.map (starRingEnd ℂ))ᴴ = 1
    rw [hstar, ← Matrix.map_mul, hA.2]
    simp

/-- Applying the literal unshifted gate equation twice and cancelling the
coisometric gate gives the Kronecker identity of arXiv:1703.09188,
`paper_v2.tex` lines 1033–1035. This identity is derived, not assumed. -/
theorem kronecker_map_star_mul_eq_one_of_gate_conjugation
    {x : Matrix a a ℂ} {y : Matrix b b ℂ} {u : Matrix (a × b) c ℂ}
    (hu : u.IsCoisometry)
    (hconj : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u) :
    (x.map (starRingEnd ℂ) * x) ⊗ₖ (y.map (starRingEnd ℂ) * y) = 1 := by
  have hmap : (x ⊗ₖ y).map (starRingEnd ℂ) =
      x.map (starRingEnd ℂ) ⊗ₖ y.map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.kroneckerMap_apply]
  have hdouble := congrArg (fun M ↦ M.map (starRingEnd ℂ)) hconj
  have hinvolutive : (u.map (starRingEnd ℂ)).map (starRingEnd ℂ) = u := by
    ext i j
    simp
  rw [hinvolutive, Matrix.map_mul, hmap, hconj] at hdouble
  have hright : u * uᴴ = 1 := hu
  calc
    (x.map (starRingEnd ℂ) * x) ⊗ₖ (y.map (starRingEnd ℂ) * y) =
        (x.map (starRingEnd ℂ) ⊗ₖ y.map (starRingEnd ℂ)) * (x ⊗ₖ y) :=
      Matrix.mul_kronecker_mul _ _ _ _
    _ = ((x.map (starRingEnd ℂ) ⊗ₖ y.map (starRingEnd ℂ)) * (x ⊗ₖ y)) *
        (u * uᴴ) := by rw [hright, Matrix.mul_one]
    _ = ((x.map (starRingEnd ℂ) ⊗ₖ y.map (starRingEnd ℂ)) *
        ((x ⊗ₖ y) * u)) * uᴴ := by simp only [Matrix.mul_assoc]
    _ = u * uᴴ := by rw [← hdouble]
    _ = 1 := hright

/-- The local equation for a coisometric gate already forces the two unitary
factors to be both symmetric or both skew-symmetric, as in arXiv:1703.09188,
`paper_v2.tex` lines 1033–1038. -/
theorem transpose_eq_self_or_transpose_eq_neg_of_gate_conjugation
    [Nonempty a] [Nonempty b]
    {x : Matrix a a ℂ} {y : Matrix b b ℂ} {u : Matrix (a × b) c ℂ}
    (hx : x ∈ unitaryGroup a ℂ) (hy : y ∈ unitaryGroup b ℂ)
    (hu : u.IsCoisometry)
    (hconj : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u) :
    (xᵀ = x ∧ yᵀ = y) ∨ (xᵀ = -x ∧ yᵀ = -y) :=
  transpose_eq_self_or_transpose_eq_neg_of_kronecker_map_star_mul_eq_one hx hy
    (kronecker_map_star_mul_eq_one_of_gate_conjugation hu hconj)

end Matrix

end
