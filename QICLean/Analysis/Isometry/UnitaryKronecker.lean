/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import QICLean.Analysis.Real.ComplexSqrt
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Module

/-!
# Unitary factors of a Kronecker product

This file proves that a unitary Kronecker product over the complex numbers has
unitary factors after reciprocal rescaling by one positive real number.  The
algebraic core is an entrywise characterization of two matrices whose
Kronecker product is the identity. It also proves that unitarity of `K† ⊗ K` implies
unitarity of `K`, and compares two factorizations of one matrix whose comparison matrices
have a unitary Kronecker product.

## Main results

- `Matrix.exists_eq_smul_one_of_kronecker_eq_one`: the two factors of a
  Kronecker product equal to the identity are reciprocal scalar matrices.
- `Matrix.exists_pos_real_rescaling_mem_unitaryGroup_of_kronecker_mem_unitaryGroup`:
  the factors of a unitary Kronecker product become unitary after reciprocal
  positive rescaling.
- `Matrix.exists_pos_real_smul_unitary_factors_of_kronecker_mem_unitaryGroup`:
  the equivalent factorization into a positive scalar and unitary matrices.
- `Matrix.isUnitaryBetween_of_conjTranspose_kronecker`: unitarity of `K† ⊗ K` implies
  unitarity of `K`.
- `Matrix.factorization_comparison_of_one_sided_inverses`: compares two equal
  rectangular matrix factorizations using chosen one-sided inverses.
- `Matrix.exists_reciprocal_unitary_gauges_of_comparison`: converts two
  comparison matrices with unitary Kronecker product into reciprocal unitary
  gauges.

Moved from TNLean, `TNLean/Algebra/UnitaryKronecker.lean`,
`TNLean/Algebra/UnitaryAdjointKronecker.lean` and `TNLean/Algebra/UnitaryKroneckerComparison.lean`
at commit `49b78ed821` (Apache-2.0), merged into one file.

Moved from TNLean, `TNLean/MPS/MPU/Circuit/Merging/TwoSectorMerging.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

open scoped ComplexOrder Kronecker

namespace Matrix

namespace IsUnitaryBetween

/-- The Kronecker product of two matrices unitary between finite coordinate
spaces is again unitary between the product coordinate spaces. -/
theorem kronecker {m n o p : Type*}
    [Fintype m] [Fintype n] [Fintype o] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq o] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix o p ℂ)
    (hA : A.IsUnitaryBetween) (hB : B.IsUnitaryBetween) :
    (A ⊗ₖ B).IsUnitaryBetween := by
  refine ⟨hA.1.kronecker _ _ hB.1, ?_⟩
  have h := (hA.conjTranspose A).1.kronecker _ _ (hB.conjTranspose B).1
  simpa only [← Matrix.conjTranspose_kronecker,
    Matrix.IsIsometry, Matrix.IsCoisometry, Matrix.conjTranspose_conjTranspose] using h

end IsUnitaryBetween

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n]

/-- If a Kronecker product of two complex square matrices is the identity, then
its factors are reciprocal nonzero scalar matrices. -/
theorem exists_eq_smul_one_of_kronecker_eq_one
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (h : A ⊗ₖ B = 1) :
    ∃ c : ℂ, c ≠ 0 ∧ A = c • 1 ∧ B = c⁻¹ • 1 := by
  classical
  let i₀ : m := Classical.choice inferInstance
  let j₀ : n := Classical.choice inferInstance
  have hdiag : A i₀ i₀ * B j₀ j₀ = 1 := by
    have := congrFun (congrFun h (i₀, j₀)) (i₀, j₀)
    simpa [kroneckerMap_apply] using this
  have hc : A i₀ i₀ ≠ 0 := fun hc ↦ by simp [hc] at hdiag
  refine ⟨A i₀ i₀, hc, ?_, ?_⟩
  · ext i i'
    have hij := congrFun (congrFun h (i, j₀)) (i', j₀)
    simp only [kroneckerMap_apply, one_apply, Prod.mk.injEq] at hij
    rw [show B j₀ j₀ = (A i₀ i₀)⁻¹ by
      exact eq_inv_of_mul_eq_one_right hdiag] at hij
    simp only [smul_apply, one_apply]
    split_ifs with hii
    · subst i'
      simp only [true_and, ↓reduceIte] at hij
      simpa [hc] using eq_inv_of_mul_eq_one_left hij
    · have : A i i' = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_right (inv_ne_zero hc)
        simpa [hii] using hij
      simp [this]
  · ext j j'
    have hij := congrFun (congrFun h (i₀, j)) (i₀, j')
    simp only [kroneckerMap_apply, one_apply, Prod.mk.injEq] at hij
    simp only [smul_apply, one_apply]
    split_ifs with hjj
    · subst j'
      simp only [true_and, ↓reduceIte] at hij
      simpa [smul_eq_mul] using eq_inv_of_mul_eq_one_right hij
    · have : B j j' = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left hc
        simpa [hjj] using hij
      simp [this]

variable [Fintype m] [Fintype n]

/-- If a Kronecker product is unitary, reciprocal positive rescalings of its
factors are unitary.  This is the factor-by-factor step in FBC25, Lemma
`lem:deco` (arXiv:2502.20257, lines 1052--1066). -/
theorem exists_pos_real_rescaling_mem_unitaryGroup_of_kronecker_mem_unitaryGroup
    {K₁ : Matrix m m ℂ} {K₂ : Matrix n n ℂ}
    (hK : K₁ ⊗ₖ K₂ ∈ Matrix.unitaryGroup (m × n) ℂ) :
    ∃ δ : ℝ, 0 < δ ∧
      ((δ : ℂ)⁻¹ • K₁) ∈ Matrix.unitaryGroup m ℂ ∧
      ((δ : ℂ) • K₂) ∈ Matrix.unitaryGroup n ℂ := by
  classical
  have hgram : (K₁ᴴ * K₁) ⊗ₖ (K₂ᴴ * K₂) = 1 := by
    rw [mul_kronecker_mul, ← conjTranspose_kronecker]
    exact mem_unitaryGroup_iff'.mp hK
  obtain ⟨c, hc, hK₁, hK₂⟩ := exists_eq_smul_one_of_kronecker_eq_one hgram
  have hc_nonneg : 0 ≤ c := by
    let i₀ : m := Classical.choice inferInstance
    have hpos := (posSemidef_conjTranspose_mul_self K₁).diag_nonneg (i := i₀)
    rw [hK₁] at hpos
    simpa using hpos
  let r : ℝ := c.re
  have hc_eq : c = (r : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [r] using (Complex.nonneg_iff.mp hc_nonneg).2.symm
  have hr_nonneg : 0 ≤ r := (Complex.nonneg_iff.mp hc_nonneg).1
  have hr_ne : r ≠ 0 := by
    intro hr
    apply hc
    rw [hc_eq, hr]
    exact Complex.ofReal_zero
  have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_ne)
  let δ := Real.sqrt r
  have hδ_pos : 0 < δ := Real.sqrt_pos.2 hr_pos
  have hδ_ne : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ_pos.ne'
  have hδ_sq : (δ : ℂ) ^ 2 = (r : ℂ) := Complex.ofReal_sqrt_sq r hr_nonneg
  refine ⟨δ, hδ_pos, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff']
    rw [show star ((δ : ℂ)⁻¹ • K₁) = (δ : ℂ)⁻¹ • K₁ᴴ by
      simp [star_eq_conjTranspose]]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hK₁, hc_eq]
    simp only [smul_smul]
    rw [← hδ_sq]
    field_simp
    simp
  · rw [mem_unitaryGroup_iff']
    rw [show star ((δ : ℂ) • K₂) = (δ : ℂ) • K₂ᴴ by
      simp [star_eq_conjTranspose]]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hK₂, hc_eq]
    simp only [smul_smul]
    rw [← hδ_sq]
    field_simp
    simp

/-- Equivalently, the factors of a unitary Kronecker product are a positive
real scalar and its reciprocal times unitary matrices.  This packages the
rescaled matrices from
`Matrix.exists_pos_real_rescaling_mem_unitaryGroup_of_kronecker_mem_unitaryGroup`
as elements of the matrix unitary groups. -/
theorem exists_pos_real_smul_unitary_factors_of_kronecker_mem_unitaryGroup
    {K₁ : Matrix m m ℂ} {K₂ : Matrix n n ℂ}
    (hK : K₁ ⊗ₖ K₂ ∈ Matrix.unitaryGroup (m × n) ℂ) :
    ∃ (δ : ℝ) (_ : 0 < δ) (W₁ : Matrix.unitaryGroup m ℂ)
      (W₂ : Matrix.unitaryGroup n ℂ),
      K₁ = (δ : ℂ) • (W₁ : Matrix m m ℂ) ∧
      K₂ = (δ : ℂ)⁻¹ • (W₂ : Matrix n n ℂ) := by
  obtain ⟨δ, hδ, hK₁, hK₂⟩ :=
    exists_pos_real_rescaling_mem_unitaryGroup_of_kronecker_mem_unitaryGroup hK
  let W₁ : Matrix.unitaryGroup m ℂ := ⟨(δ : ℂ)⁻¹ • K₁, hK₁⟩
  let W₂ : Matrix.unitaryGroup n ℂ := ⟨(δ : ℂ) • K₂, hK₂⟩
  have hδ_ne : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  refine ⟨δ, hδ, W₁, W₂, ?_, ?_⟩
  · change K₁ = (δ : ℂ) • ((δ : ℂ)⁻¹ • K₁)
    rw [smul_smul, mul_inv_cancel₀ hδ_ne, one_smul]
  · change K₂ = (δ : ℂ)⁻¹ • ((δ : ℂ) • K₂)
    rw [smul_smul, inv_mul_cancel₀ hδ_ne, one_smul]

end Matrix

/-!
## Unitarity from an adjoint Kronecker product

For a complex matrix between two nonempty finite coordinate spaces, unitarity
of $K^\dagger \otimes K$ implies unitarity of $K$. No equality of the two
coordinate-space cardinalities is assumed.

This is the general matrix implication used in arXiv:2502.20257,
lines 5444--5487, after the identity
$u=\sigma(K^\dagger\otimes K)v^\dagger$, which is not asserted here.
-/

open scoped Kronecker ComplexOrder

namespace Matrix

/-- A complex matrix is unitary between its coordinate spaces if its adjoint
Kronecker product is unitary. The reciprocal scalar Gram matrices have scalar
square one; Gram positivity excludes the negative root.

Source use: arXiv:2502.20257, lines 5444--5487. This implication applies to
rectangular matrices without an equal-cardinality hypothesis. -/
theorem isUnitaryBetween_of_conjTranspose_kronecker
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Nonempty m] [Nonempty n] {K : Matrix m n ℂ}
    (hK : (Kᴴ ⊗ₖ K).IsUnitaryBetween) : K.IsUnitaryBetween := by
  have hgram : (K * Kᴴ) ⊗ₖ (Kᴴ * K) = 1 := by
    simpa only [IsIsometry, conjTranspose_kronecker,
      conjTranspose_conjTranspose, ← mul_kronecker_mul] using hK.1
  obtain ⟨c, hc, hA, hB⟩ := exists_eq_smul_one_of_kronecker_eq_one hgram
  have hsquare : (K * Kᴴ) * (K * Kᴴ) = 1 := by
    calc
      _ = K * (Kᴴ * K) * Kᴴ := by simp only [Matrix.mul_assoc]
      _ = c⁻¹ • (K * Kᴴ) := by
        rw [hB, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = 1 := by rw [hA, smul_smul, inv_mul_cancel₀ hc, one_smul]
  let i : m := Classical.choice inferInstance
  have hcc : c * c = 1 := by
    have h := congrArg (fun M : Matrix m m ℂ ↦ M i i) hsquare
    simpa [hA, Matrix.smul_mul, Matrix.mul_smul, smul_smul] using h
  have hnonneg : 0 ≤ c := by
    have h := (posSemidef_self_mul_conjTranspose K).diag_nonneg (i := i)
    simpa [hA] using h
  have hc_one : c = 1 := by
    rcases mul_self_eq_one_iff.mp hcc with h | h
    · exact h
    · have hreal := (Complex.nonneg_iff.mp hnonneg).1
      norm_num [h] at hreal
  constructor
  · simpa only [IsIsometry, hc_one, inv_one, one_smul] using hB
  · simpa only [IsCoisometry, hc_one, one_smul] using hA

end Matrix

/-!
## Comparison of matrix factorizations with unitary Kronecker gauges

The matrix-algebraic core of the uniqueness argument for
the three-legged decompositions of arXiv:2502.20257, Lemma `lem:deco`.  A chosen left inverse
and right inverse identify the comparison matrix between two factorizations.
When two such comparison matrices have unitary Kronecker product, their
reciprocal positive rescalings give the unitary gauges in the orientation of
the original decompositions.
-/

open scoped Kronecker

namespace Matrix

/-- Suppose `X * Y` and `Xt * Yt` are the same matrix, `Lt` is a left inverse
of `Xt`, and `R` is a right inverse of `Y`.  Then `Lt * X` is the comparison
matrix between the two factorizations.

This is the one-sided-inverse step in FBC25, Lemma `lem:deco`
(arXiv:2502.20257, lines 1052--1066). -/
theorem factorization_comparison_of_one_sided_inverses
    {α β βt γ 𝕜 : Type*} [Fintype α] [Fintype β] [Fintype βt] [Fintype γ]
    [DecidableEq β] [DecidableEq βt] [Semiring 𝕜]
    {X : Matrix α β 𝕜} {Xt : Matrix α βt 𝕜}
    {Y : Matrix β γ 𝕜} {Yt : Matrix βt γ 𝕜}
    {Lt : Matrix βt α 𝕜} {R : Matrix γ β 𝕜}
    (hfac : X * Y = Xt * Yt) (hleft : Lt * Xt = 1) (hright : Y * R = 1) :
    Lt * X = Yt * R ∧ X = Xt * (Lt * X) ∧ Yt = (Lt * X) * Y := by
  have hK : Lt * X = Yt * R := by
    calc
      Lt * X = (Lt * X) * (Y * R) := by rw [hright, Matrix.mul_one]
      _ = Lt * (X * Y) * R := by simp only [Matrix.mul_assoc]
      _ = Lt * (Xt * Yt) * R := by rw [hfac]
      _ = (Lt * Xt) * Yt * R := by simp only [Matrix.mul_assoc]
      _ = Yt * R := by rw [hleft, Matrix.one_mul]
  refine ⟨hK, ?_, ?_⟩
  · calc
      X = X * (Y * R) := by rw [hright, Matrix.mul_one]
      _ = (X * Y) * R := by simp only [Matrix.mul_assoc]
      _ = (Xt * Yt) * R := by rw [hfac]
      _ = Xt * (Yt * R) := by simp only [Matrix.mul_assoc]
      _ = Xt * (Lt * X) := by rw [hK]
  · calc
      Yt = (Lt * Xt) * Yt := by rw [hleft, Matrix.one_mul]
      _ = Lt * (Xt * Yt) := by simp only [Matrix.mul_assoc]
      _ = Lt * (X * Y) := by rw [hfac]
      _ = (Lt * X) * Y := by simp only [Matrix.mul_assoc]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Nonempty m] [Nonempty n]

/-- Two comparison matrices whose Kronecker product `K₁ ⊗ₖ K₂` is unitary
determine unitary gauges with reciprocal positive scalars.  If the returned
scalar is `δ`, the source-oriented scalars are `δ⁻¹` for the first factor and
`δ` for the second, so their product is one.

The unitary matrices in the conclusion are the inverses, equivalently the
adjoints, of the unitary factors of the comparison matrices.  This is the
reciprocal-unitary-gauge step in FBC25, Lemma `lem:deco`
(arXiv:2502.20257, lines 1052--1066). -/
theorem exists_reciprocal_unitary_gauges_of_comparison
    {α₁ β₁ α₂ β₂ : Type*}
    {X₁ Xt₁ : Matrix α₁ m ℂ} {Y₁ Yt₁ : Matrix m β₁ ℂ}
    {X₂ Xt₂ : Matrix α₂ n ℂ} {Y₂ Yt₂ : Matrix n β₂ ℂ}
    {K₁ : Matrix m m ℂ} {K₂ : Matrix n n ℂ}
    (hK : K₁ ⊗ₖ K₂ ∈ Matrix.unitaryGroup (m × n) ℂ)
    (hX₁ : X₁ = Xt₁ * K₁) (hY₁ : Yt₁ = K₁ * Y₁)
    (hX₂ : X₂ = Xt₂ * K₂) (hY₂ : Yt₂ = K₂ * Y₂) :
    ∃ (δ : ℝ) (_ : 0 < δ) (W₁ : Matrix.unitaryGroup m ℂ)
      (W₂ : Matrix.unitaryGroup n ℂ),
      Xt₁ = (δ : ℂ)⁻¹ • (X₁ * (W₁ : Matrix m m ℂ)) ∧
      Yt₁ = (δ : ℂ) • (star (W₁ : Matrix m m ℂ) * Y₁) ∧
      Xt₂ = (δ : ℂ) • (X₂ * (W₂ : Matrix n n ℂ)) ∧
      Yt₂ = (δ : ℂ)⁻¹ • (star (W₂ : Matrix n n ℂ) * Y₂) ∧
      (δ : ℂ)⁻¹ * (δ : ℂ) = 1 := by
  classical
  obtain ⟨δ, hδ, U₁, U₂, hK₁, hK₂⟩ :=
    exists_pos_real_smul_unitary_factors_of_kronecker_mem_unitaryGroup hK
  have hδℂ : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  let W₁ : Matrix.unitaryGroup m ℂ := U₁⁻¹
  let W₂ : Matrix.unitaryGroup n ℂ := U₂⁻¹
  have hU₁W₁ : (U₁ : Matrix m m ℂ) * (W₁ : Matrix m m ℂ) = 1 := by
    change (U₁ : Matrix m m ℂ) * star (U₁ : Matrix m m ℂ) = 1
    exact U₁.2.2
  have hU₂W₂ : (U₂ : Matrix n n ℂ) * (W₂ : Matrix n n ℂ) = 1 := by
    change (U₂ : Matrix n n ℂ) * star (U₂ : Matrix n n ℂ) = 1
    exact U₂.2.2
  have hstarW₁ : star (W₁ : Matrix m m ℂ) = (U₁ : Matrix m m ℂ) := by
    simp [W₁]
  have hstarW₂ : star (W₂ : Matrix n n ℂ) = (U₂ : Matrix n n ℂ) := by
    simp [W₂]
  refine ⟨δ, hδ, W₁, W₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hX₁, hK₁, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hU₁W₁,
      Matrix.mul_one]
    ext i j
    simp [smul_apply, hδℂ]
  · rw [hY₁, hK₁, Matrix.smul_mul, hstarW₁]
  · rw [hX₂, hK₂, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hU₂W₂,
      Matrix.mul_one]
    ext i j
    simp [smul_apply, hδℂ]
  · rw [hY₂, hK₂, Matrix.smul_mul, hstarW₂]
  · exact inv_mul_cancel₀ hδℂ

end Matrix

section

open scoped Matrix Kronecker

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The block operator that records the complementary sectors `P` and `1 - P`
in a flag. Source: the sector encoder in Section 3 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def twoSectorEncoder (P : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks P (1 - P) (1 - P) P

/-- The sector encoder is an involution whenever its sector matrix is idempotent. -/
theorem twoSectorEncoder_mul_self (P : Matrix n n ℂ) (hP : IsIdempotentElem P) :
    twoSectorEncoder P * twoSectorEncoder P = 1 := by
  unfold twoSectorEncoder
  rw [fromBlocks_multiply]
  simp [hP.eq, hP.one_sub.eq, hP.mul_one_sub_self, hP.one_sub_mul_self]

omit [Fintype n] in
/-- Self-adjoint sector matrices give self-adjoint encoders. -/
theorem twoSectorEncoder_conjTranspose (P : Matrix n n ℂ) (hP : IsSelfAdjoint P) :
    (twoSectorEncoder P)ᴴ = twoSectorEncoder P := by
  simpa only [twoSectorEncoder, fromBlocks_conjTranspose, conjTranspose_sub,
    conjTranspose_one, star_eq_conjTranspose] using
    congrArg (fun Q : Matrix n n ℂ => fromBlocks Q (1 - Q) (1 - Q) Q) hP.star_eq

/-- Recording the sectors of an orthogonal projection is unitary. -/
theorem twoSectorEncoder_mem_unitaryGroup (P : Matrix n n ℂ) (hP : IsStarProjection P) :
    twoSectorEncoder P ∈ unitaryGroup (n ⊕ n) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose,
    twoSectorEncoder_conjTranspose P hP.isSelfAdjoint,
    twoSectorEncoder_mul_self P hP.isIdempotentElem]

/-- The projection onto data with its flag in the zero state. -/
def zeroFlagProjection : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks 1 0 0 0

/-- Operations preserving both sectors can be applied under the recorded flag,
after which the record is erased. The zero lower-left block states that the
final flag is zero for every input in the zero-flag sector.
Source: the coherent merging identity in Section 3 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem twoSectorEncoder_merge (P X₀ X₁ : Matrix n n ℂ) (hP : IsIdempotentElem P)
    (h₀ : Commute P X₀) (h₁ : Commute P X₁) :
    twoSectorEncoder P * fromBlocks X₀ 0 0 X₁ * twoSectorEncoder P * zeroFlagProjection =
      fromBlocks (X₀ * P + X₁ * (1 - P)) 0 0 0 := by
  simp only [twoSectorEncoder, zeroFlagProjection, fromBlocks_multiply,
    mul_zero, add_zero, zero_add, mul_one]
  rw [h₀.eq, ((Commute.one_left X₁).sub_left h₁).eq,
    ((Commute.one_left X₀).sub_left h₀).eq, h₁.eq]
  simp only [mul_assoc, hP.eq, hP.one_sub.eq, hP.one_sub_mul_self,
    hP.mul_one_sub_self, mul_zero, add_zero]

/-- A Hermitian involution defines its positive eigenspace projection as
`(1 + R) / 2`. The complementary projection is provided by
`IsStarProjection.one_sub`. -/
theorem isStarProjection_half_one_add (R : Matrix n n ℂ)
    (hR : IsSelfAdjoint R) (hRR : R * R = 1) :
    IsStarProjection ((1 / 2 : ℂ) • (1 + R)) := by
  rw [isStarProjection_iff']
  constructor
  · simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
      one_mul, mul_one, hRR]
    module
  · simp [star_smul, hR.star_eq]

/-- A Hadamard on the flag, with identity action on the data. -/
noncomputable def flagHadamard : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Complex.invSqrtTwo • fromBlocks 1 1 1 (-1)

/-- Conjugation of a two-block diagonal operator by the flag Hadamard. -/
theorem flagHadamard_mul_diagonal_mul (A B : Matrix n n ℂ) :
    flagHadamard * fromBlocks A 0 0 B * flagHadamard =
      (1 / 2 : ℂ) • fromBlocks (A + B) (A - B) (A - B) (A + B) := by
  simp only [flagHadamard, smul_mul_assoc, mul_smul_comm, smul_smul,
    Complex.invSqrtTwo_mul_self, fromBlocks_multiply, one_mul, mul_one,
    mul_zero, add_zero, zero_add, neg_mul, mul_neg, smul_neg, neg_neg,
    fromBlocks_smul, sub_eq_add_neg, one_div]
  simp only [smul_add, smul_neg]

/-- Hadamard, controlled `R`, and Hadamard again give the sector encoder.
For a Hermitian involution, `isStarProjection_half_one_add` makes this a
unitary recording of its positive and negative eigenspaces.
Source: `E_c` in Section 3 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem flagHadamard_mul_controlled_mul (R : Matrix n n ℂ) :
    flagHadamard * fromBlocks 1 0 0 R * flagHadamard =
      twoSectorEncoder ((1 / 2 : ℂ) • (1 + R)) := by
  rw [flagHadamard_mul_diagonal_mul]
  simp only [twoSectorEncoder, fromBlocks_smul]
  congr 1 <;> module

/-- A common final factor combines with the sector encoder into two controlled
factors between Hadamards. -/
theorem diagonal_mul_twoSectorEncoder (B R : Matrix n n ℂ) :
    fromBlocks B 0 0 B * twoSectorEncoder ((1 / 2 : ℂ) • (1 + R)) =
      flagHadamard * fromBlocks B 0 0 (B * R) * flagHadamard := by
  rw [flagHadamard_mul_diagonal_mul]
  simp only [twoSectorEncoder, fromBlocks_multiply, zero_mul,
    add_zero, mul_smul_comm, mul_add, mul_sub, mul_one, fromBlocks_smul]
  congr 1 <;> module

/-- For a unitary common factor `B` and relative operator `Bᴴ * C`, sector
erasure and the final factor use the two blocks `B` and `C`.
This is the cancellation that reduces the seven-call construction to six
child calls in Section 3 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The equality itself does
not require the relative operator to be a Hermitian involution. -/
theorem diagonal_mul_twoSectorEncoder_of_mem_unitaryGroup (B C : Matrix n n ℂ)
    (hB : B ∈ unitaryGroup n ℂ) :
    fromBlocks B 0 0 B * twoSectorEncoder ((1 / 2 : ℂ) • (1 + Bᴴ * C)) =
      flagHadamard * fromBlocks B 0 0 C * flagHadamard := by
  have hBC : B * (Bᴴ * C) = C := by
    simp only [← mul_assoc, ← star_eq_conjTranspose, hB.2, one_mul]
  simpa only [hBC] using diagonal_mul_twoSectorEncoder B (Bᴴ * C)

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Operators on the two distinct tensor factors commute. -/
theorem one_kronecker_commute_kronecker_one (P : Matrix n n ℂ) (X : Matrix m m ℂ) :
    Commute ((1 : Matrix m m ℂ) ⊗ₖ P) (X ⊗ₖ (1 : Matrix n n ℂ)) := by
  change (1 ⊗ₖ P) * (X ⊗ₖ 1) = (X ⊗ₖ 1) * (1 ⊗ₖ P)
  simp only [← mul_kronecker_mul, one_mul, mul_one]

/-- Coherently record a sector on the second factor, apply the two corresponding
operations on the first factor, and erase the flag. The resulting physical
operator is `X₀ ⊗ P + X₁ ⊗ (1 - P)` and the auxiliary flag is zero.
Source: the two-sector merging step in Section 3 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem twoSectorEncoder_merge_kronecker (P : Matrix n n ℂ) (X₀ X₁ : Matrix m m ℂ)
    (hP : IsIdempotentElem P) :
    twoSectorEncoder ((1 : Matrix m m ℂ) ⊗ₖ P) *
      fromBlocks (X₀ ⊗ₖ (1 : Matrix n n ℂ)) 0 0 (X₁ ⊗ₖ (1 : Matrix n n ℂ)) *
      twoSectorEncoder ((1 : Matrix m m ℂ) ⊗ₖ P) * zeroFlagProjection =
        fromBlocks (X₀ ⊗ₖ P + X₁ ⊗ₖ (1 - P)) 0 0 0 := by
  have hIP : IsIdempotentElem ((1 : Matrix m m ℂ) ⊗ₖ P) := by
    change (1 ⊗ₖ P) * (1 ⊗ₖ P) = 1 ⊗ₖ P
    simp only [← mul_kronecker_mul, hP.eq, one_mul]
  have hcompl : (1 : Matrix m m ℂ) ⊗ₖ (1 - P) = 1 - (1 : Matrix m m ℂ) ⊗ₖ P := by
    rw [← one_kronecker_one (m := m) (n := n)]
    ext i j; simp only [kroneckerMap_apply, sub_apply, mul_sub]
  have h := twoSectorEncoder_merge ((1 : Matrix m m ℂ) ⊗ₖ P)
    (X₀ ⊗ₖ (1 : Matrix n n ℂ)) (X₁ ⊗ₖ (1 : Matrix n n ℂ)) hIP
    (one_kronecker_commute_kronecker_one P X₀)
    (one_kronecker_commute_kronecker_one P X₁)
  simpa only [← hcompl, ← mul_kronecker_mul, mul_one, one_mul] using h

end Matrix

end
