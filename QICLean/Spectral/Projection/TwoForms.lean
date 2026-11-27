/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import QICLean.Analysis.Support.InverseSandwich

/-!
# Spectral projection splitting of two positive-semidefinite forms

Given two positive-semidefinite matrices `E₀, E₁ : Matrix A A ℂ` on an arbitrary finite
basis `A`, without assuming commutativity or invertibility of `H = E₀ + E₁`, this file
constructs complementary oblique idempotents `R₀` and `R₁ = 1 - R₀` on `A` such that:

* the cross-forms vanish at the operator level:
  `R₁ᴴ * E₀ * R₀ = 0`, `R₁ᴴ * E₁ * R₀ = 0`, `R₀ᴴ * E₀ * R₁ = 0`, `R₀ᴴ * E₁ * R₁ = 0`;
* the compressed differences are sign-definite:
  `(R₀ᴴ * (E₀ - E₁) * R₀).PosSemidef` and `(R₁ᴴ * (E₁ - E₀) * R₁).PosSemidef`.

Applying `R₀ ⊗ₖ 1` and `R₁ ⊗ₖ 1` to an arbitrary bipartite vector `u : A × B → ℂ` splits
`u = v + w` so that for every positive-semidefinite operator `F` on `B` (simultaneously
for any family `(F j)`), the cross-forms `⟨w | (Eᵢ ⊗ F) | v⟩` vanish,
`⟨v | (E₀ - E₁) ⊗ F | v⟩ ≥ 0`, and `⟨w | (E₁ - E₀) ⊗ F | w⟩ ≥ 0`.

## Proof mechanism

1. **Normalized forms on a projection:** When `E₀', E₁' ≥ 0` sum to an orthogonal projection `Q`,
   both are absorbed by `Q`, hence commute. The nonnegative spectral projection `P` of
   `E₀' - E₁'` commutes with `Q`, `E₀'`, and `E₁'`, giving `(1 - P) * Eᵢ' * P = 0`,
   `P * (E₀' - E₁') * P ≥ 0`, and `(1 - P) * (E₁' - E₀') * (1 - P) ≥ 0`.
2. **Support whitening (including singular `H` and `H = 0`):** For `H = E₀ + E₁ ≥ 0` with
   support projection `Q`, define `N = H⁻¹/² Q + (1 - Q)` and `M = H¹/² + (1 - Q)`.
   Then `N` and `M` are Hermitian mutual inverses, `N * H * N = Q`, and `Eᵢ' = N * Eᵢ * N`
   satisfy `E₀' + E₁' = Q`.
3. **Oblique pull-back and bipartite split:** Setting `R₀ = N * P * M` and
   `R₁ = 1 - R₀ = N * (1 - P) * M` transfers the orthogonality and sign-definiteness
   identities to `(E₀, E₁)`, and tensoring with `1_B` produces `u = v + w`.

## Main declarations

* `Matrix.nonnegSpectralProj`: spectral projection onto the nonnegative eigenvalues of a
  Hermitian matrix.
* `Matrix.PosSemidef.supportWhitening` and `Matrix.PosSemidef.supportWhiteningInv`:
  ambient invertible whitening operator `H⁻¹/² Q + (1 - Q)` and its inverse `H¹/² + (1 - Q)`.
* `Matrix.twoFormSplitProj`: oblique idempotent `R₀` splitting two arbitrary PSD forms.
* `Matrix.exists_twoForms_bipartite_split`: bipartite vector decomposition `v + w = u`
  simultaneously valid for an arbitrary family of PSD matrices on `B`.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker

namespace Matrix

section NonnegSpectralProj

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The spectral projection of a matrix `D` onto its nonnegative eigenvalues, defined via the
real continuous functional calculus of the indicator `fun t : ℝ ↦ if 0 ≤ t then 1 else 0`. -/
noncomputable def nonnegSpectralProj (D : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc (fun t : ℝ ↦ if 0 ≤ t then 1 else 0) D

/-- The nonnegative spectral projection of a Hermitian matrix is an orthogonal projection. -/
theorem isStarProjection_nonnegSpectralProj {D : Matrix ι ι ℂ} (hD : D.IsHermitian) :
    IsStarProjection (nonnegSpectralProj D) := by
  rw [isStarProjection_iff']
  constructor
  · rw [nonnegSpectralProj, hD.cfc_eq, ← hD.cfc_mul]
    congr 1
    funext t
    split_ifs <;> norm_num
  · exact (cfc_predicate _ D : IsSelfAdjoint (nonnegSpectralProj D))

/-- The nonnegative spectral projection of a Hermitian matrix is Hermitian. -/
theorem nonnegSpectralProj_isHermitian {D : Matrix ι ι ℂ} (hD : D.IsHermitian) :
    (nonnegSpectralProj D).IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.mpr (isStarProjection_nonnegSpectralProj hD).isSelfAdjoint

/-- The nonnegative spectral projection of a Hermitian matrix is idempotent. -/
theorem nonnegSpectralProj_mul_self {D : Matrix ι ι ℂ} (hD : D.IsHermitian) :
    nonnegSpectralProj D * nonnegSpectralProj D = nonnegSpectralProj D :=
  (isStarProjection_nonnegSpectralProj hD).isIdempotentElem

/-- The nonnegative spectral projection of `D` commutes with `D`. -/
theorem nonnegSpectralProj_commute_self {D : Matrix ι ι ℂ} (hD : D.IsHermitian) :
    Commute (nonnegSpectralProj D) D := by
  simpa only [nonnegSpectralProj, cfc_id ℝ D hD.isSelfAdjoint] using
    cfc_commute_cfc (fun t : ℝ ↦ if 0 ≤ t then 1 else 0) id D

/-- Any matrix commuting with `D` commutes with `nonnegSpectralProj D`. -/
theorem nonnegSpectralProj_commute_of_commute {D B : Matrix ι ι ℂ} (hDB : Commute D B) :
    Commute (nonnegSpectralProj D) B :=
  hDB.cfc_real (fun t : ℝ ↦ if 0 ≤ t then 1 else 0)

/-- Compressing a Hermitian matrix `D` by its nonnegative spectral projection yields a
positive-semidefinite matrix. -/
theorem nonnegSpectralProj_mul_mul_posSemidef {D : Matrix ι ι ℂ} (hD : D.IsHermitian) :
    (nonnegSpectralProj D * D * nonnegSpectralProj D).PosSemidef := by
  have hEq :
      nonnegSpectralProj D * D * nonnegSpectralProj D =
        cfc (fun t : ℝ ↦ if 0 ≤ t then t else 0) D := by
    rw [nonnegSpectralProj, hD.cfc_eq, hD.cfc_eq]
    nth_rewrite 2 [← hD.cfc_id]
    rw [← hD.cfc_mul, ← hD.cfc_mul]
    congr 1
    funext t
    split_ifs <;> simp
  rw [hEq]
  refine Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg fun t _ ↦ ?_)
  split_ifs with ht
  · exact ht
  · exact le_rfl

/-- Compressing `-D` by the complementary projection `1 - nonnegSpectralProj D` yields a
positive-semidefinite matrix. -/
theorem one_sub_nonnegSpectralProj_mul_neg_mul_posSemidef {D : Matrix ι ι ℂ} (hD : D.IsHermitian) :
    ((1 - nonnegSpectralProj D) * (-D) * (1 - nonnegSpectralProj D)).PosSemidef := by
  have hOne : (1 : Matrix ι ι ℂ) - nonnegSpectralProj D =
      cfc (fun t : ℝ ↦ if 0 ≤ t then 0 else 1) D := by
    have h1 : (1 : Matrix ι ι ℂ) = cfc (fun _ : ℝ ↦ (1 : ℝ)) D := (cfc_const_one ℝ D).symm
    rw [h1, nonnegSpectralProj, ← cfc_sub (fun _ : ℝ ↦ (1 : ℝ))
      (fun t : ℝ ↦ if 0 ≤ t then 1 else 0) D
      (hf := D.finite_real_spectrum.continuousOn _)
      (hg := D.finite_real_spectrum.continuousOn _)]
    refine cfc_congr fun t _ ↦ ?_
    split_ifs <;> norm_num
  have hNeg : -D = cfc (fun t : ℝ ↦ -t) D := by
    simpa only [cfc_id' ℝ D hD.isSelfAdjoint] using (cfc_neg (f := fun t : ℝ ↦ t) D).symm
  have hEq :
      (1 - nonnegSpectralProj D) * (-D) * (1 - nonnegSpectralProj D) =
        cfc (fun t : ℝ ↦ if 0 ≤ t then 0 else -t) D := by
    rw [hOne, hNeg, hD.cfc_eq, hD.cfc_eq, hD.cfc_eq, ← hD.cfc_mul, ← hD.cfc_mul]
    congr 1
    funext t
    split_ifs <;> simp
  rw [hEq]
  refine Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg fun t _ ↦ ?_)
  split_ifs with ht
  · exact le_rfl
  · linarith

end NonnegSpectralProj

section NormalizedSplit

variable {ι : Type*} [Fintype ι]

/-- If `E₀, E₁ ≥ 0` sum to an orthogonal projection `Q`, then `Q` absorbs `E₀` on the right. -/
theorem mul_eq_self_of_add_eq_isStarProjection_left
    {E₀ E₁ Q : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef)
    (hQ : IsStarProjection Q) (hsum : E₀ + E₁ = Q) :
    E₀ * Q = E₀ := by
  classical
  have hle : E₀ ≤ Q := by
    rw [Matrix.le_iff, ← hsum, add_sub_cancel_left]
    exact hE₁
  have hsub : E₀ * (1 - Q) = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    apply hE₀.mulVec_eq_zero_of_le hle
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hQ.isIdempotentElem, sub_self,
      Matrix.zero_mulVec]
  exact (by simpa [Matrix.mul_sub, sub_eq_zero] using hsub : E₀ = E₀ * Q).symm

/-- If `E₀, E₁ ≥ 0` sum to an orthogonal projection `Q`, then `Q` absorbs `E₀` on the left. -/
theorem eq_self_mul_of_add_eq_isStarProjection_left
    {E₀ E₁ Q : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef)
    (hQ : IsStarProjection Q) (hsum : E₀ + E₁ = Q) :
    Q * E₀ = E₀ := by
  have hHerm : Q.IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr hQ.isSelfAdjoint
  simpa only [Matrix.conjTranspose_mul, hHerm.eq, hE₀.isHermitian.eq] using
    congrArg Matrix.conjTranspose (mul_eq_self_of_add_eq_isStarProjection_left hE₀ hE₁ hQ hsum)

/-- If `E₀, E₁ ≥ 0` sum to an orthogonal projection `Q`, then `Q` absorbs `E₁` on the right. -/
theorem mul_eq_self_of_add_eq_isStarProjection_right
    {E₀ E₁ Q : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef)
    (hQ : IsStarProjection Q) (hsum : E₀ + E₁ = Q) :
    E₁ * Q = E₁ :=
  mul_eq_self_of_add_eq_isStarProjection_left hE₁ hE₀ hQ (by rw [add_comm, hsum])

/-- If `E₀, E₁ ≥ 0` sum to an orthogonal projection `Q`, then `Q` absorbs `E₁` on the left. -/
theorem eq_self_mul_of_add_eq_isStarProjection_right
    {E₀ E₁ Q : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef)
    (hQ : IsStarProjection Q) (hsum : E₀ + E₁ = Q) :
    Q * E₁ = E₁ :=
  eq_self_mul_of_add_eq_isStarProjection_left hE₁ hE₀ hQ (by rw [add_comm, hsum])

/-- Two positive-semidefinite matrices summing to an orthogonal projection commute. -/
theorem commute_of_add_eq_isStarProjection
    {E₀ E₁ Q : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef)
    (hQ : IsStarProjection Q) (hsum : E₀ + E₁ = Q) :
    Commute E₀ E₁ := by
  have hE₁_eq : E₁ = Q - E₀ := eq_sub_of_add_eq' hsum
  have hR := mul_eq_self_of_add_eq_isStarProjection_left hE₀ hE₁ hQ hsum
  have hL := eq_self_mul_of_add_eq_isStarProjection_left hE₀ hE₁ hQ hsum
  rw [Commute, SemiconjBy, hE₁_eq, Matrix.mul_sub, Matrix.sub_mul, hR, hL]

variable [DecidableEq ι]

/-- For `E₀, E₁ ≥ 0` summing to an orthogonal projection `Q`, the nonnegative spectral
projection of `E₀ - E₁` commutes with `E₀`. -/
theorem nonnegSpectralProj_sub_commute_left
    {E₀ E₁ Q : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef)
    (hQ : IsStarProjection Q) (hsum : E₀ + E₁ = Q) :
    Commute (nonnegSpectralProj (E₀ - E₁)) E₀ := by
  have hcomm : Commute (E₀ - E₁) E₀ := by
    have h01 := commute_of_add_eq_isStarProjection hE₀ hE₁ hQ hsum
    exact (Commute.refl E₀).sub_left h01.symm
  exact nonnegSpectralProj_commute_of_commute hcomm

/-- For `E₀, E₁ ≥ 0` summing to an orthogonal projection `Q`, the nonnegative spectral
projection of `E₀ - E₁` commutes with `E₁`. -/
theorem nonnegSpectralProj_sub_commute_right
    {E₀ E₁ Q : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef)
    (hQ : IsStarProjection Q) (hsum : E₀ + E₁ = Q) :
    Commute (nonnegSpectralProj (E₀ - E₁)) E₁ := by
  have hcomm : Commute (E₀ - E₁) E₁ := by
    have h01 := commute_of_add_eq_isStarProjection hE₀ hE₁ hQ hsum
    exact h01.sub_left (Commute.refl E₁)
  exact nonnegSpectralProj_commute_of_commute hcomm

/-- Off-diagonal vanishing `(1 - P) * E₀ * P = 0` for normalized forms summing to a projection. -/
theorem one_sub_nonnegSpectralProj_mul_left_mul_eq_zero
    {E₀ E₁ Q : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef)
    (hQ : IsStarProjection Q) (hsum : E₀ + E₁ = Q) :
    (1 - nonnegSpectralProj (E₀ - E₁)) * E₀ * nonnegSpectralProj (E₀ - E₁) = 0 := by
  set P := nonnegSpectralProj (E₀ - E₁)
  have hD : (E₀ - E₁).IsHermitian := hE₀.isHermitian.sub hE₁.isHermitian
  have hP2 : P * P = P := nonnegSpectralProj_mul_self hD
  have hPE₀ : P * E₀ = E₀ * P := (nonnegSpectralProj_sub_commute_left hE₀ hE₁ hQ hsum).eq
  calc
    (1 - P) * E₀ * P = (1 - P) * (E₀ * P) := Matrix.mul_assoc ..
    _ = (1 - P) * (P * E₀) := by rw [hPE₀]
    _ = ((1 - P) * P) * E₀ := (Matrix.mul_assoc ..).symm
    _ = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hP2, sub_self, Matrix.zero_mul]

/-- Off-diagonal vanishing `(1 - P) * E₁ * P = 0` for normalized forms summing to a projection. -/
theorem one_sub_nonnegSpectralProj_mul_right_mul_eq_zero
    {E₀ E₁ Q : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef)
    (hQ : IsStarProjection Q) (hsum : E₀ + E₁ = Q) :
    (1 - nonnegSpectralProj (E₀ - E₁)) * E₁ * nonnegSpectralProj (E₀ - E₁) = 0 := by
  set P := nonnegSpectralProj (E₀ - E₁)
  have hD : (E₀ - E₁).IsHermitian := hE₀.isHermitian.sub hE₁.isHermitian
  have hP2 : P * P = P := nonnegSpectralProj_mul_self hD
  have hPE₁ : P * E₁ = E₁ * P := (nonnegSpectralProj_sub_commute_right hE₀ hE₁ hQ hsum).eq
  calc
    (1 - P) * E₁ * P = (1 - P) * (E₁ * P) := Matrix.mul_assoc ..
    _ = (1 - P) * (P * E₁) := by rw [hPE₁]
    _ = ((1 - P) * P) * E₁ := (Matrix.mul_assoc ..).symm
    _ = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hP2, sub_self, Matrix.zero_mul]

/-- Off-diagonal vanishing `P * E₀ * (1 - P) = 0` for normalized forms summing to a projection. -/
theorem nonnegSpectralProj_mul_left_mul_one_sub_eq_zero
    {E₀ E₁ Q : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef)
    (hQ : IsStarProjection Q) (hsum : E₀ + E₁ = Q) :
    nonnegSpectralProj (E₀ - E₁) * E₀ * (1 - nonnegSpectralProj (E₀ - E₁)) = 0 := by
  have hD : (E₀ - E₁).IsHermitian := hE₀.isHermitian.sub hE₁.isHermitian
  have hP := nonnegSpectralProj_isHermitian hD
  have h := congrArg Matrix.conjTranspose
    (one_sub_nonnegSpectralProj_mul_left_mul_eq_zero hE₀ hE₁ hQ hsum)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_zero, hP.eq, hE₀.isHermitian.eq, Matrix.mul_assoc] using h

/-- Off-diagonal vanishing `P * E₁ * (1 - P) = 0` for normalized forms summing to a projection. -/
theorem nonnegSpectralProj_mul_right_mul_one_sub_eq_zero
    {E₀ E₁ Q : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef)
    (hQ : IsStarProjection Q) (hsum : E₀ + E₁ = Q) :
    nonnegSpectralProj (E₀ - E₁) * E₁ * (1 - nonnegSpectralProj (E₀ - E₁)) = 0 := by
  have hD : (E₀ - E₁).IsHermitian := hE₀.isHermitian.sub hE₁.isHermitian
  have hP := nonnegSpectralProj_isHermitian hD
  have h := congrArg Matrix.conjTranspose
    (one_sub_nonnegSpectralProj_mul_right_mul_eq_zero hE₀ hE₁ hQ hsum)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_zero, hP.eq, hE₁.isHermitian.eq, Matrix.mul_assoc] using h

end NormalizedSplit

section SupportWhitening

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ambient invertible whitening operator `N = H⁻¹/² Q + (1 - Q)` for an arbitrary
positive-semidefinite matrix `H`, acting as `H⁻¹/²` on the support of `H` and as the
identity on the kernel of `H`. -/
noncomputable def PosSemidef.supportWhitening {H : Matrix ι ι ℂ} (hH : H.PosSemidef) :
    Matrix ι ι ℂ :=
  hH.supportInvSqrt + (1 - hH.supportProj)

/-- Explicit inverse `M = H¹/² + (1 - Q)` of `PosSemidef.supportWhitening`. -/
noncomputable def PosSemidef.supportWhiteningInv {H : Matrix ι ι ℂ} (hH : H.PosSemidef) :
    Matrix ι ι ℂ :=
  hH.isHermitian.cfc Real.sqrt + (1 - hH.supportProj)

/-- The support whitening operator is Hermitian. -/
theorem PosSemidef.supportWhitening_isHermitian {H : Matrix ι ι ℂ} (hH : H.PosSemidef) :
    hH.supportWhitening.IsHermitian :=
  hH.supportInvSqrt_isHermitian.add (Matrix.isHermitian_one.sub hH.supportProj_isHermitian)

/-- The inverse of the support whitening operator is Hermitian. -/
theorem PosSemidef.supportWhiteningInv_isHermitian {H : Matrix ι ι ℂ} (hH : H.PosSemidef) :
    hH.supportWhiteningInv.IsHermitian :=
  hH.cfc_sqrt_isHermitian.add (Matrix.isHermitian_one.sub hH.supportProj_isHermitian)

/-- Right inverse identity `supportWhitening * supportWhiteningInv = 1`, valid for arbitrary
positive-semidefinite `H` (including singular `H` and `H = 0`). -/
theorem PosSemidef.supportWhitening_mul_supportWhiteningInv {H : Matrix ι ι ℂ}
    (hH : H.PosSemidef) :
    hH.supportWhitening * hH.supportWhiteningInv = 1 := by
  have h1 : hH.supportInvSqrt * (1 - hH.supportProj) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hH.supportInvSqrt_mul_supportProj, sub_self]
  have hsqrtL : hH.supportProj * hH.isHermitian.cfc Real.sqrt = hH.isHermitian.cfc Real.sqrt := by
    have h := congrArg Matrix.conjTranspose hH.cfc_sqrt_mul_supportProj
    simpa only [PosSemidef.supportProj, Matrix.conjTranspose_mul,
      hH.isHermitian.supportProj_isHermitian.eq, hH.cfc_sqrt_isHermitian.eq] using h
  have h2 : (1 - hH.supportProj) * hH.isHermitian.cfc Real.sqrt = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hsqrtL, sub_self]
  have h3 : (1 - hH.supportProj) * (1 - hH.supportProj) = 1 - hH.supportProj :=
    hH.isHermitian.one_sub_supportProj_idem
  rw [PosSemidef.supportWhitening, PosSemidef.supportWhiteningInv,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    hH.supportInvSqrt_mul_cfc_sqrt, h1, h2, h3, add_zero, zero_add, add_sub_cancel]

/-- Left inverse identity `supportWhiteningInv * supportWhitening = 1`. -/
theorem PosSemidef.supportWhiteningInv_mul_supportWhitening {H : Matrix ι ι ℂ}
    (hH : H.PosSemidef) :
    hH.supportWhiteningInv * hH.supportWhitening = 1 := by
  have h := congrArg Matrix.conjTranspose hH.supportWhitening_mul_supportWhiteningInv
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one,
    hH.supportWhitening_isHermitian.eq, hH.supportWhiteningInv_isHermitian.eq] using h

/-- The support whitening operator is always positive definite (even when `H` is singular or
zero). -/
theorem PosSemidef.supportWhitening_posDef {H : Matrix ι ι ℂ} (hH : H.PosSemidef) :
    hH.supportWhitening.PosDef := by
  have hcompHerm : (1 - hH.supportProj).IsHermitian :=
    Matrix.isHermitian_one.sub hH.supportProj_isHermitian
  have hcompPSD : (1 - hH.supportProj).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hcompHerm fun x ↦ ?_
    calc
      0 ≤ star ((1 - hH.supportProj) *ᵥ x) ⬝ᵥ ((1 - hH.supportProj) *ᵥ x) :=
        dotProduct_star_self_nonneg _
      _ = star x ⬝ᵥ ((1 - hH.supportProj) * (1 - hH.supportProj)) *ᵥ x := by
        rw [← Matrix.mulVec_mulVec, hcompHerm.star_mulVec_dotProduct]
      _ = star x ⬝ᵥ (1 - hH.supportProj) *ᵥ x := by
        have hidem : (1 - hH.supportProj) * (1 - hH.supportProj) = 1 - hH.supportProj :=
          hH.isHermitian.one_sub_supportProj_idem
        rw [hidem]
  have hPSD : hH.supportWhitening.PosSemidef := hH.supportInvSqrt_posSemidef.add hcompPSD
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH.supportWhitening_isHermitian fun x hx ↦ ?_
  have hnonneg : 0 ≤ star x ⬝ᵥ hH.supportWhitening *ᵥ x := hPSD.dotProduct_mulVec_nonneg x
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have hmul : hH.supportWhitening *ᵥ x = 0 := hPSD.dotProduct_mulVec_zero_iff.mp hzero.symm
  have hx0 : x = 0 := by
    calc
      x = (1 : Matrix ι ι ℂ) *ᵥ x := (Matrix.one_mulVec x).symm
      _ = (hH.supportWhiteningInv * hH.supportWhitening) *ᵥ x := by
        rw [hH.supportWhiteningInv_mul_supportWhitening]
      _ = hH.supportWhiteningInv *ᵥ (hH.supportWhitening *ᵥ x) := (Matrix.mulVec_mulVec ..).symm
      _ = 0 := by rw [hmul, Matrix.mulVec_zero]
  exact hx hx0

/-- Sandwiching `H` by its support whitening operator produces its support projection:
`N * H * N = Q`. -/
theorem PosSemidef.supportWhitening_mul_self_mul_supportWhitening {H : Matrix ι ι ℂ}
    (hH : H.PosSemidef) :
    hH.supportWhitening * H * hH.supportWhitening = hH.supportProj := by
  have hL : (1 - hH.supportProj) * H = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hH.supportProj_mul_self, sub_self]
  have hR : H * (1 - hH.supportProj) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hH.mul_supportProj_self, sub_self]
  calc
    hH.supportWhitening * H * hH.supportWhitening =
        (hH.supportInvSqrt * H + (1 - hH.supportProj) * H) * hH.supportWhitening := by
      rw [PosSemidef.supportWhitening, Matrix.add_mul]
    _ = hH.supportInvSqrt * H * hH.supportInvSqrt +
          hH.supportInvSqrt * (H * (1 - hH.supportProj)) := by
      rw [hL, add_zero, PosSemidef.supportWhitening, Matrix.mul_add]
      simp only [Matrix.mul_assoc]
    _ = hH.supportInvSqrt * H * hH.supportInvSqrt := by
      rw [hR, Matrix.mul_zero, add_zero]
    _ = hH.supportProj := hH.supportInvSqrt_mul_self_mul_supportInvSqrt

/-- For any positive-semidefinite matrix `E ≤ H`, whitening by `supportWhitening` agrees with
sandwiching by `supportInvSqrt`. -/
theorem PosSemidef.supportWhitening_mul_mul_supportWhitening_of_le
    {E H : Matrix ι ι ℂ} (hE : E.PosSemidef) (hH : H.PosSemidef) (hEH : E ≤ H) :
    hH.supportWhitening * E * hH.supportWhitening =
      hH.supportInvSqrt * E * hH.supportInvSqrt := by
  have hL : (1 - hH.supportProj) * E = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hE.supportProj_mul_eq_self_of_le hH hEH, sub_self]
  have hR : E * (1 - hH.supportProj) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hE.mul_supportProj_eq_self_of_le hH hEH, sub_self]
  calc
    hH.supportWhitening * E * hH.supportWhitening =
        (hH.supportInvSqrt * E + (1 - hH.supportProj) * E) * hH.supportWhitening := by
      rw [PosSemidef.supportWhitening, Matrix.add_mul]
    _ = hH.supportInvSqrt * E * hH.supportInvSqrt +
          hH.supportInvSqrt * (E * (1 - hH.supportProj)) := by
      rw [hL, add_zero, PosSemidef.supportWhitening, Matrix.mul_add]
      simp only [Matrix.mul_assoc]
    _ = hH.supportInvSqrt * E * hH.supportInvSqrt := by
      rw [hR, Matrix.mul_zero, add_zero]

/-- For a positive-definite matrix `H`, `supportWhitening` coincides with `(CFC.sqrt H)⁻¹`. -/
theorem PosDef.supportWhitening_eq_inv_sqrt {H : Matrix ι ι ℂ} (hH : H.PosDef) :
    hH.posSemidef.supportWhitening = (CFC.sqrt H)⁻¹ := by
  rw [PosSemidef.supportWhitening, hH.supportProj_eq_one, sub_self, add_zero,
    hH.supportInvSqrt_eq_inv_sqrt]

/-- For a positive-definite matrix `H`, `supportWhiteningInv` coincides with `CFC.sqrt H`. -/
theorem PosDef.supportWhiteningInv_eq_sqrt {H : Matrix ι ι ℂ} (hH : H.PosDef) :
    hH.posSemidef.supportWhiteningInv = CFC.sqrt H := by
  rw [PosSemidef.supportWhiteningInv, hH.supportProj_eq_one, sub_self, add_zero,
    CFC.sqrt_eq_real_sqrt H hH.posSemidef.nonneg, cfcₙ_eq_cfc, hH.isHermitian.cfc_eq]

end SupportWhitening

section TwoFormSplit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Helper: conjugating a PSD matrix by a Hermitian matrix preserves PSD. -/
private theorem posSemidef_mul_mul_of_isHermitian {E N : Matrix ι ι ℂ}
    (hE : E.PosSemidef) (hN : N.IsHermitian) : (N * E * N).PosSemidef := by
  have h := hE.mul_mul_conjTranspose_same N
  rwa [hN.eq] at h

/-- Support projection of a positive-semidefinite matrix is a star projection. -/
private theorem PosSemidef.isStarProjection_supportProj {H : Matrix ι ι ℂ} (hH : H.PosSemidef) :
    IsStarProjection hH.supportProj := by
  rw [isStarProjection_iff']
  exact ⟨hH.supportProj_idem,
    Matrix.isHermitian_iff_isSelfAdjoint.mp hH.supportProj_isHermitian⟩

/-- The oblique idempotent `R₀ = N * P * M` splitting two arbitrary positive-semidefinite
matrices `E₀, E₁`, where `N` is the support whitening of `H = E₀ + E₁`, `M = N⁻¹`, and
`P` is the nonnegative spectral projection of `N * (E₀ - E₁) * N`. -/
noncomputable def twoFormSplitProj {E₀ E₁ : Matrix ι ι ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) : Matrix ι ι ℂ :=
  let hH := hE₀.add hE₁
  let N := hH.supportWhitening
  let M := hH.supportWhiteningInv
  let P := nonnegSpectralProj (N * E₀ * N - N * E₁ * N)
  N * P * M

/-- The complementary oblique idempotent `1 - R₀` equals `N * (1 - P) * M`. -/
theorem one_sub_twoFormSplitProj_eq {E₀ E₁ : Matrix ι ι ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) :
    let hH := hE₀.add hE₁
    let N := hH.supportWhitening
    let M := hH.supportWhiteningInv
    let P := nonnegSpectralProj (N * E₀ * N - N * E₁ * N)
    1 - twoFormSplitProj hE₀ hE₁ = N * (1 - P) * M := by
  dsimp only [twoFormSplitProj]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
    (hE₀.add hE₁).supportWhitening_mul_supportWhiteningInv]

/-- The oblique splitting operator `R₀` is idempotent: `R₀ * R₀ = R₀`. -/
theorem twoFormSplitProj_mul_self {E₀ E₁ : Matrix ι ι ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) :
    twoFormSplitProj hE₀ hE₁ * twoFormSplitProj hE₀ hE₁ = twoFormSplitProj hE₀ hE₁ := by
  dsimp only [twoFormSplitProj]
  generalize hNdef : (hE₀.add hE₁).supportWhitening = N
  generalize hMdef : (hE₀.add hE₁).supportWhiteningInv = M
  have hN : N.IsHermitian := hNdef ▸ (hE₀.add hE₁).supportWhitening_isHermitian
  have hMN : M * N = 1 := hNdef ▸ hMdef ▸ (hE₀.add hE₁).supportWhiteningInv_mul_supportWhitening
  have hE₀' : (N * E₀ * N).PosSemidef := posSemidef_mul_mul_of_isHermitian hE₀ hN
  have hE₁' : (N * E₁ * N).PosSemidef := posSemidef_mul_mul_of_isHermitian hE₁ hN
  have hD : (N * E₀ * N - N * E₁ * N).IsHermitian := hE₀'.isHermitian.sub hE₁'.isHermitian
  set P := nonnegSpectralProj (N * E₀ * N - N * E₁ * N)
  have hP2 : P * P = P := nonnegSpectralProj_mul_self hD
  calc
    (N * P * M) * (N * P * M) = N * P * ((M * N) * P) * M := by simp only [Matrix.mul_assoc]
    _ = N * (P * P) * M := by rw [hMN, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    _ = N * P * M := by rw [hP2]

/-- Operator-level cross-form vanishing `(1 - R₀)ᴴ * E₀ * R₀ = 0`. -/
theorem one_sub_twoFormSplitProj_conjTranspose_mul_left_mul
    {E₀ E₁ : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) :
    (1 - twoFormSplitProj hE₀ hE₁)ᴴ * E₀ * twoFormSplitProj hE₀ hE₁ = 0 := by
  rw [one_sub_twoFormSplitProj_eq hE₀ hE₁]
  dsimp only [twoFormSplitProj]
  generalize hNdef : (hE₀.add hE₁).supportWhitening = N
  generalize hMdef : (hE₀.add hE₁).supportWhiteningInv = M
  have hN : N.IsHermitian := hNdef ▸ (hE₀.add hE₁).supportWhitening_isHermitian
  have hM : M.IsHermitian := hMdef ▸ (hE₀.add hE₁).supportWhiteningInv_isHermitian
  have hE₀' : (N * E₀ * N).PosSemidef := posSemidef_mul_mul_of_isHermitian hE₀ hN
  have hE₁' : (N * E₁ * N).PosSemidef := posSemidef_mul_mul_of_isHermitian hE₁ hN
  have hsum : N * E₀ * N + N * E₁ * N = (hE₀.add hE₁).supportProj := by
    have h := hNdef ▸ (hE₀.add hE₁).supportWhitening_mul_self_mul_supportWhitening
    simpa only [Matrix.mul_add, Matrix.add_mul] using h
  have hD : (N * E₀ * N - N * E₁ * N).IsHermitian := hE₀'.isHermitian.sub hE₁'.isHermitian
  set P := nonnegSpectralProj (N * E₀ * N - N * E₁ * N)
  have hP : P.IsHermitian := nonnegSpectralProj_isHermitian hD
  have hvan : (1 - P) * (N * E₀ * N) * P = 0 :=
    one_sub_nonnegSpectralProj_mul_left_mul_eq_zero hE₀' hE₁'
      (hE₀.add hE₁).isStarProjection_supportProj hsum
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    hN.eq, hM.eq, hP.eq]
  calc
    M * ((1 - P) * N) * E₀ * (N * P * M) = M * ((1 - P) * (N * E₀ * N) * P) * M := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hvan, Matrix.mul_zero, Matrix.zero_mul]

/-- Operator-level cross-form vanishing `(1 - R₀)ᴴ * E₁ * R₀ = 0`. -/
theorem one_sub_twoFormSplitProj_conjTranspose_mul_right_mul
    {E₀ E₁ : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) :
    (1 - twoFormSplitProj hE₀ hE₁)ᴴ * E₁ * twoFormSplitProj hE₀ hE₁ = 0 := by
  rw [one_sub_twoFormSplitProj_eq hE₀ hE₁]
  dsimp only [twoFormSplitProj]
  generalize hNdef : (hE₀.add hE₁).supportWhitening = N
  generalize hMdef : (hE₀.add hE₁).supportWhiteningInv = M
  have hN : N.IsHermitian := hNdef ▸ (hE₀.add hE₁).supportWhitening_isHermitian
  have hM : M.IsHermitian := hMdef ▸ (hE₀.add hE₁).supportWhiteningInv_isHermitian
  have hE₀' : (N * E₀ * N).PosSemidef := posSemidef_mul_mul_of_isHermitian hE₀ hN
  have hE₁' : (N * E₁ * N).PosSemidef := posSemidef_mul_mul_of_isHermitian hE₁ hN
  have hsum : N * E₀ * N + N * E₁ * N = (hE₀.add hE₁).supportProj := by
    have h := hNdef ▸ (hE₀.add hE₁).supportWhitening_mul_self_mul_supportWhitening
    simpa only [Matrix.mul_add, Matrix.add_mul] using h
  have hD : (N * E₀ * N - N * E₁ * N).IsHermitian := hE₀'.isHermitian.sub hE₁'.isHermitian
  set P := nonnegSpectralProj (N * E₀ * N - N * E₁ * N)
  have hP : P.IsHermitian := nonnegSpectralProj_isHermitian hD
  have hvan : (1 - P) * (N * E₁ * N) * P = 0 :=
    one_sub_nonnegSpectralProj_mul_right_mul_eq_zero hE₀' hE₁'
      (hE₀.add hE₁).isStarProjection_supportProj hsum
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    hN.eq, hM.eq, hP.eq]
  calc
    M * ((1 - P) * N) * E₁ * (N * P * M) = M * ((1 - P) * (N * E₁ * N) * P) * M := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hvan, Matrix.mul_zero, Matrix.zero_mul]

/-- Operator-level cross-form vanishing `R₀ᴴ * E₀ * (1 - R₀) = 0`. -/
theorem twoFormSplitProj_conjTranspose_mul_left_mul_one_sub
    {E₀ E₁ : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) :
    (twoFormSplitProj hE₀ hE₁)ᴴ * E₀ * (1 - twoFormSplitProj hE₀ hE₁) = 0 := by
  have h := congrArg Matrix.conjTranspose
    (one_sub_twoFormSplitProj_conjTranspose_mul_left_mul hE₀ hE₁)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero, hE₀.isHermitian.eq, Matrix.mul_assoc] using h

/-- Operator-level cross-form vanishing `R₀ᴴ * E₁ * (1 - R₀) = 0`. -/
theorem twoFormSplitProj_conjTranspose_mul_right_mul_one_sub
    {E₀ E₁ : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) :
    (twoFormSplitProj hE₀ hE₁)ᴴ * E₁ * (1 - twoFormSplitProj hE₀ hE₁) = 0 := by
  have h := congrArg Matrix.conjTranspose
    (one_sub_twoFormSplitProj_conjTranspose_mul_right_mul hE₀ hE₁)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero, hE₁.isHermitian.eq, Matrix.mul_assoc] using h

/-- Sign-definiteness on the first sector: `R₀ᴴ * (E₀ - E₁) * R₀ ≥ 0`. -/
theorem twoFormSplitProj_conjTranspose_mul_sub_mul_posSemidef
    {E₀ E₁ : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) :
    ((twoFormSplitProj hE₀ hE₁)ᴴ * (E₀ - E₁) * twoFormSplitProj hE₀ hE₁).PosSemidef := by
  dsimp only [twoFormSplitProj]
  generalize hNdef : (hE₀.add hE₁).supportWhitening = N
  generalize hMdef : (hE₀.add hE₁).supportWhiteningInv = M
  have hN : N.IsHermitian := hNdef ▸ (hE₀.add hE₁).supportWhitening_isHermitian
  have hM : M.IsHermitian := hMdef ▸ (hE₀.add hE₁).supportWhiteningInv_isHermitian
  have hE₀' : (N * E₀ * N).PosSemidef := posSemidef_mul_mul_of_isHermitian hE₀ hN
  have hE₁' : (N * E₁ * N).PosSemidef := posSemidef_mul_mul_of_isHermitian hE₁ hN
  have hD : (N * E₀ * N - N * E₁ * N).IsHermitian := hE₀'.isHermitian.sub hE₁'.isHermitian
  set P := nonnegSpectralProj (N * E₀ * N - N * E₁ * N)
  have hP : P.IsHermitian := nonnegSpectralProj_isHermitian hD
  have hpos : (P * (N * E₀ * N - N * E₁ * N) * P).PosSemidef :=
    nonnegSpectralProj_mul_mul_posSemidef hD
  have hEq :
      (N * P * M)ᴴ * (E₀ - E₁) * (N * P * M) =
        M * (P * (N * E₀ * N - N * E₁ * N) * P) * Mᴴ := by
    simp only [Matrix.conjTranspose_mul, hN.eq, hM.eq, hP.eq]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [hEq]
  exact hpos.mul_mul_conjTranspose_same M

/-- Sign-definiteness on the second sector: `(1 - R₀)ᴴ * (E₁ - E₀) * (1 - R₀) ≥ 0`. -/
theorem one_sub_twoFormSplitProj_conjTranspose_mul_sub_mul_posSemidef
    {E₀ E₁ : Matrix ι ι ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) :
    ((1 - twoFormSplitProj hE₀ hE₁)ᴴ * (E₁ - E₀) * (1 - twoFormSplitProj hE₀ hE₁)).PosSemidef := by
  rw [one_sub_twoFormSplitProj_eq hE₀ hE₁]
  generalize hNdef : (hE₀.add hE₁).supportWhitening = N
  generalize hMdef : (hE₀.add hE₁).supportWhiteningInv = M
  have hN : N.IsHermitian := hNdef ▸ (hE₀.add hE₁).supportWhitening_isHermitian
  have hM : M.IsHermitian := hMdef ▸ (hE₀.add hE₁).supportWhiteningInv_isHermitian
  have hE₀' : (N * E₀ * N).PosSemidef := posSemidef_mul_mul_of_isHermitian hE₀ hN
  have hE₁' : (N * E₁ * N).PosSemidef := posSemidef_mul_mul_of_isHermitian hE₁ hN
  have hD : (N * E₀ * N - N * E₁ * N).IsHermitian := hE₀'.isHermitian.sub hE₁'.isHermitian
  set P := nonnegSpectralProj (N * E₀ * N - N * E₁ * N)
  have hP : P.IsHermitian := nonnegSpectralProj_isHermitian hD
  have hpos : ((1 - P) * (N * E₁ * N - N * E₀ * N) * (1 - P)).PosSemidef := by
    simpa only [neg_sub] using one_sub_nonnegSpectralProj_mul_neg_mul_posSemidef hD
  have hEq :
      (N * (1 - P) * M)ᴴ * (E₁ - E₀) * (N * (1 - P) * M) =
        M * ((1 - P) * (N * E₁ * N - N * E₀ * N) * (1 - P)) * Mᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hN.eq, hM.eq, hP.eq]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [hEq]
  exact hpos.mul_mul_conjTranspose_same M

end TwoFormSplit

section BipartiteSplit

/-- Helper rewriting a bilinear form `star (L₁ *ᵥ u) ⬝ᵥ M *ᵥ (L₂ *ᵥ u)` as
`star u ⬝ᵥ (L₁ᴴ * M * L₂) *ᵥ u`. -/
private theorem star_mulVec_dotProduct_mulVec {n : Type*} [Fintype n]
    (L₁ M L₂ : Matrix n n ℂ) (u : n → ℂ) :
    star (L₁ *ᵥ u) ⬝ᵥ M *ᵥ (L₂ *ᵥ u) = star u ⬝ᵥ (L₁ᴴ * M * L₂) *ᵥ u := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

/-- Helper: left-linearity of Kronecker product with respect to subtraction. -/
private theorem sub_kronecker_eq {n m : Type*} (X Y : Matrix n n ℂ) (Z : Matrix m m ℂ) :
    (X - Y) ⊗ₖ Z = X ⊗ₖ Z - Y ⊗ₖ Z := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.kroneckerMap_apply, sub_mul]

section ExplicitVectors

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- First vector in the bipartite two-form decomposition of `u : A × B → ℂ`. -/
noncomputable def twoFormSplitLeft {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ) : A × B → ℂ :=
  (twoFormSplitProj hE₀ hE₁ ⊗ₖ (1 : Matrix B B ℂ)) *ᵥ u

/-- Second vector in the bipartite two-form decomposition of `u : A × B → ℂ`. -/
noncomputable def twoFormSplitRight {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ) : A × B → ℂ :=
  ((1 - twoFormSplitProj hE₀ hE₁) ⊗ₖ (1 : Matrix B B ℂ)) *ᵥ u

/-- The two split vectors sum to `u`. -/
theorem twoFormSplitLeft_add_twoFormSplitRight {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ) :
    twoFormSplitLeft hE₀ hE₁ u + twoFormSplitRight hE₀ hE₁ u = u := by
  rw [twoFormSplitLeft, twoFormSplitRight, ← Matrix.add_mulVec, ← Matrix.add_kronecker,
    add_sub_cancel, Matrix.one_kronecker_one, Matrix.one_mulVec]

/-- Cross-form vanishing `⟨w | (E₀ ⊗ F) | v⟩ = 0` for any matrix `F` on `B`. -/
theorem twoFormSplit_cross_right_left_zero {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ) (F : Matrix B B ℂ) :
    star (twoFormSplitRight hE₀ hE₁ u) ⬝ᵥ (E₀ ⊗ₖ F) *ᵥ (twoFormSplitLeft hE₀ hE₁ u) = 0 := by
  rw [twoFormSplitRight, twoFormSplitLeft, star_mulVec_dotProduct_mulVec,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one,
    one_sub_twoFormSplitProj_conjTranspose_mul_left_mul hE₀ hE₁,
    Matrix.zero_kronecker, Matrix.zero_mulVec, dotProduct_zero]

/-- Cross-form vanishing `⟨w | (E₁ ⊗ F) | v⟩ = 0` for any matrix `F` on `B`. -/
theorem twoFormSplit_cross_right_left_one {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ) (F : Matrix B B ℂ) :
    star (twoFormSplitRight hE₀ hE₁ u) ⬝ᵥ (E₁ ⊗ₖ F) *ᵥ (twoFormSplitLeft hE₀ hE₁ u) = 0 := by
  rw [twoFormSplitRight, twoFormSplitLeft, star_mulVec_dotProduct_mulVec,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one,
    one_sub_twoFormSplitProj_conjTranspose_mul_right_mul hE₀ hE₁,
    Matrix.zero_kronecker, Matrix.zero_mulVec, dotProduct_zero]

/-- Cross-form vanishing `⟨v | (E₀ ⊗ F) | w⟩ = 0` for any matrix `F` on `B`. -/
theorem twoFormSplit_cross_left_right_zero {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ) (F : Matrix B B ℂ) :
    star (twoFormSplitLeft hE₀ hE₁ u) ⬝ᵥ (E₀ ⊗ₖ F) *ᵥ (twoFormSplitRight hE₀ hE₁ u) = 0 := by
  rw [twoFormSplitLeft, twoFormSplitRight, star_mulVec_dotProduct_mulVec,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one,
    twoFormSplitProj_conjTranspose_mul_left_mul_one_sub hE₀ hE₁,
    Matrix.zero_kronecker, Matrix.zero_mulVec, dotProduct_zero]

/-- Cross-form vanishing `⟨v | (E₁ ⊗ F) | w⟩ = 0` for any matrix `F` on `B`. -/
theorem twoFormSplit_cross_left_right_one {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ) (F : Matrix B B ℂ) :
    star (twoFormSplitLeft hE₀ hE₁ u) ⬝ᵥ (E₁ ⊗ₖ F) *ᵥ (twoFormSplitRight hE₀ hE₁ u) = 0 := by
  rw [twoFormSplitLeft, twoFormSplitRight, star_mulVec_dotProduct_mulVec,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one,
    twoFormSplitProj_conjTranspose_mul_right_mul_one_sub hE₀ hE₁,
    Matrix.zero_kronecker, Matrix.zero_mulVec, dotProduct_zero]

/-- Quadratic-form additivity for `E₀ ⊗ F`:
`⟨u | (E₀ ⊗ F) | u⟩ = ⟨v | (E₀ ⊗ F) | v⟩ + ⟨w | (E₀ ⊗ F) | w⟩`. -/
theorem twoFormSplit_quad_zero_eq_add {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ) (F : Matrix B B ℂ) :
    star u ⬝ᵥ (E₀ ⊗ₖ F) *ᵥ u =
      star (twoFormSplitLeft hE₀ hE₁ u) ⬝ᵥ (E₀ ⊗ₖ F) *ᵥ (twoFormSplitLeft hE₀ hE₁ u) +
        star (twoFormSplitRight hE₀ hE₁ u) ⬝ᵥ (E₀ ⊗ₖ F) *ᵥ (twoFormSplitRight hE₀ hE₁ u) := by
  set v := twoFormSplitLeft hE₀ hE₁ u
  set w := twoFormSplitRight hE₀ hE₁ u
  have huv : v + w = u := twoFormSplitLeft_add_twoFormSplitRight hE₀ hE₁ u
  rw [← huv, star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    twoFormSplit_cross_left_right_zero hE₀ hE₁ u F,
    twoFormSplit_cross_right_left_zero hE₀ hE₁ u F, add_zero, zero_add]

/-- Quadratic-form additivity for `E₁ ⊗ F`:
`⟨u | (E₁ ⊗ F) | u⟩ = ⟨v | (E₁ ⊗ F) | v⟩ + ⟨w | (E₁ ⊗ F) | w⟩`. -/
theorem twoFormSplit_quad_one_eq_add {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ) (F : Matrix B B ℂ) :
    star u ⬝ᵥ (E₁ ⊗ₖ F) *ᵥ u =
      star (twoFormSplitLeft hE₀ hE₁ u) ⬝ᵥ (E₁ ⊗ₖ F) *ᵥ (twoFormSplitLeft hE₀ hE₁ u) +
        star (twoFormSplitRight hE₀ hE₁ u) ⬝ᵥ (E₁ ⊗ₖ F) *ᵥ (twoFormSplitRight hE₀ hE₁ u) := by
  set v := twoFormSplitLeft hE₀ hE₁ u
  set w := twoFormSplitRight hE₀ hE₁ u
  have huv : v + w = u := twoFormSplitLeft_add_twoFormSplitRight hE₀ hE₁ u
  rw [← huv, star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    twoFormSplit_cross_left_right_one hE₀ hE₁ u F,
    twoFormSplit_cross_right_left_one hE₀ hE₁ u F, add_zero, zero_add]

/-- Sign-definiteness `⟨v | ((E₀ - E₁) ⊗ F) | v⟩ ≥ 0` for any PSD `F` on `B`. -/
theorem twoFormSplit_left_diff_nonneg {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ)
    {F : Matrix B B ℂ} (hF : F.PosSemidef) :
    0 ≤ star (twoFormSplitLeft hE₀ hE₁ u) ⬝ᵥ ((E₀ - E₁) ⊗ₖ F) *ᵥ (twoFormSplitLeft hE₀ hE₁ u) := by
  rw [twoFormSplitLeft, star_mulVec_dotProduct_mulVec,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]
  exact ((twoFormSplitProj_conjTranspose_mul_sub_mul_posSemidef hE₀ hE₁).kronecker
    hF).dotProduct_mulVec_nonneg u

/-- Sign-definiteness `⟨w | ((E₁ - E₀) ⊗ F) | w⟩ ≥ 0` for any PSD `F` on `B`. -/
theorem twoFormSplit_right_diff_nonneg {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ)
    {F : Matrix B B ℂ} (hF : F.PosSemidef) :
    0 ≤ star (twoFormSplitRight hE₀ hE₁ u) ⬝ᵥ ((E₁ - E₀) ⊗ₖ F) *ᵥ
      (twoFormSplitRight hE₀ hE₁ u) := by
  rw [twoFormSplitRight, star_mulVec_dotProduct_mulVec,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]
  exact ((one_sub_twoFormSplitProj_conjTranspose_mul_sub_mul_posSemidef hE₀ hE₁).kronecker
    hF).dotProduct_mulVec_nonneg u

/-- Order comparison `⟨v | (E₁ ⊗ F) | v⟩ ≤ ⟨v | (E₀ ⊗ F) | v⟩` on the first sector. -/
theorem twoFormSplit_left_le {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ)
    {F : Matrix B B ℂ} (hF : F.PosSemidef) :
    star (twoFormSplitLeft hE₀ hE₁ u) ⬝ᵥ (E₁ ⊗ₖ F) *ᵥ (twoFormSplitLeft hE₀ hE₁ u) ≤
      star (twoFormSplitLeft hE₀ hE₁ u) ⬝ᵥ (E₀ ⊗ₖ F) *ᵥ (twoFormSplitLeft hE₀ hE₁ u) := by
  have h := twoFormSplit_left_diff_nonneg hE₀ hE₁ u hF
  rw [sub_kronecker_eq, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] at h
  exact h

/-- Order comparison `⟨w | (E₀ ⊗ F) | w⟩ ≤ ⟨w | (E₁ ⊗ F) | w⟩` on the second sector. -/
theorem twoFormSplit_right_le {E₀ E₁ : Matrix A A ℂ}
    (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef) (u : A × B → ℂ)
    {F : Matrix B B ℂ} (hF : F.PosSemidef) :
    star (twoFormSplitRight hE₀ hE₁ u) ⬝ᵥ (E₀ ⊗ₖ F) *ᵥ (twoFormSplitRight hE₀ hE₁ u) ≤
      star (twoFormSplitRight hE₀ hE₁ u) ⬝ᵥ (E₁ ⊗ₖ F) *ᵥ (twoFormSplitRight hE₀ hE₁ u) := by
  have h := twoFormSplit_right_diff_nonneg hE₀ hE₁ u hF
  rw [sub_kronecker_eq, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] at h
  exact h

end ExplicitVectors

/-- **Bipartite two-form splitting theorem.** Given two positive-semidefinite matrices
`E₀, E₁` on `A` (with no commutativity or invertibility assumption on `E₀ + E₁`), an
arbitrary vector `u : A × B → ℂ`, and an arbitrary family of positive-semidefinite matrices
`F : J → Matrix B B ℂ`, there exist `v, w : A × B → ℂ` with `v + w = u` such that for every `j`:

* `⟨w | (E₀ ⊗ F j) | v⟩ = 0` and `⟨w | (E₁ ⊗ F j) | v⟩ = 0`,
* `⟨v | (E₀ ⊗ F j) | w⟩ = 0` and `⟨v | (E₁ ⊗ F j) | w⟩ = 0`,
* `⟨v | ((E₀ - E₁) ⊗ F j) | v⟩ ≥ 0` and `⟨w | ((E₁ - E₀) ⊗ F j) | w⟩ ≥ 0`. -/
theorem exists_twoForms_bipartite_split {A B J : Type*} [Fintype A] [Fintype B]
    {E₀ E₁ : Matrix A A ℂ} (hE₀ : E₀.PosSemidef) (hE₁ : E₁.PosSemidef)
    (u : A × B → ℂ) (F : J → Matrix B B ℂ) (hF : ∀ j, (F j).PosSemidef) :
    ∃ v w : A × B → ℂ,
      v + w = u ∧
      (∀ j, star w ⬝ᵥ (E₀ ⊗ₖ F j) *ᵥ v = 0 ∧
            star w ⬝ᵥ (E₁ ⊗ₖ F j) *ᵥ v = 0 ∧
            star v ⬝ᵥ (E₀ ⊗ₖ F j) *ᵥ w = 0 ∧
            star v ⬝ᵥ (E₁ ⊗ₖ F j) *ᵥ w = 0) ∧
      (∀ j, 0 ≤ star v ⬝ᵥ ((E₀ - E₁) ⊗ₖ F j) *ᵥ v ∧
            0 ≤ star w ⬝ᵥ ((E₁ - E₀) ⊗ₖ F j) *ᵥ w) := by
  classical
  exact ⟨twoFormSplitLeft hE₀ hE₁ u, twoFormSplitRight hE₀ hE₁ u,
    twoFormSplitLeft_add_twoFormSplitRight hE₀ hE₁ u,
    fun j ↦ ⟨twoFormSplit_cross_right_left_zero hE₀ hE₁ u (F j),
      twoFormSplit_cross_right_left_one hE₀ hE₁ u (F j),
      twoFormSplit_cross_left_right_zero hE₀ hE₁ u (F j),
      twoFormSplit_cross_left_right_one hE₀ hE₁ u (F j)⟩,
    fun j ↦ ⟨twoFormSplit_left_diff_nonneg hE₀ hE₁ u (hF j),
      twoFormSplit_right_diff_nonneg hE₀ hE₁ u (hF j)⟩⟩

end BipartiteSplit

end Matrix
