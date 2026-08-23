/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausRank
import QICLean.Channel.LorentzNormalForm.Basic
import QICLean.Channel.SingleKraus
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Invertible Kraus-rank-one filtering operations

Wolf Section 2.4 studies completely positive maps up to pre- and
postcomposition by invertible maps of Kraus rank one.  Such a *filtering
operation* has the form

`Phi_X(A) = X * A * X^H`, with `X` invertible.

This module records these general filters using `GL (Fin D) C`.  It also
separates each filtering matrix into a nonzero complex scalar and a
determinant-one matrix.  The complex scalar itself need not be real or
positive; only its contribution `Complex.normSq c` to the induced completely
positive map is a positive real number.

## Main declarations

* `Wolf.InvertibleFilter` -- an invertible single-Kraus filter.
* `Wolf.InvertibleFilter.comp` and `Wolf.InvertibleFilter.inv` -- composition
  and inverse filterings, with the same order as composition of their maps.
* `Wolf.InvertibleFilter.choiRank_eq_one` -- the Kraus rank is exactly one in
  nonzero dimension.
* `Wolf.InvertibleFilter.exists_scalar_slFiltering` -- decomposition into a
  nonzero complex scalar and an existing `Wolf.SLFiltering`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 2.4,
  Equation (2.35) and Proposition 2.11][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder

namespace Wolf

/-- An invertible Kraus-rank-one filtering operation on `D x D` matrices.
The filtering matrix is bundled as an element of `GL (Fin D) C`; its map is
defined separately below. -/
structure InvertibleFilter (D : ℕ) where
  /-- The invertible filtering matrix `X`. -/
  X : GL (Fin D) ℂ

namespace InvertibleFilter

/-- The filtering operation `Phi_X(A) = X A X^H`. -/
noncomputable def map {D : ℕ} (Phi : InvertibleFilter D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  singleKrausMap (Phi.X : Matrix (Fin D) (Fin D) ℂ)

@[simp]
theorem map_apply {D : ℕ} (Phi : InvertibleFilter D)
    (A : Matrix (Fin D) (Fin D) ℂ) :
    Phi.map A = (Phi.X : Matrix (Fin D) (Fin D) ℂ) * A *
      (Phi.X : Matrix (Fin D) (Fin D) ℂ)ᴴ :=
  rfl

/-- The general filtering map agrees with the conjugation map used by the
existing determinant-one filtering API. -/
theorem map_eq_unitaryConjLM {D : ℕ} (Phi : InvertibleFilter D) :
    Phi.map = unitaryConjLM (Phi.X : Matrix (Fin D) (Fin D) ℂ) := by
  ext A
  rfl

/-- Every invertible filtering operation is completely positive. -/
theorem cp {D : ℕ} (Phi : InvertibleFilter D) : IsCPMap Phi.map := by
  exact isKrausCP_iff_isCPMap.mp
    (singleKrausMap_isKrausCP (Phi.X : Matrix (Fin D) (Fin D) ℂ))

/-- The identity filtering operation. -/
def id (D : ℕ) : InvertibleFilter D where
  X := 1

@[simp]
theorem map_id (D : ℕ) : (id D).map = LinearMap.id := by
  apply LinearMap.ext
  intro A
  simp [map_apply, id]

/-- Composition of filtering operations.  The order matches map
composition: `(Phi.comp Psi).map = Phi.map.comp Psi.map`. -/
def comp {D : ℕ} (Phi Psi : InvertibleFilter D) : InvertibleFilter D where
  X := Phi.X * Psi.X

@[simp]
theorem comp_X {D : ℕ} (Phi Psi : InvertibleFilter D) :
    (Phi.comp Psi).X = Phi.X * Psi.X :=
  rfl

/-- Matrix multiplication gives the source composition order for filtering
operations. -/
theorem map_comp {D : ℕ} (Phi Psi : InvertibleFilter D) :
    (Phi.comp Psi).map = Phi.map.comp Psi.map := by
  exact (singleKrausMap_comp
    (Phi.X : Matrix (Fin D) (Fin D) ℂ)
    (Psi.X : Matrix (Fin D) (Fin D) ℂ)).symm

/-- The inverse filtering operation, represented by `X^{-1}`. -/
def inv {D : ℕ} (Phi : InvertibleFilter D) : InvertibleFilter D where
  X := Phi.X⁻¹

@[simp]
theorem inv_X {D : ℕ} (Phi : InvertibleFilter D) : Phi.inv.X = Phi.X⁻¹ :=
  rfl

@[simp]
theorem inv_comp {D : ℕ} (Phi : InvertibleFilter D) : Phi.inv.comp Phi = id D := by
  cases Phi with
  | mk X =>
    change InvertibleFilter.mk (X⁻¹ * X) = InvertibleFilter.mk 1
    rw [inv_mul_cancel X]

@[simp]
theorem comp_inv {D : ℕ} (Phi : InvertibleFilter D) : Phi.comp Phi.inv = id D := by
  cases Phi with
  | mk X =>
    change InvertibleFilter.mk (X * X⁻¹) = InvertibleFilter.mk 1
    rw [mul_inv_cancel X]

/-- The inverse filtering map is a left inverse. -/
theorem inv_map_comp {D : ℕ} (Phi : InvertibleFilter D) :
    Phi.inv.map.comp Phi.map = LinearMap.id := by
  rw [← map_comp Phi.inv Phi, inv_comp, map_id]

/-- The inverse filtering map is a right inverse. -/
theorem map_comp_inv {D : ℕ} (Phi : InvertibleFilter D) :
    Phi.map.comp Phi.inv.map = LinearMap.id := by
  rw [← map_comp Phi Phi.inv, comp_inv, map_id]

/-- The displayed filtering matrix is a one-operator Kraus representation. -/
theorem hasKrausCard_one {D : ℕ} (Phi : InvertibleFilter D) :
    Channel.HasKrausCard Phi.map 1 := by
  refine ⟨fun _ ↦ (Phi.X : Matrix (Fin D) (Fin D) ℂ), ?_⟩
  intro A
  simp [map_apply]

/-- In nonzero dimension an invertible filtering operation is not the zero
linear map. -/
theorem map_ne_zero {D : ℕ} [NeZero D] (Phi : InvertibleFilter D) :
    Phi.map ≠ 0 := by
  intro hzero
  have hcomp := Phi.inv_map_comp
  rw [hzero] at hcomp
  simp only [LinearMap.comp_zero] at hcomp
  have hone := LinearMap.congr_fun hcomp (1 : Matrix (Fin D) (Fin D) ℂ)
  simp only [LinearMap.zero_apply, LinearMap.id_apply] at hone
  exact one_ne_zero hone.symm

/-- In nonzero dimension an invertible single-Kraus filtering operation has
Kraus rank (equivalently, Choi rank) exactly one. -/
theorem choiRank_eq_one {D : ℕ} [NeZero D] (Phi : InvertibleFilter D) :
    Channel.choiRank Phi.map = 1 := by
  have hle : Channel.choiRank Phi.map ≤ 1 :=
    Channel.choiRank_le_of_hasKrausCard Phi.hasKrausCard_one
  have hne : Channel.choiRank Phi.map ≠ 0 := by
    intro hzero
    have hcard := Channel.hasKrausCard_choiRank_of_cp
      (isKrausCP_iff_isCPMap.mpr Phi.cp)
    rw [hzero] at hcard
    rcases hcard with ⟨K, hK⟩
    have heqzero : Phi.map = 0 := by
      ext A
      simp [hK A]
    exact Phi.map_ne_zero heqzero
  omega

/-- Scaling a single Kraus matrix by `c` scales its completely positive map
by the nonnegative real number `Complex.normSq c = |c|^2`. -/
theorem singleKrausMap_smul {D : ℕ} (c : ℂ)
    (S : Matrix (Fin D) (Fin D) ℂ) :
    singleKrausMap (c • S) =
      ((Complex.normSq c : ℝ) : ℂ) • singleKrausMap S := by
  apply LinearMap.ext
  intro A
  simp only [singleKrausMap_apply, LinearMap.smul_apply, Matrix.conjTranspose_smul]
  simp [smul_smul, Complex.normSq_eq_conj_mul_self, mul_comm]

/-! ### Pre- and postfiltering in Wolf's order -/

/-- Pre- and postfilter a possibly rectangular map in the order of Wolf
Equation (2.35): `Phi₂ ∘ T ∘ Phi₁`. -/
noncomputable def filteredMap {d₁ d₂ : ℕ}
    (Phi₂ : InvertibleFilter d₂)
    (T : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ)
    (Phi₁ : InvertibleFilter d₁) :
    Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ :=
  Phi₂.map.comp (T.comp Phi₁.map)

@[simp]
theorem filteredMap_apply {d₁ d₂ : ℕ}
    (Phi₂ : InvertibleFilter d₂)
    (T : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ)
    (Phi₁ : InvertibleFilter d₁) (A : Matrix (Fin d₁) (Fin d₁) ℂ) :
    filteredMap Phi₂ T Phi₁ A =
      (Phi₂.X : Matrix (Fin d₂) (Fin d₂) ℂ) *
        T ((Phi₁.X : Matrix (Fin d₁) (Fin d₁) ℂ) * A *
          (Phi₁.X : Matrix (Fin d₁) (Fin d₁) ℂ)ᴴ) *
        (Phi₂.X : Matrix (Fin d₂) (Fin d₂) ℂ)ᴴ :=
  rfl

/-- The two scalar factors in `Phi₂ ∘ T ∘ Phi₁` combine to the positive
map scalar `Complex.normSq (c₁ * c₂)`.  This is the rectangular-map identity
used in the scalar-normalization discussion following Wolf Equation (2.35). -/
theorem filteredMap_eq_normSq_smul {d₁ d₂ : ℕ}
    (Phi₂ : InvertibleFilter d₂)
    (T : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ)
    (Phi₁ : InvertibleFilter d₁)
    (c₁ c₂ : ℂ) (Psi₁ : SLFiltering d₁) (Psi₂ : SLFiltering d₂)
    (h₁ : Phi₁.map = ((Complex.normSq c₁ : ℝ) : ℂ) • Psi₁.map)
    (h₂ : Phi₂.map = ((Complex.normSq c₂ : ℝ) : ℂ) • Psi₂.map) :
    filteredMap Phi₂ T Phi₁ =
      ((Complex.normSq (c₁ * c₂) : ℝ) : ℂ) •
        (Psi₂.map.comp (T.comp Psi₁.map)) := by
  ext A
  simp only [filteredMap, LinearMap.comp_apply, LinearMap.smul_apply]
  rw [h₁, h₂]
  simp only [LinearMap.smul_apply, map_smul]
  rw [smul_smul, Complex.normSq_mul]
  norm_cast

/-- Every invertible filtering matrix in nonzero dimension is a nonzero
complex scalar multiple of a determinant-one filtering matrix.  At map level
the corresponding scalar is the positive real number `Complex.normSq c`.

This is the scalar freedom required by Wolf Proposition 2.11; it is not a
claim that the matrix scalar `c` itself is positive real. -/
theorem exists_scalar_slFiltering {D : ℕ} [NeZero D]
    (Phi : InvertibleFilter D) :
    ∃ (c : ℂ), c ≠ 0 ∧
      c ^ D = (Phi.X : Matrix (Fin D) (Fin D) ℂ).det ∧
      0 < Complex.normSq c ∧
      ∃ Psi : SLFiltering D,
        (Phi.X : Matrix (Fin D) (Fin D) ℂ) = c • Psi.S ∧
          Phi.map = ((Complex.normSq c : ℝ) : ℂ) • Psi.map := by
  obtain ⟨c, hcD⟩ := IsAlgClosed.exists_pow_nat_eq
    (Phi.X : Matrix (Fin D) (Fin D) ℂ).det (NeZero.pos D)
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_pow (NeZero.ne D)] at hcD
    exact Phi.X.det_ne_zero hcD.symm
  let S : Matrix (Fin D) (Fin D) ℂ := c⁻¹ • (Phi.X : Matrix (Fin D) (Fin D) ℂ)
  have hSdet : S.det = 1 := by
    dsimp only [S]
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hcD]
    exact inv_mul_cancel₀ Phi.X.det_ne_zero
  let Psi : SLFiltering D :=
    { S := S
      det_eq_one := hSdet
      map := unitaryConjLM S
      map_eq := rfl
      cp := unitaryConjLM_isCPMap S }
  have hX : (Phi.X : Matrix (Fin D) (Fin D) ℂ) = c • S := by
    dsimp only [S]
    rw [smul_smul, mul_inv_cancel₀ hc]
    exact (one_smul ℂ (Phi.X : Matrix (Fin D) (Fin D) ℂ)).symm
  have hmap : Phi.map = ((Complex.normSq c : ℝ) : ℂ) • Psi.map := by
    rw [show Phi.map = singleKrausMap (Phi.X : Matrix (Fin D) (Fin D) ℂ) from rfl,
      hX, singleKrausMap_smul]
    congr 1
  refine ⟨c, hc, hcD, Complex.normSq_pos.mpr hc, Psi, ?_, hmap⟩
  exact hX

end InvertibleFilter

namespace SLFiltering

/-- Regard an existing determinant-one filtering as a general invertible
filtering operation.  This preserves the established `SLFiltering` API as the
determinant-one specialization. -/
noncomputable def toInvertibleFilter {D : ℕ} (Phi : SLFiltering D) :
    InvertibleFilter D where
  X := Matrix.GeneralLinearGroup.mkOfDetNeZero Phi.S (by
    rw [Phi.det_eq_one]
    exact one_ne_zero)

@[simp]
theorem toInvertibleFilter_X {D : ℕ} (Phi : SLFiltering D) :
    (Phi.toInvertibleFilter.X : Matrix (Fin D) (Fin D) ℂ) = Phi.S :=
  rfl

/-- Passing an `SLFiltering` to the general filter type does not change its
associated completely positive map. -/
theorem toInvertibleFilter_map {D : ℕ} (Phi : SLFiltering D) :
    Phi.toInvertibleFilter.map = Phi.map := by
  rw [Phi.map_eq, Phi.toInvertibleFilter.map_eq_unitaryConjLM,
    toInvertibleFilter_X]

end SLFiltering

end Wolf
