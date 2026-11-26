/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Complex.Basic

/-!
# Entrywise conjugation of matrices

Entrywise complex conjugation `σ X = X.map (starRingEnd ℂ)` is an anti-linear
involution of the space of complex matrices. Conjugating a matrix endomorphism `Φ` by `σ`
produces the linear endomorphism `σ ∘ Φ ∘ σ`; on the endomorphism ring this transport is a
ring automorphism that conjugates the scalars.

## Main definitions

- `entrywiseConjTransport`: the transport `Φ ↦ σ ∘ Φ ∘ σ` of a matrix endomorphism
  along entrywise conjugation `σ`
- `entrywiseConjTransportRingEquiv`: the same transport as a ring automorphism of the
  endomorphism ring

## Main results

- `Matrix.map_starRingEnd_map_starRingEnd`: entrywise conjugation is an involution
- `Matrix.map_smul_starRingEnd`: entrywise conjugation conjugates scalars
- `entrywiseConjTransport_mul`, `entrywiseConjTransport_algebraMap`: the transport is
  multiplicative and sends the scalar `μ` to `conj μ`
-/

variable {D : ℕ}

namespace Matrix

/-- Entrywise conjugation of a matrix is an involution. -/
@[simp] theorem map_starRingEnd_map_starRingEnd {m n : Type*} (X : Matrix m n ℂ) :
    (X.map (starRingEnd ℂ)).map (starRingEnd ℂ) = X := by
  ext i j
  simp [Matrix.map_apply]

/-- Entrywise conjugation of a matrix is an involution, composed-function form. -/
@[simp] theorem map_starRingEnd_comp_starRingEnd {m n : Type*} (X : Matrix m n ℂ) :
    X.map (⇑(starRingEnd ℂ) ∘ ⇑(starRingEnd ℂ)) = X := by
  ext i j
  simp [Matrix.map_apply]

/-- Entrywise conjugation is anti-linear: it conjugates scalars. -/
theorem map_smul_starRingEnd {m n : Type*} (c : ℂ) (X : Matrix m n ℂ) :
    (c • X).map (starRingEnd ℂ) = star c • X.map (starRingEnd ℂ) := by
  ext i j
  simp [Matrix.map_apply]

end Matrix

/-- Transport of a matrix endomorphism along entrywise complex conjugation:
`Φ ↦ σ ∘ Φ ∘ σ`, where `σ X = X.map (starRingEnd ℂ)` is the anti-linear
involution given by entrywise conjugation. Both anti-linear factors conjugate
the scalars, so the composite is again linear.

This is the anti-linear conjugacy through which entrywise conjugation of a
tensor acts on its transfer map (arXiv:1606.00608, lines 219--225). -/
noncomputable def entrywiseConjTransport
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun X := (Φ (X.map (starRingEnd ℂ))).map (starRingEnd ℂ)
  map_add' X Y := by
    rw [Matrix.map_add (starRingEnd ℂ) (map_add (starRingEnd ℂ)) X Y, map_add,
      Matrix.map_add (starRingEnd ℂ) (map_add (starRingEnd ℂ))]
  map_smul' c X := by
    rw [Matrix.map_smul_starRingEnd, map_smul, Matrix.map_smul_starRingEnd, star_star]
    rfl

@[simp] theorem entrywiseConjTransport_apply
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    entrywiseConjTransport Φ X = (Φ (X.map (starRingEnd ℂ))).map (starRingEnd ℂ) := rfl

/-- Transport along entrywise conjugation is an involution on endomorphisms. -/
@[simp] theorem entrywiseConjTransport_entrywiseConjTransport
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    entrywiseConjTransport (entrywiseConjTransport Φ) = Φ := by
  apply LinearMap.ext
  intro X
  simp

/-- Transport along entrywise conjugation is multiplicative for composition. -/
theorem entrywiseConjTransport_mul
    (Φ Ψ : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) :
    entrywiseConjTransport (Φ * Ψ) =
      entrywiseConjTransport Φ * entrywiseConjTransport Ψ := by
  apply LinearMap.ext
  intro X
  simp [Module.End.mul_apply]

/-- Transport along entrywise conjugation sends the scalar `μ` to `conj μ`. -/
theorem entrywiseConjTransport_algebraMap (μ : ℂ) :
    entrywiseConjTransport
        (algebraMap ℂ (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) μ) =
      algebraMap ℂ (Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (star μ) := by
  apply LinearMap.ext
  intro X
  rw [entrywiseConjTransport_apply, Module.algebraMap_end_apply,
    Module.algebraMap_end_apply, Matrix.map_smul_starRingEnd,
    Matrix.map_starRingEnd_map_starRingEnd]

/-- Transport along entrywise conjugation as a ring automorphism of the
endomorphism ring of the matrix space. On scalars it acts by complex
conjugation (`entrywiseConjTransport_algebraMap`), so it is a ring
automorphism but not an algebra automorphism. -/
noncomputable def entrywiseConjTransportRingEquiv (D : ℕ) :
    Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) ≃+*
      Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) where
  toFun := entrywiseConjTransport
  invFun := entrywiseConjTransport
  left_inv := entrywiseConjTransport_entrywiseConjTransport
  right_inv := entrywiseConjTransport_entrywiseConjTransport
  map_mul' := entrywiseConjTransport_mul
  map_add' Φ Ψ := by
    apply LinearMap.ext
    intro X
    simp [Matrix.map_add (starRingEnd ℂ) (map_add (starRingEnd ℂ))]

