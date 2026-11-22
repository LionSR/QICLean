/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Isometry.UnitaryMulVecInner

/-!
# Stability of expectations and connected correlations

For a vector `ψ` of a finite-dimensional coordinate space and a matrix `A`, the expectation
`⟨ψ|A|ψ⟩` is written `star ψ ⬝ᵥ (A *ᵥ ψ)`. The expectation of a unitary in a unit vector has
modulus at most one. Changing the unit vector by distance `η` changes the expectation by at
most `2η` and a connected two-point correlation `⟨AB⟩ - ⟨A⟩⟨B⟩` by at most `6η`. A unit scalar
does not change expectations, and a superposition of two basis vectors has no cross terms when
both matrix elements between them vanish. The estimates use the Euclidean distance between
vectors.

Moved from TNLean, `TNLean/Circuit/ExpectationBounds.lean` and (the last lemma)
`TNLean/Circuit/SupportedMatrixElements.lean` at commit `49b78ed821` (Apache-2.0).
Changes: any finite index type in place of the configurations of a system of qudits; the
expectation `QuantumCircuit.expect ψ A` is written out as `star ψ ⬝ᵥ (A *ᵥ ψ)`, and the
lemmas are renamed accordingly.

## Main results

* `Matrix.star_dotProduct_mulVec_eq_inner` — the expectation as a Euclidean inner product.
* `Matrix.norm_star_dotProduct_mulVec_le_one`, `Matrix.norm_star_dotProduct_mulVec_sub_le`.
* `Matrix.norm_covariance_sub_le` — connected correlations of unitaries are `6`-Lipschitz on
  unit vectors.
-/

open scoped InnerProductSpace

namespace Matrix

variable {n : Type*} [Fintype n]

/-- The coordinate expectation is the Euclidean inner product with the operator image. -/
theorem star_dotProduct_mulVec_eq_inner (ψ : n → ℂ) (A : Matrix n n ℂ) :
    star ψ ⬝ᵥ (A *ᵥ ψ) =
      ⟪(WithLp.toLp 2 ψ : EuclideanSpace ℂ n), WithLp.toLp 2 (A *ᵥ ψ)⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

variable [DecidableEq n]

/-- The expectation of a unitary in a unit vector has modulus at most one. -/
theorem norm_star_dotProduct_mulVec_le_one {ψ : n → ℂ}
    (hψ : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ n)‖ = 1) {A : Matrix n n ℂ}
    (hA : A ∈ unitary (Matrix n n ℂ)) : ‖star ψ ⬝ᵥ (A *ᵥ ψ)‖ ≤ 1 := by
  rw [star_dotProduct_mulVec_eq_inner]
  have hAψ : ‖(WithLp.toLp 2 (A *ᵥ ψ) : EuclideanSpace ℂ n)‖ = 1 :=
    (norm_eq_of_mulVec_eq hA rfl).trans hψ
  simpa [hψ, hAψ] using norm_inner_le_norm
    (WithLp.toLp 2 ψ : EuclideanSpace ℂ n) (WithLp.toLp 2 (A *ᵥ ψ))

/-- Expectations of a unitary differ by at most twice the distance between unit vectors. -/
theorem norm_star_dotProduct_mulVec_sub_le {ψ φ : n → ℂ}
    (hψ : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ n)‖ = 1)
    (hφ : ‖(WithLp.toLp 2 φ : EuclideanSpace ℂ n)‖ = 1)
    {A : Matrix n n ℂ} (hA : A ∈ unitary (Matrix n n ℂ)) :
    ‖star ψ ⬝ᵥ (A *ᵥ ψ) - star φ ⬝ᵥ (A *ᵥ φ)‖ ≤
      2 * ‖(WithLp.toLp 2 ψ - WithLp.toLp 2 φ : EuclideanSpace ℂ n)‖ := by
  let x : EuclideanSpace ℂ n := WithLp.toLp 2 ψ
  let y : EuclideanSpace ℂ n := WithLp.toLp 2 φ
  let Ax : EuclideanSpace ℂ n := WithLp.toLp 2 (A *ᵥ ψ)
  let Ay : EuclideanSpace ℂ n := WithLp.toLp 2 (A *ᵥ φ)
  have hAx : ‖Ax‖ = 1 := (norm_eq_of_mulVec_eq hA rfl).trans hψ
  have hdiff : ‖Ax - Ay‖ = ‖x - y‖ :=
    norm_eq_of_mulVec_eq hA (by
      change (A *ᵥ ψ) - (A *ᵥ φ) = A *ᵥ (ψ - φ)
      exact (mulVec_sub A ψ φ).symm)
  have heq : star ψ ⬝ᵥ (A *ᵥ ψ) - star φ ⬝ᵥ (A *ᵥ φ) = ⟪x - y, Ax⟫_ℂ + ⟪y, Ax - Ay⟫_ℂ := by
    rw [star_dotProduct_mulVec_eq_inner, star_dotProduct_mulVec_eq_inner, inner_sub_left,
      inner_sub_right]
    change ⟪x, Ax⟫_ℂ - ⟪y, Ay⟫_ℂ = _
    ring
  rw [heq]
  calc
    _ ≤ ‖⟪x - y, Ax⟫_ℂ‖ + ‖⟪y, Ax - Ay⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖Ax‖ + ‖y‖ * ‖Ax - Ay‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = 2 * ‖x - y‖ := by rw [hAx, hdiff, hφ]; ring

omit [DecidableEq n] in
/-- Multiplying a vector by a scalar of modulus one preserves every expectation. -/
theorem star_smul_dotProduct_mulVec_smul {c : ℂ} (hc : ‖c‖ = 1) (ψ : n → ℂ)
    (A : Matrix n n ℂ) : star (c • ψ) ⬝ᵥ (A *ᵥ (c • ψ)) = star ψ ⬝ᵥ (A *ᵥ ψ) := by
  have hc' : star c * c = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, hc]
    norm_num
  simp only [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [← mul_assoc, mul_comm c (star c), hc', one_mul]

/-- **Stability of connected correlations.** Connected two-point correlations
`⟨AB⟩ - ⟨A⟩⟨B⟩` of unitaries are Lipschitz on unit vectors, with constant `6`. -/
theorem norm_covariance_sub_le {ψ φ : n → ℂ}
    (hψ : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ n)‖ = 1)
    (hφ : ‖(WithLp.toLp 2 φ : EuclideanSpace ℂ n)‖ = 1)
    {A B : Matrix n n ℂ} (hA : A ∈ unitary (Matrix n n ℂ)) (hB : B ∈ unitary (Matrix n n ℂ)) :
    ‖(star ψ ⬝ᵥ ((A * B) *ᵥ ψ) - star ψ ⬝ᵥ (A *ᵥ ψ) * star ψ ⬝ᵥ (B *ᵥ ψ)) -
      (star φ ⬝ᵥ ((A * B) *ᵥ φ) - star φ ⬝ᵥ (A *ᵥ φ) * star φ ⬝ᵥ (B *ᵥ φ))‖ ≤
      6 * ‖(WithLp.toLp 2 ψ - WithLp.toLp 2 φ : EuclideanSpace ℂ n)‖ := by
  set η := ‖(WithLp.toLp 2 ψ - WithLp.toLp 2 φ : EuclideanSpace ℂ n)‖
  set eψ : Matrix n n ℂ → ℂ := fun M ↦ star ψ ⬝ᵥ (M *ᵥ ψ) with heψ
  set eφ : Matrix n n ℂ → ℂ := fun M ↦ star φ ⬝ᵥ (M *ᵥ φ) with heφ
  have hAB : ‖eψ (A * B) - eφ (A * B)‖ ≤ 2 * η :=
    norm_star_dotProduct_mulVec_sub_le hψ hφ (Submonoid.mul_mem (unitary _) hA hB)
  have hAd : ‖eψ A - eφ A‖ ≤ 2 * η := norm_star_dotProduct_mulVec_sub_le hψ hφ hA
  have hBd : ‖eψ B - eφ B‖ ≤ 2 * η := norm_star_dotProduct_mulVec_sub_le hψ hφ hB
  have hAφ : ‖eφ A‖ ≤ 1 := norm_star_dotProduct_mulVec_le_one hφ hA
  have hBψ : ‖eψ B‖ ≤ 1 := norm_star_dotProduct_mulVec_le_one hψ hB
  change ‖(eψ (A * B) - eψ A * eψ B) - (eφ (A * B) - eφ A * eφ B)‖ ≤ 6 * η
  have heq : (eψ (A * B) - eψ A * eψ B) - (eφ (A * B) - eφ A * eφ B) =
      (eψ (A * B) - eφ (A * B)) - ((eψ A - eφ A) * eψ B + eφ A * (eψ B - eφ B)) := by ring
  rw [heq]
  calc
    _ ≤ ‖eψ (A * B) - eφ (A * B)‖ +
        (‖eψ A - eφ A‖ * ‖eψ B‖ + ‖eφ A‖ * ‖eψ B - eφ B‖) := by
      refine (norm_sub_le _ _).trans (add_le_add_right ?_ _)
      simpa only [norm_mul] using norm_add_le ((eψ A - eφ A) * eψ B) (eφ A * (eψ B - eφ B))
    _ ≤ 2 * η + (2 * η * 1 + 1 * (2 * η)) :=
      add_le_add hAB (add_le_add
        (mul_le_mul hAd hBψ (norm_nonneg _) (by positivity))
        (mul_le_mul hAφ hBd (norm_nonneg _) (by norm_num)))
    _ = 6 * η := by ring

omit [Fintype n] in
/-- A superposition of two basis vectors has no cross terms in the expectation of `A` when both
matrix elements of `A` between them vanish. -/
theorem star_dotProduct_mulVec_smul_single_add_of_apply_eq_zero [Fintype n] (a b : ℂ)
    {σ τ : n} {A : Matrix n n ℂ} (hστ : A σ τ = 0) (hτσ : A τ σ = 0) :
    star (a • Pi.single σ 1 + b • Pi.single τ 1) ⬝ᵥ
        (A *ᵥ (a • Pi.single σ 1 + b • Pi.single τ 1)) =
      star a * a * A σ σ + star b * b * A τ τ := by
  simp [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, hστ, hτσ]
  ring

end Matrix
