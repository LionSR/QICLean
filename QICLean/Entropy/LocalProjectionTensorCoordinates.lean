/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RegionUnion
import QICLean.Algebra.ProjectionTensorCoordinates

/-!
# Consistent range coordinates on disjoint physical regions

The parent range is expressed in fixed child coordinates. The coordinates are
chosen once, rather than chosen independently for each occurrence of a child.
All containments are identities between the actual lifted projections.
This is auxiliary to Hastings, arXiv:cond-mat/0508554v3, Section III,
lines 630–685. Empty retained ranges and empty physical regions are allowed.
-/

open Matrix
open scoped Kronecker

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- Fixed local range coordinates descend through a contained lifted range.
Auxiliary to Hastings, arXiv:cond-mat/0508554v3, Section III, lines 630–685. -/
theorem localLift_range_coordinates {D : Finset V}
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    {U : Matrix (RegionConfig n D) α ℂ} (hU : U.IsIsometry)
    (A : Matrix (RegionConfig n D) β ℂ) (σ₀ : SiteConfig n)
    (hcontain : localLift D (A * Aᴴ) * localLift D (U * Uᴴ) =
      localLift D (U * Uᴴ)) :
    (Aᴴ * U).IsIsometry ∧ U = A * (Aᴴ * U) := by
  classical
  have hlocal : A * Aᴴ * (U * Uᴴ) = U * Uᴴ :=
    localLift_injective D σ₀ ((localLift_mul _ _).trans hcontain)
  apply hU.conjTranspose_mul_of_range_eq A
  simpa only [Matrix.mul_assoc, (show Uᴴ * U = 1 from hU), Matrix.mul_one] using
    congrArg (fun X ↦ X * U) hlocal

/-- The range product of two local column families lifts to the product of their
separate range operators. Auxiliary to Hastings, arXiv:cond-mat/0508554v3,
Section III, lines 630–685. -/
theorem localLift_tensor_columns {X Y : Finset V} (hXY : Disjoint X Y)
    {a b : ℕ} (U : Matrix (RegionConfig n X) (Fin a) ℂ)
    (W : Matrix (RegionConfig n Y) (Fin b) ℂ) :
    let A := reindex (regionUnionEquiv hXY).symm (Equiv.refl (Fin a × Fin b)) (U ⊗ₖ W)
    localLift (X ∪ Y) (A * Aᴴ) = localLift X (U * Uᴴ) * localLift Y (W * Wᴴ) := by
  classical
  change localLift (X ∪ Y)
    (reindexLinearEquiv ℂ ℂ (regionUnionEquiv hXY).symm (Equiv.refl _) (U ⊗ₖ W) *
      reindexLinearEquiv ℂ ℂ (Equiv.refl _) (regionUnionEquiv hXY).symm (U ⊗ₖ W)ᴴ) = _
  rw [reindexLinearEquiv_mul]
  simpa only [coe_reindexLinearEquiv, conjTranspose_kronecker, ← mul_kronecker_mul] using
    localLift_union_kronecker hXY (U * Uᴴ) (W * Wᴴ)

/-- A parent range has actual isometric coefficients in fixed child coordinates.
The last identity is its expansion on physical configurations. Auxiliary to
Hastings, arXiv:cond-mat/0508554v3, Section III, lines 630–685. -/
theorem localLift_tensor_range_coordinates {X Y : Finset V} (hXY : Disjoint X Y)
    {a b c : ℕ} {U : Matrix (RegionConfig n (X ∪ Y)) (Fin a) ℂ}
    (hU : U.IsIsometry) (V₁ : Matrix (RegionConfig n X) (Fin b) ℂ)
    (V₂ : Matrix (RegionConfig n Y) (Fin c) ℂ) (σ₀ : SiteConfig n)
    (hcontain : localLift X (V₁ * V₁ᴴ) * localLift Y (V₂ * V₂ᴴ) *
      localLift (X ∪ Y) (U * Uᴴ) = localLift (X ∪ Y) (U * Uᴴ)) :
    let A := reindex (regionUnionEquiv hXY).symm (Equiv.refl (Fin b × Fin c)) (V₁ ⊗ₖ V₂)
    (Aᴴ * U).IsIsometry ∧ U = A * (Aᴴ * U) ∧ a ≤ b * c ∧
      ∀ (σ : SiteConfig n) (j : Fin a),
        U (fun v ↦ σ v) j = ∑ k : Fin b × Fin c,
          V₁ (fun v ↦ σ v) k.1 * V₂ (fun v ↦ σ v) k.2 * (Aᴴ * U) k j := by
  classical
  let A := reindex (regionUnionEquiv hXY).symm (Equiv.refl (Fin b × Fin c)) (V₁ ⊗ₖ V₂)
  have hcoords := localLift_range_coordinates hU A σ₀
    ((congrArg (fun T ↦ T * localLift (X ∪ Y) (U * Uᴴ))
      (localLift_tensor_columns hXY V₁ V₂)).trans hcontain)
  refine ⟨hcoords.1, hcoords.2, ?_, ?_⟩
  case refine_2 =>
    intro σ j
    simpa only [Matrix.mul_apply, A, reindex_apply, submatrix_apply,
      Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, kroneckerMap_apply,
      regionUnionEquiv, Equiv.coe_fn_mk, id_eq] using
      congrFun (congrFun hcoords.2 (fun v ↦ σ v)) j
  case refine_1 =>
    simpa only [Fintype.card_fin, Fintype.card_prod] using
      Matrix.IsIsometry.card_le (Aᴴ * U) hcoords.1

end Entropy
