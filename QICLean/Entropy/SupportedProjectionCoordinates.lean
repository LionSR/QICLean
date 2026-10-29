/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.LocalLift
import QICLean.Algebra.ProjectionRangeIsometry
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Local coordinates for a supported orthogonal projection

A projection supported on a region is the lift of an actual local projection.
The identity on the exterior is removed before choosing its range coordinates.
These are auxiliary finite-dimensional coordinates for Hastings,
arXiv:cond-mat/0508554v3, Section III, lines 630–685.
-/

open Matrix
open scoped ComplexOrder

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {D : Finset V}

/-- A supported global projection is the lift of a local orthogonal projection.
Auxiliary to Hastings, arXiv:cond-mat/0508554v3, Section III, lines 630–685. -/
theorem IsSupportedOn.exists_projection_localLift
    {P : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (hS : IsSupportedOn P D) (hP : IsStarProjection P) (σ₀ : SiteConfig n) :
    ∃ Q : Matrix (RegionConfig n D) (RegionConfig n D) ℂ,
      IsStarProjection Q ∧ P = localLift D Q := by
  classical
  obtain ⟨Q, hPQ⟩ := hS.exists_localLift σ₀
  refine ⟨Q, ⟨?_, ?_⟩, hPQ⟩
  case refine_2 =>
    change Qᴴ = Q
    apply localLift_injective D σ₀
    rw [localLift_conjTranspose, ← hPQ, hP.isSelfAdjoint.isHermitian.eq]
  case refine_1 =>
    change Q * Q = Q
    apply localLift_injective D σ₀
    rw [localLift_mul, ← hPQ, hP.isIdempotentElem.eq]

/-- A supported projection has actual local isometric coordinates. The dimension
is the rank of its local projection, before lifting by the exterior identity.
Auxiliary to Hastings, arXiv:cond-mat/0508554v3, Section III, lines 630–685. -/
theorem IsSupportedOn.exists_local_range_isometry
    {P : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (hS : IsSupportedOn P D) (hP : IsStarProjection P) (σ₀ : SiteConfig n) :
    ∃ (r : ℕ) (U : Matrix (RegionConfig n D) (Fin r) ℂ),
      U.IsIsometry ∧ P = localLift D (U * Uᴴ) ∧
      r = (U * Uᴴ).rank ∧ r ≤ Fintype.card (RegionConfig n D) := by
  classical
  obtain ⟨Q, hQ, hPQ⟩ := hS.exists_projection_localLift hP σ₀
  obtain ⟨r, U, hU, hUP⟩ := hQ.exists_matrix_range_isometry
  exact ⟨r, U, hU, hPQ.trans (congrArg (localLift D) hUP.symm),
    ((Matrix.rank_self_mul_conjTranspose U).trans
      ((Matrix.IsIsometry.rank_eq_card U hU).trans (Fintype.card_fin r))).symm,
    (Fintype.card_fin r).symm.le.trans (Matrix.IsIsometry.card_le U hU)⟩

end Entropy
