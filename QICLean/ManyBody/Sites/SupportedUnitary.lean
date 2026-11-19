/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixReindexEuclidean
import QICLean.Analysis.PolarUnitaryCorrectionKronecker
import QICLean.ManyBody.Sites.Placement

/-!
# A supported unitary polar correction

An operator `D` supported on a region `S` has a unitary polar factor supported on the same
region. For all vectors `x, y` this unitary satisfies the two-sided correction estimate
`‖U x - y‖ ≤ ‖D x - y‖ + ‖Dᴴ y - x‖`. No auxiliary system is adjoined, and no invertibility or
normalization of `D` is required.

Moved from TNLean, `TNLean/Lattice/SupportedPolarUnitary.lean` at commit `e41c3b63`, restated
for an arbitrary family of local alphabets.

## Main results

* `ManyBody.exists_supported_unitary_polar_correction`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, `02-information.tex`, lines 565–595, equations `eq:info-reset-polar-errors` and
  `eq:info-reset-unitary`.
-/

open Matrix
open scoped Kronecker

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- **A unitary polar factor on the same support.** Every operator `D` supported on a region
`S` has a unitary `U`, also supported on `S`, with `‖U x - y‖ ≤ ‖D x - y‖ + ‖Dᴴ y - x‖` for
all vectors `x, y`. The unitary is the placement of the polar factor of the regional operator
of `D`. Polynomial PEPS approximation, `02-information.tex`, lines 580–595
(`eq:info-reset-unitary`). -/
theorem exists_supported_unitary_polar_correction {S : Finset V}
    {D : Matrix (Config X) (Config X) ℂ} (hD : D ∈ supportedOperators X S) :
    ∃ U ∈ unitaryGroup (Config X) ℂ, U ∈ supportedOperators X S ∧
      ∀ x y : EuclideanSpace ℂ (Config X),
        ‖toEuclideanLin U x - y‖ ≤ ‖toEuclideanLin D x - y‖ + ‖toEuclideanLin Dᴴ y - x‖ := by
  obtain ⟨K, rfl⟩ := exists_eq_place_of_mem_supportedOperators hD
  obtain ⟨U', hpolar, -, -⟩ := exists_unitary_polar_correction K
  obtain ⟨-, -, -, hcorr⟩ :=
    unitary_polar_correction_kronecker_one (m := ComplConfig X S) K U' hpolar
  refine ⟨place S U', ?_, place_mem_supportedOperators _, fun x y ↦ ?_⟩
  · rw [mem_unitaryGroup_iff', star_eq_conjTranspose, ← place_conjTranspose, ← place_mul,
      ← star_eq_conjTranspose, (mem_unitaryGroup_iff'.mp U'.prop), place_one]
  set e := (cutEquiv X S).symm
  set φ := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  have hlin (A : Matrix (RegionConfig X S) (RegionConfig X S) ℂ) (z : EuclideanSpace ℂ _) :
      toEuclideanLin (place S A) z =
        φ (toEuclideanLin (A ⊗ₖ (1 : Matrix (ComplConfig X S) (ComplConfig X S) ℂ))
          (φ.symm z)) := by
    rw [← toEuclideanLin_reindex_piLpCongrLeft, LinearIsometryEquiv.apply_symm_apply]
    rfl
  have h := hcorr (φ.symm x) (φ.symm y)
  rw [← place_conjTranspose, hlin, hlin, hlin]
  have hcl (A : Matrix (RegionConfig X S × ComplConfig X S)
      (RegionConfig X S × ComplConfig X S) ℂ) (z : EuclideanSpace ℂ _) :
      toEuclideanCLM (n := _) (𝕜 := ℂ) A z = toEuclideanLin A z :=
    rfl
  simp only [hcl] at h
  rw [← φ.apply_symm_apply y, ← φ.apply_symm_apply x, ← map_sub, ← map_sub, ← map_sub,
    φ.norm_map, φ.norm_map, φ.norm_map, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]
  simpa [conjTranspose_kronecker] using h

end ManyBody
