/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausMap.KrausCPTP

/-!
# Maps with a single Kraus operator

The map `X ↦ V X Vᴴ` of one matrix `V`: its behaviour under reindexing of the two spaces, the
range of an isometric conjugation, and commutation with a unitary intertwiner of `V`. These are
finite-dimensional facts about sitewise physical matrices, used with the physical-sector
projections of arXiv:1606.00608, Appendix C.2.

Moved from TNLean, `TNLean/MPS/Operator/PhysicalSector/SitewisePhysicalMatrix.lean`,
`TNLean/MPS/Symmetry/GappedPath/PhysicalInteractionGroundSpace.lean`,
`TNLean/MPS/Symmetry/SPTClassification/CommonPhysicalFixedPointPath.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

section

open scoped Matrix BigOperators Kronecker

namespace Matrix

/-- Reindexing the input and output bases commutes with a single-Kraus
conjugation. -/
theorem reindex_singleKrausMap
    {α α' β β' : Type*} [Fintype α] [Fintype α']
    [Fintype β] [Fintype β']
    (eα : α ≃ α') (eβ : β ≃ β')
    (V : Matrix β α ℂ) (X : Matrix α α ℂ) :
    reindex eβ eβ (singleKrausMap V X) =
      singleKrausMap (reindex eβ eα V) (reindex eα eα X) := by
  simp only [singleKrausMap_apply]
  change reindexLinearEquiv ℂ ℂ eβ eβ (V * X * Vᴴ) = _
  rw [← reindexLinearEquiv_mul ℂ ℂ eβ eα eβ,
    ← reindexLinearEquiv_mul ℂ ℂ eβ eα eα]
  simp only [Matrix.coe_reindexLinearEquiv, Matrix.conjTranspose_reindex]

end Matrix

end

section

open scoped Matrix BigOperators ComplexOrder Kronecker


namespace Matrix

/-- The range of an isometrically conjugated matrix is the isometric
image of its original range. -/
theorem range_toEuclideanLin_singleKrausMap_of_isometry
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix κ ι ℂ) (hV : Vᴴ * V = 1) (M : Matrix ι ι ℂ) :
    LinearMap.range (Matrix.toEuclideanLin (singleKrausMap V M)) =
      (LinearMap.range (Matrix.toEuclideanLin M)).map (Matrix.toEuclideanLin V) := by
  have hSurj : Function.Surjective (Matrix.toEuclideanLin Vᴴ) := fun x =>
    ⟨Matrix.toEuclideanLin V x, by
      simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
        Matrix.toLpLin_one, LinearMap.comp_apply, LinearMap.id_apply] using
        congrArg (fun A => Matrix.toEuclideanLin A x) hV⟩
  simpa only [singleKrausMap_apply, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
    (LinearMap.range_comp_of_range_eq_top
      (Matrix.toEuclideanLin V ∘ₗ Matrix.toEuclideanLin M)
      (LinearMap.range_eq_top.mpr hSurj)).trans (LinearMap.range_comp _ _)

end Matrix

end

section

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator


namespace Matrix

/-- Unitary symmetry is preserved by physical conjugation when the
rectangular physical map intertwines the two unitary actions. -/
theorem commute_singleKrausMap_of_unitary_intertwiner
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix κ κ ℂ) (V : Matrix ι ι ℂ) (E : Matrix κ ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup κ ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (hE : U * E = E * V) (M : Matrix ι ι ℂ) (hM : Commute V M) :
    Commute U (singleKrausMap E M) := by
  have hRight : Eᴴ * U = V * Eᴴ := by
    have h := congrArg Matrix.conjTranspose hE
    have hh := congrArg (fun A => V * A * U) h
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.star_eq_conjTranspose] at hh
    rw [(Matrix.mem_unitaryGroup_iff'.mp hU), Matrix.mul_one,
      ← Matrix.mul_assoc V, (Matrix.mem_unitaryGroup_iff.mp hV), Matrix.one_mul] at hh
    exact hh.symm
  apply (commute_iff_eq _ _).mpr
  calc
    U * singleKrausMap E M = (U * E) * M * Eᴴ := by
      simp only [singleKrausMap_apply, Matrix.mul_assoc]
    _ = (E * V) * M * Eᴴ := by rw [hE]
    _ = E * (M * V) * Eᴴ := by rw [Matrix.mul_assoc E V M, hM.eq]
    _ = (E * M) * (Eᴴ * U) := by simp only [Matrix.mul_assoc, hRight]
    _ = singleKrausMap E M * U := by simp only [singleKrausMap_apply, Matrix.mul_assoc]

end Matrix

end
