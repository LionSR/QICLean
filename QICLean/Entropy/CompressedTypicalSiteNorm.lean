/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CompressedTypicalSiteCoordinates

/-!
# Norm of the actual compressed selected vector on exterior sites

The exterior site family carries the same compressed selected vector as the
selected spectral coordinate space. The identification is the actual option
product equivalence followed by the inverse enumeration of the selected
indices. It is a coordinate isometry, so positive actual selected mass gives
a unit vector. No normalization assumption on the original vector is needed.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 240–247 and 332–354,
  source commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped ComplexOrder

noncomputable section

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- Positive actual selected mass normalizes the literal compressed vector
on the auxiliary site and the original complementary physical sites.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem norm_compressedTypicalSiteState
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
    (E : Finset (ManyBody.RegionConfig β X))
    (hz : 0 < (ManyBody.regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (ManyBody.cutEquiv β X) Ω
    ‖WithLp.toLp 2
      (fun x : (f : Option {v // v ∉ X}) → ManyBody.compressedSiteSpace β X (Fin E.card) f ↦
        Matrix.compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x none), fun v ↦ x (some v)))‖ = 1 := by
  intro ΩX
  let e : ((f : Option {v // v ∉ X}) → ManyBody.compressedSiteSpace β X (Fin E.card) f) ≃
      E × ManyBody.ComplConfig β X :=
    (Equiv.piOptionEquivProd (β := ManyBody.compressedSiteSpace β X (Fin E.card))).trans
      ((Finset.equivFin E).symm.prodCongr (Equiv.refl (ManyBody.ComplConfig β X)))
  have hzX : 0 < Matrix.IsHermitian.spectralRestrictionMass
      (Matrix.PosSemidef.isHermitian
        (Matrix.posSemidef_vecMulVec_self_star ΩX).partialTraceRight) E := by
    exact hz
  calc
    _ = ‖Matrix.compressedTypicalPureState ΩX E‖ :=
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).norm_map
        (Matrix.compressedTypicalPureState ΩX E)
    _ = 1 := Matrix.norm_compressedTypicalPureState ΩX E hzX

end ManyBody
