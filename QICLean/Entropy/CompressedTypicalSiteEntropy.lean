/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CompressedTypicalSiteCoordinates

/-!
# Regional entropy of the actual compressed selected vector

The actual regional marginal in the augmented site family is the selected
physical marginal after a canonical coordinate change. Entropy is invariant
under this change. The existing entropy comparison for the selected physical
state therefore applies to this same compressed vector on every disjoint
physical region.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 320–343,
  `comparator:post-marginal` and `comparator:rough-overlap`, source commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped ComplexOrder

noncomputable section

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The actual compressed state's entropy on a disjoint physical region is
at most the original regional entropy divided by the actual selected mass.
The regional marginal equality is derived from the literal selected state,
not supplied as a hypothesis.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 320–343. -/
theorem entropy_compressedTypicalSiteState_le
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X B : Finset V)
    (hXB : Disjoint X B) (E : Finset (Configuration β X)) (hΩ : ‖Ω‖ = 1)
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let χsite := WithLp.toLp 2
      (fun x : (f : Option ↥(Xᶜ)) → compressedSiteSpace β X (Fin E.card) f ↦
        Matrix.compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x none), fun v ↦ x (some v)))
    entropy (compressedSiteSpace β X (Fin E.card)) χsite (exteriorRegion X B) ≤
      entropy β Ω B /
        (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E := by
  intro ΩX χsite
  let ρ := reducedPure (compressedSiteSpace β X (Fin E.card)) χsite (exteriorRegion X B)
  have hρ : ρ.IsHermitian :=
    (reducedPure_posSemidef (compressedSiteSpace β X (Fin E.card))
      χsite (exteriorRegion X B)).isHermitian
  let e := exteriorRegionEquiv β X B (Fin E.card) hXB
  have hm : ρ.submatrix e.symm e.symm =
      reducedPure β (typicalPureState β Ω X E) B :=
    reducedPure_compressedTypicalSiteState β X B Ω hXB E
  have hentropy :
      entropy (compressedSiteSpace β X (Fin E.card)) χsite (exteriorRegion X B) =
        entropy β (typicalPureState β Ω X E) B := by
    exact (vonNeumannEntropy_submatrix_equiv e.symm ρ hρ).symm.trans
      (vonNeumannEntropy_congr hm _
        (reducedPure_posSemidef β (typicalPureState β Ω X E) B).isHermitian)
  rw [hentropy]
  exact entropy_typicalPureState_le β Ω X E B hXB hΩ hz

end FiniteProduct
