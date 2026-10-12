/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchmidtBellPrevectorOverlap
import QICLean.Representation.SchmidtBellWitnessCoordinates
import QICLean.Representation.RegionalFiveFactorCoordinates

/-!
# Enumerating the selected auxiliary register in the prevector

The supplied Schmidt--Bell prevector uses the selected index set itself as
the left auxiliary register. Enumerating that register identifies this
vector with the original prevector whose two auxiliary registers are both
indexed by the same finite interval. The physical state, selected set and
irreducible label are unchanged.

The equality holds for an arbitrary physical vector and every copy number.
It requires neither normalization nor positive selected mass, and includes
an empty selected set. Splitting the physical coordinates and enumerating
the auxiliary register are the only changes of coordinates.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 130--147,
  240--254 and 283--290, `comparator:prevector` and `comparator:bell-pin`,
  manuscript revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix TensorPower PermutationRepresentation

noncomputable section

namespace FiniteProduct

/-- Enumerating only the selected C register identifies the supplied
Schmidt--Bell prevector with the original global prevector. The physical
state, selected set and irreducible label are unchanged. No normalization
or positive-mass hypothesis is required for this coordinate identity.

Source: area-law manuscript, `07-comparators.tex`, lines 130--147,
240--254 and 283--290, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem schmidtBellSitePrevector_enumerate_C
    {V : Type} [Fintype V] [DecidableEq V]
    (β : V → Type) [∀ v, Fintype (β v)]
    (Ω : EuclideanSpace ℂ ((v : V) → β v))
    (X : Finset V) (E : Finset (Configuration β X)) (k : ℕ)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let ιE := addedSiteSpace (addedSiteSpace β E) (Fin E.card)
    let ιF := addedSiteSpace (addedSiteSpace β (Fin E.card)) (Fin E.card)
    let changeSite : ∀ o : Option (Option V), ιF o ≃ ιE o := fun o ↦
      match o with
      | none => Equiv.refl (Fin E.card)
      | some none => (Finset.equivFin E).symm
      | some (some v) => Equiv.refl (β v)
    let e := Equiv.piCongrRight fun _ : Fin k ↦ Equiv.piCongrRight changeSite
    let τ := schmidtBellWitnessEquiv β X E k
    (schmidtBellSitePrevector β X E k ΩX ell).ofLp ∘ τ ∘ e =
      replicaPrevector Ω E.card k ell ∘
        globalReplicaCopiesEquiv β (Fin E.card) (Fin E.card) k := by
  intro ΩX ιE ιF changeSite e τ
  funext x
  change replicaPrevector ΩX E.card k ell
      ((fun j ↦ splitEquiv β X (fun v ↦ x j (some (some v)))),
        ((fun j ↦ (Finset.equivFin E) ((Finset.equivFin E).symm (x j (some none)))),
          (fun j ↦ x j none))) =
    replicaPrevector Ω E.card k ell
      ((fun j v ↦ x j (some (some v))),
        ((fun j ↦ x j (some none)), (fun j ↦ x j none)))
  simp only [replicaPrevector, ΩX,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
  dsimp only [ιF, addedSiteSpace] at x
  simp only [(Finset.equivFin E).apply_symm_apply, (splitEquiv β X).symm_apply_apply]

end FiniteProduct
