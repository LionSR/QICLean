/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellInsertionSymmetry
import QICLean.Entropy.TypicalBellPinPowers

/-!
# The selected Bell insertion in witness coordinates

The left auxiliary coordinate is the actual selected set E, and the right
auxiliary coordinate is Fin E.card. Separating the inserted Bell coordinates
from the exterior coordinates identifies the actual insertion range matrix
with the selected Bell tensor-power matrix tensored with the exterior identity.
The identity is valid before any normalization or positive selected-mass
hypothesis is imposed.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 240–254, 283–290
  and 332–354, `comparator:bell-pin` and `comparator:rough-overlap`,
  at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation TensorPower
open scoped BigOperators Matrix Kronecker

noncomputable section

namespace ManyBody

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (X : Finset V) (E : Finset (ManyBody.RegionConfig β X)) (k : ℕ)

local notation "A" => ManyBody.RegionConfig β X
local notation "B" => ManyBody.RegionConfig β Xᶜ
local notation "ι₀" => addedSiteSpace (addedSiteSpace β E) (Fin E.card)
local notation "ιe" => ManyBody.compressedSiteSpace β X (Fin E.card)
local notation "L" => Fin k → A × E

local instance schmidtBellCoordinatesConfigurationDecidableEq : DecidableEq
    (ManyBody.RegionConfig β X) :=
  Fintype.decidablePiFintype

local instance schmidtBellCoordinatesExteriorConfigDecidableEq :
    DecidableEq (TensorPower.Config k ιe) := Fintype.decidablePiFintype

/-- Separate the actual selected-Bell copies from the retained exterior
copies. The left selected coordinate E and the right coordinate Fin E.card
are retained separately.
Source: area-law manuscript, `07-comparators.tex`, lines 240–254 and 283–290. -/
def schmidtBellWitnessEquiv : TensorPower.Config k ι₀ ≃ L × TensorPower.Config k ιe :=
  (bellInsertionCopyEquiv β X ↥E (Fin E.card) k).trans
    (addedSiteConfigEquiv ιe (A × E) k)

variable (Ω : EuclideanSpace ℂ (ManyBody.RegionConfig β X × ManyBody.RegionConfig β Xᶜ))

/-- The actual insertion range matrix is the selected Bell tensor-power
matrix tensored with the exterior identity, in the explicit witness
coordinates. No range identity, normalization, or positive selected mass is
assumed.
Source: area-law manuscript, `07-comparators.tex`, lines 247–254 and 283–290. -/
theorem bellInsertion_mul_conjTranspose_selectedBell :
    let e := bellInsertionCopyEquiv β X ↥E (Fin E.card) k
    let b : A × E → ℂ := selectedBellVector Ω E
    let J := (addedSiteInsertion ιe (A × E) k b).submatrix e id
    J * Jᴴ =
      ((finKronecker fun _ : Fin k ↦ selectedBellProjection Ω E) ⊗ₖ
        (1 : Matrix (TensorPower.Config k ιe) (TensorPower.Config k ιe) ℂ)).submatrix
          (ManyBody.schmidtBellWitnessEquiv β X E k)
              (ManyBody.schmidtBellWitnessEquiv β X E k) := by
  intro e b J
  let τ := ManyBody.schmidtBellWitnessEquiv β X E k
  let : DecidableEq (TensorPower.Config k ιe) := fun y z ↦ Classical.propDecidable (y = z)
  ext x y
  change (∑ q : TensorPower.Config k ιe,
      ((∏ j, b ((τ x).1 j)) * if (τ x).2 = q then 1 else 0) *
        star ((∏ j, b ((τ y).1 j)) * if (τ y).2 = q then 1 else 0)) = _
  calc
    _ = (∏ j, b ((τ x).1 j)) * star (∏ j, b ((τ y).1 j)) *
        (if (τ x).2 = (τ y).2 then 1 else 0) := by
      rw [Finset.sum_eq_single ((τ x).2)]
      · by_cases h : (τ x).2 = (τ y).2 <;> simp [h, eq_comm]
      · intro q _ hq
        simp [Ne.symm hq]
      · simp
    _ = _ := by
      by_cases h : (τ x).2 = (τ y).2 <;>
        simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
          finKronecker_apply, selectedBellProjection, vecMulVec_apply,
          Pi.star_apply, Matrix.one_apply, b, τ, h, star_prod, Finset.prod_mul_distrib]

end ManyBody
