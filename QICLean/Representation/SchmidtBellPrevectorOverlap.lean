/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchmidtBellSitePin
import Mathlib.Analysis.Matrix.Hermitian

/-!
# The overlap with a supplied-label physical prevector

The selected Bell projection sends the original regrouped prevector to the
post vector with its supplied auxiliary label and the exact coefficient
`(sqrt z / E.card)^k`. For any supplied vector fixed by that Bell projection,
self-adjointness transfers this identity to the inner product. The coefficient
is not conjugated because the complex inner product is linear in its second
argument.

The same state, selected spectral set and irreducible label are retained.
No label sequence or common-cutoff vector is chosen. The overlap statement
requires positive selected mass and the displayed Bell-range equation, with
no normalization or symmetry hypothesis on the supplied vector. Every copy
number, including zero, is covered.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 240–254, 283–290 and
  346–354, `comparator:bell-pin` and `comparator:rough-overlap`, manuscript
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder
open Matrix PermutationRepresentation TensorPower

noncomputable section

namespace FiniteProduct

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (X : Finset V) (E : Finset (Configuration β X)) (k : ℕ)

local notation "A" => Configuration β X
local notation "B" => Configuration β Xᶜ
local notation "ι" => compressedSiteSpace β X (Fin E.card)
local notation "M" => (Fin k → A × E) × Config k ι

local instance schmidtBellOverlapConfigurationDecidableEq : DecidableEq (Configuration β X) :=
  Fintype.decidablePiFintype

variable (Ω : EuclideanSpace ℂ (Configuration β X × Configuration β Xᶜ))

/-- The original physical prevector in the actual selected-Bell and exterior
site coordinates, using only the fixed enumeration and copy regrouping.
Source: `07-comparators.tex`, lines 240–254 and 283–290. -/
def schmidtBellSitePrevector (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    EuclideanSpace ℂ M :=
  let r := (((Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ A)
    (fun _ ↦ Fin E.card)).prodCongr
      (Equiv.prodComm (Fin k → Fin E.card) (Fin k → B))).trans
    (Equiv.prodProdProdComm (Fin k → A) (Fin k → Fin E.card)
      (Fin k → B) (Fin k → Fin E.card))).trans
    ((Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ A) (fun _ ↦ B)).symm.prodCongr
      (Equiv.refl ((Fin k → Fin E.card) × (Fin k → Fin E.card))))
  WithLp.toLp 2 (replicaPrevector Ω E.card k ell ∘
    (r ∘ schmidtBellSiteEquiv β X E k))

local notation "z" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian (Matrix.PosSemidef.partialTraceRight
    (Matrix.posSemidef_vecMulVec_self_star Ω))) E

/-- A vector in the actual selected Bell range has an exact inner product
with the original prevector. The scalar is not conjugated, since the complex
inner product is linear in its second argument.
Source: `07-comparators.tex`, lines 283–290 and 346–354. -/
theorem inner_schmidtBellSitePrevector (hz : 0 < z)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) (φ : EuclideanSpace ℂ M)
    (hφ : toEuclideanLin
      ((finKronecker fun _ : Fin k ↦ selectedBellProjection Ω E) ⊗ₖ
        (1 : Matrix (Config k ι) (Config k ι) ℂ)) φ = φ) :
    let post : EuclideanSpace ℂ M := WithLp.toLp 2
      (fun x ↦ (∏ j, selectedBellVector Ω E (x.1 j)) *
        ∏ j, compressedTypicalPureState Ω E
          ((Finset.equivFin E).symm (x.2 j none), fun v ↦ x.2 j (some v)))
    ⟪φ, schmidtBellSitePrevector β X E k Ω ell⟫_ℂ =
      (((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k) *
        ⟪φ, toEuclideanLin
          ((1 : Matrix (Fin k → A × E) (Fin k → A × E) ℂ) ⊗ₖ
            labelProj (subsystemPerm k ι {none}) ell) post⟫_ℂ := by
  intro post
  let P := (finKronecker fun _ : Fin k ↦ selectedBellProjection Ω E) ⊗ₖ
    (1 : Matrix (Config k ι) (Config k ι) ℂ)
  let Q := (1 : Matrix (Fin k → A × E) (Fin k → A × E) ℂ) ⊗ₖ
    labelProj (subsystemPerm k ι {none}) ell
  let c : ℂ := ((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k
  have hBell : (finKronecker fun _ : Fin k ↦ selectedBellProjection Ω E).IsHermitian :=
    (isStarProjection_finKronecker_selectedBellProjection Ω E k hz).isSelfAdjoint.isHermitian
  have hP : P.IsHermitian := by
    change (finKronecker (fun _ : Fin k ↦ selectedBellProjection Ω E) ⊗ₖ
      (1 : Matrix (Config k ι) (Config k ι) ℂ))ᴴ = _
    rw [conjTranspose_kronecker, hBell.eq, conjTranspose_one]
  have hpin := selectedBellProjection_replicaPrevector_site β X E k Ω hz ell
  change toEuclideanLin P (schmidtBellSitePrevector β X E k Ω ell) =
    c • toEuclideanLin Q post at hpin
  change ⟪φ, schmidtBellSitePrevector β X E k Ω ell⟫_ℂ =
    c * ⟪φ, toEuclideanLin Q post⟫_ℂ
  calc
    ⟪φ, schmidtBellSitePrevector β X E k Ω ell⟫_ℂ =
        ⟪toEuclideanLin P φ, schmidtBellSitePrevector β X E k Ω ell⟫_ℂ := by rw [hφ]
    _ = ⟪φ, toEuclideanLin P (schmidtBellSitePrevector β X E k Ω ell)⟫_ℂ :=
      (isSymmetric_toEuclideanLin_iff.mpr hP) φ _
    _ = c * ⟪φ, toEuclideanLin Q post⟫_ℂ := by rw [hpin, inner_smul_right]

end FiniteProduct
