/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchmidtBellPrevector
import QICLean.Representation.CompressedTypicalLabelMass

/-!
# The selected Bell identity in the actual exterior-site coordinates

The selected Bell factor uses the original selected set E, while the exterior
auxiliary site uses Fin E.card. Their relation is the fixed enumeration of E.
The physical complementary copies and auxiliary copies are collected by the
actual exterior coordinate equivalence. Under these changes of coordinates,
the universal selected-Bell identity becomes an identity with the literal
sitewise compressed vector, retaining its scalar (sqrt z / E.card)^k.

No input-vector identity, projector intertwining, or choice of basis is
assumed. The coordinate equalities below derive them from the actual
enumeration and subsystem action. The final identity holds for every label
and every copy number, including zero. The bipartite vector is arbitrary,
subject only to the existing positive selected-mass hypothesis.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 240–254 and 283–290,
  `comparator:bell-pin`, manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder
open Matrix PermutationRepresentation TensorPower

noncomputable section

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (X : Finset V) (E : Finset (Configuration β X)) (k : ℕ)

local notation "A" => Configuration β X
local notation "B" => Configuration β Xᶜ
local notation "ι" => compressedSiteSpace β X (Fin E.card)
local notation "M" => (Fin k → A × E) × Config k ι
local notation "N" => (Fin k → A × Fin E.card) ×
  ((Fin k → Fin E.card) × (Fin k → B))

/-- Enumerate the left selected coordinates and collect the actual exterior
copies, with the right auxiliary coordinates before the physical complement.
Source: `07-comparators.tex`, lines 240–254 and 283–290. -/
def schmidtBellSiteEquiv : M ≃ N :=
  (Equiv.piCongrRight fun _ : Fin k ↦
    (Equiv.refl A).prodCongr (Finset.equivFin E)).prodCongr
      ((exteriorCopyEquiv β X (Fin E.card) k).trans
        (Equiv.prodComm (Fin k → B) (Fin k → Fin E.card)))

variable (Ω : EuclideanSpace ℂ (Configuration β X × Configuration β Xᶜ))

/-- Pulling back the enumerated Bell projector gives the literal selected
Bell projector, with identity on the actual exterior sites.
Source: `07-comparators.tex`, lines 247–254 and 283–290. -/
theorem selectedBellProjection_schmidtBellSiteEquiv :
    let b : A × Fin E.card → ℂ := fun x ↦
      selectedBellVector Ω E (x.1, (Finset.equivFin E).symm x.2)
    let P := finKronecker fun _ : Fin k ↦ vecMulVec b (star b)
    ((P ⊗ₖ (1 : Matrix ((Fin k → Fin E.card) × (Fin k → B))
        ((Fin k → Fin E.card) × (Fin k → B)) ℂ)).submatrix
        (schmidtBellSiteEquiv β X E k) (schmidtBellSiteEquiv β X E k)) =
      (finKronecker fun _ : Fin k ↦ selectedBellProjection Ω E) ⊗ₖ
        (1 : Matrix (Config k ι) (Config k ι) ℂ) := by
  intro b P
  let eL := Equiv.piCongrRight fun _ : Fin k ↦
    (Equiv.refl A).prodCongr (Finset.equivFin E)
  let eR := (exteriorCopyEquiv β X (Fin E.card) k).trans
    (Equiv.prodComm (Fin k → B) (Fin k → Fin E.card))
  have hP : P.submatrix eL eL =
      finKronecker (fun _ : Fin k ↦ selectedBellProjection Ω E) := by
    ext x y
    change (∏ j, selectedBellVector Ω E
        ((x j).1, (Finset.equivFin E).symm ((Finset.equivFin E) (x j).2)) *
        star (selectedBellVector Ω E
          ((y j).1, (Finset.equivFin E).symm ((Finset.equivFin E) (y j).2)))) =
      ∏ j, selectedBellVector Ω E (x j) * star (selectedBellVector Ω E (y j))
    simp only [Equiv.symm_apply_apply]
  change P.submatrix eL eL ⊗ₖ
    (1 : Matrix ((Fin k → Fin E.card) × (Fin k → B))
      ((Fin k → Fin E.card) × (Fin k → B)) ℂ).submatrix eR eR = _
  rw [hP, Matrix.submatrix_one_equiv]

/-- The right auxiliary label in the enumerated coordinates is exactly the
actual label on the auxiliary site. This uses the derived subsystem action,
not a supplied intertwining hypothesis.
Source: `07-comparators.tex`, lines 255–281 and 283–290. -/
theorem labelProj_schmidtBellSiteEquiv
    (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    (((1 : Matrix (Fin k → A × Fin E.card) (Fin k → A × Fin E.card) ℂ) ⊗ₖ
        (labelProj (copyPerm (Fin E.card) k) ell ⊗ₖ
          (1 : Matrix (Fin k → B) (Fin k → B) ℂ))).submatrix
        (schmidtBellSiteEquiv β X E k) (schmidtBellSiteEquiv β X E k)) =
      (1 : Matrix (Fin k → A × E) (Fin k → A × E) ℂ) ⊗ₖ
        labelProj (subsystemPerm k ι {none}) ell := by
  let eL := Equiv.piCongrRight fun _ : Fin k ↦
    (Equiv.refl A).prodCongr (Finset.equivFin E)
  let e0 := exteriorCopyEquiv β X (Fin E.card) k
  let eR := e0.trans (Equiv.prodComm (Fin k → B) (Fin k → Fin E.card))
  have hQ : (labelProj (copyPerm (Fin E.card) k) ell ⊗ₖ
      (1 : Matrix (Fin k → B) (Fin k → B) ℂ)).submatrix eR eR =
        labelProj (subsystemPerm k ι {none}) ell := by
    ext x y
    change labelProj (copyPerm (Fin E.card) k) ell (e0 x).2 (e0 y).2 *
      (1 : Matrix (Fin k → B) (Fin k → B) ℂ) (e0 x).1 (e0 y).1 = _
    have h := congrArg (fun Q ↦ Q (e0 x) (e0 y))
      (labelProj_compressedSite_submatrix β X (Fin E.card) k ell)
    simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.kroneckerMap_apply, mul_comm] using h.symm
  change (1 : Matrix (Fin k → A × Fin E.card) (Fin k → A × Fin E.card) ℂ).
      submatrix eL eL ⊗ₖ
    (labelProj (copyPerm (Fin E.card) k) ell ⊗ₖ
      (1 : Matrix (Fin k → B) (Fin k → B) ℂ)).submatrix eR eR = _
  rw [Matrix.submatrix_one_equiv, hQ]

/-- The post vector becomes the literal selected Bell power times the
sitewise power of the actual compressed vector, with the fixed selected
enumeration. Source: `07-comparators.tex`, lines 240–254. -/
theorem schmidtBellSiteEquiv_post :
    let b : A × Fin E.card → ℂ := fun x ↦
      selectedBellVector Ω E (x.1, (Finset.equivFin E).symm x.2)
    let χ : Fin E.card × B → ℂ := fun x ↦
      compressedTypicalPureState Ω E ((Finset.equivFin E).symm x.1, x.2)
    (fun x : N ↦ (∏ j, b (x.1 j)) * ∏ j, χ (x.2.1 j, x.2.2 j)) ∘
        schmidtBellSiteEquiv β X E k =
      fun x : M ↦ (∏ j, selectedBellVector Ω E (x.1 j)) *
        ∏ j, compressedTypicalPureState Ω E
          ((Finset.equivFin E).symm (x.2 j none), fun v ↦ x.2 j (some v)) := by
  intro b χ
  funext x
  change (∏ j, selectedBellVector Ω E
      ((x.1 j).1, (Finset.equivFin E).symm ((Finset.equivFin E) (x.1 j).2))) *
      (∏ j, compressedTypicalPureState Ω E
        ((Finset.equivFin E).symm (x.2 j none), fun v ↦ x.2 j (some v))) = _
  simp only [Equiv.symm_apply_apply]

local notation "z" => (posSemidef_vecMulVec_self_star Ω).partialTraceRight.
  isHermitian.spectralRestrictionMass E

/-- The universal selected-Bell identity in the actual exterior-site
coordinates. The prevector is the original prevector pulled back by the
explicit regrouping, and the right side is the actual post vector with its
actual auxiliary label. The scalar is retained exactly, for every k and λ.

Source: `07-comparators.tex`, lines 283–290, `comparator:bell-pin`. -/
theorem selectedBellProjection_replicaPrevector_site (hz : 0 < z)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let r := (((Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ A)
      (fun _ ↦ Fin E.card)).prodCongr
        (Equiv.prodComm (Fin k → Fin E.card) (Fin k → B))).trans
      (Equiv.prodProdProdComm (Fin k → A) (Fin k → Fin E.card)
        (Fin k → B) (Fin k → Fin E.card))).trans
      ((Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ A) (fun _ ↦ B)).symm.prodCongr
        (Equiv.refl ((Fin k → Fin E.card) × (Fin k → Fin E.card))))
    let e := schmidtBellSiteEquiv β X E k
    let post : M → ℂ := fun x ↦ (∏ j, selectedBellVector Ω E (x.1 j)) *
      ∏ j, compressedTypicalPureState Ω E
        ((Finset.equivFin E).symm (x.2 j none), fun v ↦ x.2 j (some v))
    WithLp.toLp 2
      (((finKronecker fun _ : Fin k ↦ selectedBellProjection Ω E) ⊗ₖ
        (1 : Matrix (Config k ι) (Config k ι) ℂ)) *ᵥ
          (replicaPrevector Ω E.card k ell ∘ (r ∘ e))) =
      (((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k) • WithLp.toLp 2
        (((1 : Matrix (Fin k → A × E) (Fin k → A × E) ℂ) ⊗ₖ
          labelProj (subsystemPerm k ι {none}) ell) *ᵥ post) := by
  intro r e post
  let b : A × Fin E.card → ℂ := fun x ↦
    selectedBellVector Ω E (x.1, (Finset.equivFin E).symm x.2)
  let χ : Fin E.card × B → ℂ := fun x ↦
    compressedTypicalPureState Ω E ((Finset.equivFin E).symm x.1, x.2)
  let P := (finKronecker fun _ : Fin k ↦ vecMulVec b (star b)) ⊗ₖ
    (1 : Matrix ((Fin k → Fin E.card) × (Fin k → B))
      ((Fin k → Fin E.card) × (Fin k → B)) ℂ)
  let Q := (1 : Matrix (Fin k → A × Fin E.card) (Fin k → A × Fin E.card) ℂ) ⊗ₖ
    (labelProj (copyPerm (Fin E.card) k) ell ⊗ₖ
      (1 : Matrix (Fin k → B) (Fin k → B) ℂ))
  let postFin : N → ℂ := fun x ↦ (∏ j, b (x.1 j)) * ∏ j, χ (x.2.1 j, x.2.2 j)
  let c : ℂ := ((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k
  have hold := TensorPower.selectedBellProjection_replicaPrevector Ω E k hz ell
  change WithLp.toLp 2 (P *ᵥ (replicaPrevector Ω E.card k ell ∘ r)) =
    c • WithLp.toLp 2 (Q *ᵥ postFin) at hold
  have hP : P.submatrix e e =
      (finKronecker fun _ : Fin k ↦ selectedBellProjection Ω E) ⊗ₖ
        (1 : Matrix (Config k ι) (Config k ι) ℂ) :=
    selectedBellProjection_schmidtBellSiteEquiv β X E k Ω
  have hQ : Q.submatrix e e =
      (1 : Matrix (Fin k → A × E) (Fin k → A × E) ℂ) ⊗ₖ
        labelProj (subsystemPerm k ι {none}) ell :=
    labelProj_schmidtBellSiteEquiv β X E k ell
  have hpost : postFin ∘ e = post := schmidtBellSiteEquiv_post β X E k Ω
  ext x
  have hx := congrArg (fun v : EuclideanSpace ℂ N ↦ v (e x)) hold
  change (((finKronecker fun _ : Fin k ↦ selectedBellProjection Ω E) ⊗ₖ
      (1 : Matrix (Config k ι) (Config k ι) ℂ)) *ᵥ
        (replicaPrevector Ω E.card k ell ∘ (r ∘ e))) x =
    c * (((1 : Matrix (Fin k → A × E) (Fin k → A × E) ℂ) ⊗ₖ
      labelProj (subsystemPerm k ι {none}) ell) *ᵥ post) x
  rw [← hP, ← hQ, ← hpost, Matrix.submatrix_mulVec_equiv,
    Matrix.submatrix_mulVec_equiv]
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hx

end FiniteProduct
