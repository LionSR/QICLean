/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.GroupAlgebraProductCoordinates
import QICLean.Representation.CompressedTypicalAuxiliaryCoordinates
import QICLean.Representation.LabelProjectors

/-!
# The same auxiliary-label mass in actual compressed-site coordinates

The auxiliary-site permutation action is transported by the actual exterior
coordinate equivalence. Its central label projector consequently becomes
the projector on the same auxiliary copies, with the physical copies fixed.
The coordinate isometry preserves the projected norm. Applied to the literal
compressed selected vector, this gives exactly the mass in the existing
Schmidt–Bell label-sequence theorem, for every fixed label.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 255–281 and 332–354,
  source commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped BigOperators Matrix Kronecker
open Matrix PermutationRepresentation

universe u

noncomputable section

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
section GeneralAuxiliary

variable (β : V → Type u) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (X : Finset V) (R : Type u) [Fintype R] [DecidableEq R] (k : ℕ)

/-- In the actual exterior coordinates, the central auxiliary label acts on
the same auxiliary copies and fixes the physical copies. The intertwining is
derived from the literal subsystem action. -/
theorem labelProj_compressedSite_submatrix
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    (labelProj (subsystemPerm k (FiniteProduct.compressedSiteSpace β X R) {none}) l).submatrix
        (exteriorCopyEquiv β X R k).symm (exteriorCopyEquiv β X R k).symm =
      (1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
        (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
          labelProj (copyPerm R k) l := by
  exact groupAlgebraRep_submatrix_of_prod_action
    (subsystemPerm k (FiniteProduct.compressedSiteSpace β X R) {none})
    (copyPerm R k) (exteriorCopyEquiv β X R k)
    (exteriorCopyEquiv_subsystemPerm_none β X R k) (IrrepLabel.centralIdem l)

/-- The actual sitewise auxiliary-label mass equals the ordinary auxiliary
projection mass of the same tensor-power vector in physical-first coordinates.
No normalization, nonzero mass, or symmetry hypothesis is required. -/
theorem norm_sq_labelProj_compressedSite_prod
    (χ : R × FiniteProduct.Configuration β Xᶜ → ℂ)
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    ‖toEuclideanLin
        (labelProj (subsystemPerm k (FiniteProduct.compressedSiteSpace β X R) {none}) l)
        (WithLp.toLp 2 (fun x : Config k (FiniteProduct.compressedSiteSpace β X R) ↦
          ∏ j, χ (Equiv.piOptionEquivProd (x j))))‖ ^ 2 =
      ‖WithLp.toLp 2
        (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
            (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
            labelProj (copyPerm R k) l) *ᵥ
          (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) × (Fin k → R) ↦
            ∏ j, χ (x.2 j, x.1 j)))‖ ^ 2 := by
  let e := exteriorCopyEquiv β X R k
  let Q := labelProj (subsystemPerm k (FiniteProduct.compressedSiteSpace β X R) {none}) l
  let v : Config k (FiniteProduct.compressedSiteSpace β X R) → ℂ :=
    fun x ↦ ∏ j, χ (Equiv.piOptionEquivProd (x j))
  let w : (Fin k → FiniteProduct.Configuration β Xᶜ) × (Fin k → R) → ℂ :=
    fun x ↦ ∏ j, χ (x.2 j, x.1 j)
  have hw : v ∘ e.symm = w := by
    funext x
    exact exteriorCopyEquiv_prod β X R k χ x
  have hmul : Q.submatrix e.symm e.symm *ᵥ w = (Q *ᵥ v) ∘ e.symm := by
    rw [← hw, Matrix.submatrix_mulVec_equiv]
    simp only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  have hn : ‖WithLp.toLp 2 ((Q *ᵥ v) ∘ e.symm)‖ = ‖WithLp.toLp 2 (Q *ᵥ v)‖ :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map
      (WithLp.toLp 2 (Q *ᵥ v))
  change ‖WithLp.toLp 2 (Q *ᵥ v)‖ ^ 2 = _
  rw [← labelProj_compressedSite_submatrix β X R k l]
  change ‖WithLp.toLp 2 (Q *ᵥ v)‖ ^ 2 =
    ‖WithLp.toLp 2 (Q.submatrix e.symm e.symm *ᵥ w)‖ ^ 2
  rw [hmul, hn]

end GeneralAuxiliary

variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (X : Finset V) (k : ℕ)

/-- The auxiliary projection mass of the actual compressed selected state is
exactly the mass appearing in the Schmidt–Bell theorem, with the same label.
In particular, a label sequence already chosen there can be retained without
any reselection. The equality also holds for zero copies and zero selected mass.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 255–281 and 332–354. -/
theorem norm_sq_labelProj_compressedTypicalSite_prod
    (Ω : EuclideanSpace ℂ ((v : V) → β v))
    (E : Finset (FiniteProduct.Configuration β X))
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    ‖toEuclideanLin
        (labelProj (subsystemPerm k
          (FiniteProduct.compressedSiteSpace β X (Fin E.card)) {none}) l)
        (WithLp.toLp 2
          (fun x : Config k (FiniteProduct.compressedSiteSpace β X (Fin E.card)) ↦
            ∏ j, ψ ((fun v ↦ x j (some v)), x j none)))‖ ^ 2 =
      ‖WithLp.toLp 2
        (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
            (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
            labelProj (copyPerm (Fin E.card) k) l) *ᵥ
          (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) × (Fin k → Fin E.card) ↦
            ∏ j, ψ (x.1 j, x.2 j)))‖ ^ 2 := by
  intro ΩX ψ
  exact norm_sq_labelProj_compressedSite_prod β X (Fin E.card) k
    (fun x ↦ ψ (x.2, x.1)) l

end TensorPower
