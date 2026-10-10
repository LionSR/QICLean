/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CompressedTypicalSiteCoordinates
import QICLean.Representation.TensorPowerAction

/-!
# Copy coordinates for the compressed auxiliary site

The auxiliary site is `none`; the other sites are the original physical
complement. Collecting the copies gives the physical-complement coordinates
first and the auxiliary coordinates second. This is the order used by the
existing Schmidt–Bell label-sequence theorem, with exactly the same vector.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 240–281 and 332–354,
  source commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped BigOperators Matrix
open Matrix PermutationRepresentation

universe u

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (R : Type u) (k : ℕ)

/-- Collect physical complementary copies first and auxiliary copies second. -/
def exteriorCopyEquiv :
    Config k (FiniteProduct.compressedSiteSpace β X R) ≃
      (Fin k → FiniteProduct.Configuration β Xᶜ) × (Fin k → R) :=
  (Equiv.piCongrRight fun _ : Fin k ↦
    (Equiv.piOptionEquivProd (β := FiniteProduct.compressedSiteSpace β X R)).trans
      (Equiv.prodComm R (FiniteProduct.Configuration β Xᶜ))).trans
        (Equiv.arrowProdEquivProdArrow (Fin k)
          (fun _ ↦ FiniteProduct.Configuration β Xᶜ) (fun _ ↦ R))

/-- The actual auxiliary subsystem action is the ordinary copy action on
the same auxiliary coordinates; every physical coordinate is fixed. -/
theorem exteriorCopyEquiv_subsystemPerm_none (σ : Equiv.Perm (Fin k))
    (x : Config k (FiniteProduct.compressedSiteSpace β X R)) :
    exteriorCopyEquiv β X R k
        (subsystemPerm k (FiniteProduct.compressedSiteSpace β X R) {none} σ x) =
      ((exteriorCopyEquiv β X R k x).1,
        copyPerm R k σ (exteriorCopyEquiv β X R k x).2) := by
  apply Prod.ext
  · funext j v
    change (if some v ∈ ({none} : Finset (Option ↥(Xᶜ))) then
      x (σ⁻¹ j) (some v) else x j (some v)) = x j (some v)
    simp
  · funext j
    change (if none ∈ ({none} : Finset (Option ↥(Xᶜ))) then
      x (σ⁻¹ j) none else x j none) = x (σ⁻¹ j) none
    simp

/-- The literal sitewise tensor power becomes the same product-coordinate
vector used by the Schmidt–Bell theorem. No new vector is selected. -/
theorem exteriorCopyEquiv_prod (χ : R × FiniteProduct.Configuration β Xᶜ → ℂ)
    (x : (Fin k → FiniteProduct.Configuration β Xᶜ) × (Fin k → R)) :
    (∏ j, χ (Equiv.piOptionEquivProd ((exteriorCopyEquiv β X R k).symm x j))) =
      ∏ j, χ (x.2 j, x.1 j) := rfl

variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype R] [DecidableEq R]

/-- Every literal tensor power is symmetric under simultaneous permutations
of its copies, including the actual compressed selected state. -/
theorem compressedSite_prod_mem_symmetricSubspace
    (χ : R × FiniteProduct.Configuration β Xᶜ → ℂ) :
    (fun x : Config k (FiniteProduct.compressedSiteSpace β X R) ↦
      ∏ j, χ (Equiv.piOptionEquivProd (x j))) ∈
        symmetricSubspace k (FiniteProduct.compressedSiteSpace β X R) := by
  intro σ
  rw [permOp_mulVec]
  funext x
  change (∏ j, χ (Equiv.piOptionEquivProd (x (σ j)))) =
    ∏ j, χ (Equiv.piOptionEquivProd (x j))
  exact Equiv.prod_comp σ (fun j ↦ χ (Equiv.piOptionEquivProd (x j)))

end TensorPower
