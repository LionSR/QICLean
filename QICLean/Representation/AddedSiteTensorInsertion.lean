/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.AddedSiteSpace

/-!
# Inserting a tensor power at an additional site

Adjoin one site with coordinate set A to a finite family of sites. A vector b
at this site gives a rectangular insertion matrix: the new coordinates carry
b in every copy, while the old coordinates are retained literally. Permuting
the copies of the added site together with a subsystem intertwines this
insertion with the copy permutation of the original subsystem. The assertion
holds for arbitrary b, without a normalization or nonvanishing assumption.

The same finite group-algebra element, and hence the same real function of
the irreducible label, acts on the two sides. In particular, a later replica
metric application must use the original full-system label weights on both
sides; no equality with weights recomputed for the enlarged system is asserted.

The family `addedSiteSpace (fun v : Xᶜ ↦ β v) A` agrees definitionally with
`FiniteProduct.compressedSiteSpace β X A`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 283–308, at manuscript
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u v

noncomputable section

open Matrix PermutationRepresentation
open scoped BigOperators

namespace TensorPower

variable {F : Type v}

variable [Fintype F] [DecidableEq F]
variable (ι : F → Type u) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (A : Type u) [Fintype A] [DecidableEq A]

/-- The literal rectangular insertion of b in each copy of the additional
site. The old configuration is retained by a Kronecker delta.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
def addedSiteInsertion (k : ℕ) (b : A → ℂ) :
    Matrix (Config k (addedSiteSpace ι A)) (Config k ι) ℂ := by
  classical
  exact fun x y ↦ (∏ j, b (x j none)) *
    if (fun j f ↦ x j (some f)) = y then 1 else 0

omit [∀ f, DecidableEq (ι f)] [Fintype A] [DecidableEq A] in
/-- Evaluation of the actual insertion matrix is pointwise multiplication
by the new-site tensor power.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
theorem addedSiteInsertion_mulVec (k : ℕ) (b : A → ℂ) (v : Config k ι → ℂ) :
    addedSiteInsertion ι A k b *ᵥ v =
      fun x ↦ (∏ j, b (x j none)) * v (fun j f ↦ x j (some f)) := by
  classical
  funext x
  dsimp only [addedSiteInsertion, Matrix.mulVec, dotProduct]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp only [ite_mul, one_mul, zero_mul]
  let : DecidableEq (Config k ι) := fun y z ↦ Classical.propDecidable (y = z)
  exact Fintype.sum_ite_eq (ι := Config k ι) (fun j f ↦ x j (some f)) v

omit [Fintype F] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  [Fintype A] [DecidableEq A] in
/-- Restricting the actual enlarged permutation to the original sites gives
the original subsystem permutation. -/
private theorem addedSite_restrict_subsystemPerm (k : ℕ) (Q : Finset F)
    (σ : Equiv.Perm (Fin k)) (x : Config k (addedSiteSpace ι A)) :
    (fun j f ↦ subsystemPerm k (addedSiteSpace ι A)
      (insert none (Q.image some)) σ x j (some f)) =
      subsystemPerm k ι Q σ (fun j f ↦ x j (some f)) := by
  funext j f
  by_cases hf : f ∈ Q <;> simp [subsystemPerm, Finset.mem_image, hf]

omit [Fintype F] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  [Fintype A] [DecidableEq A] in
/-- The new-site tensor power is invariant under the literal permutation of
its copies. No property of b is needed. -/
private theorem addedSite_product_subsystemPerm (k : ℕ) (Q : Finset F)
    (σ : Equiv.Perm (Fin k)) (b : A → ℂ)
    (x : Config k (addedSiteSpace ι A)) :
    (∏ j, b (subsystemPerm k (addedSiteSpace ι A)
      (insert none (Q.image some)) σ x j none)) = ∏ j, b (x j none) := by
  simp only [subsystemPerm_apply, Finset.mem_insert_self, ite_true]
  exact Equiv.prod_comp σ.symm (fun j ↦ b (x j none))

/-- The actual insertion intertwines subsystem copy permutations when the
new site is permuted together with the subsystem. This derives the
intertwining from the coordinates, rather than assuming it.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
theorem permOp_mul_addedSiteInsertion (k : ℕ) (Q : Finset F)
    (σ : Equiv.Perm (Fin k)) (b : A → ℂ) :
    permOp (subsystemPerm k (addedSiteSpace ι A) (insert none (Q.image some))) σ *
        addedSiteInsertion ι A k b =
      addedSiteInsertion ι A k b * permOp (subsystemPerm k ι Q) σ := by
  classical
  rw [Matrix.ext_iff_mulVec]
  intro v
  simp only [← Matrix.mulVec_mulVec, addedSiteInsertion_mulVec, permOp_mulVec]
  funext x
  simp only [Function.comp_apply, ← map_inv]
  change (∏ j, b (subsystemPerm k (addedSiteSpace ι A)
      (insert none (Q.image some)) σ⁻¹ x j none)) *
      v (fun j f ↦ subsystemPerm k (addedSiteSpace ι A)
        (insert none (Q.image some)) σ⁻¹ x j (some f)) =
    (∏ j, b (x j none)) *
      v (subsystemPerm k ι Q σ⁻¹ (fun j f ↦ x j (some f)))
  rw [addedSite_product_subsystemPerm, addedSite_restrict_subsystemPerm]

/-- The same element of the finite permutation group algebra intertwines
with the actual added-site insertion. The existing finite-sum formula is used
once; no additional group-algebra induction is required.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
theorem groupAlgebraRep_mul_addedSiteInsertion (k : ℕ) (Q : Finset F)
    (a : MonoidAlgebra ℂ (Equiv.Perm (Fin k))) (b : A → ℂ) :
    groupAlgebraRep
        (subsystemPerm k (addedSiteSpace ι A) (insert none (Q.image some))) a *
        addedSiteInsertion ι A k b =
      addedSiteInsertion ι A k b * groupAlgebraRep (subsystemPerm k ι Q) a := by
  classical
  simp only [groupAlgebraRep_eq_sum, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, permOp_mul_addedSiteInsertion]

/-- Every real label function intertwines with the actual insertion, with
exactly the same function on both sides. This includes the original-system
replica weights without recomputing them on the enlarged family.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
theorem labelObservable_mul_addedSiteInsertion (k : ℕ) (Q : Finset F)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) (b : A → ℂ) :
    labelObservable
        (subsystemPerm k (addedSiteSpace ι A) (insert none (Q.image some))) f *
        addedSiteInsertion ι A k b =
      addedSiteInsertion ι A k b * labelObservable (subsystemPerm k ι Q) f := by
  rw [labelObservable_eq_groupAlgebraRep, labelObservable_eq_groupAlgebraRep]
  exact groupAlgebraRep_mul_addedSiteInsertion ι A k Q _ b

/-- Copy permutations of the original subsystem also intertwine with the
insertion when the new site is left fixed. Here the added tensor coefficient
is unchanged pointwise, without even reordering its factors.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
theorem permOp_mul_addedSiteInsertion_exterior (k : ℕ) (Q : Finset F)
    (σ : Equiv.Perm (Fin k)) (b : A → ℂ) :
    permOp (subsystemPerm k (addedSiteSpace ι A) (Q.image some)) σ *
        addedSiteInsertion ι A k b =
      addedSiteInsertion ι A k b * permOp (subsystemPerm k ι Q) σ := by
  classical
  rw [Matrix.ext_iff_mulVec]
  intro v
  simp only [← Matrix.mulVec_mulVec, addedSiteInsertion_mulVec, permOp_mulVec]
  funext x
  simp only [Function.comp_apply, ← map_inv]
  change (∏ j, b (subsystemPerm k (addedSiteSpace ι A)
      (Q.image some) σ⁻¹ x j none)) *
      v (fun j f ↦ subsystemPerm k (addedSiteSpace ι A)
        (Q.image some) σ⁻¹ x j (some f)) =
    (∏ j, b (x j none)) *
      v (subsystemPerm k ι Q σ⁻¹ (fun j f ↦ x j (some f)))
  have hrest :
      (fun j f ↦ subsystemPerm k (addedSiteSpace ι A)
        (Q.image some) σ⁻¹ x j (some f)) =
      subsystemPerm k ι Q σ⁻¹ (fun j f ↦ x j (some f)) := by
    funext j f
    by_cases hf : f ∈ Q <;> simp [subsystemPerm, Finset.mem_image, hf]
  rw [hrest]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp [subsystemPerm, Finset.mem_image]

/-- The same group-algebra element intertwines with insertion while fixing
the added site. As in the including-site variant, only the existing finite
sum formula is used.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
theorem groupAlgebraRep_mul_addedSiteInsertion_exterior (k : ℕ) (Q : Finset F)
    (a : MonoidAlgebra ℂ (Equiv.Perm (Fin k))) (b : A → ℂ) :
    groupAlgebraRep (subsystemPerm k (addedSiteSpace ι A) (Q.image some)) a *
        addedSiteInsertion ι A k b =
      addedSiteInsertion ι A k b * groupAlgebraRep (subsystemPerm k ι Q) a := by
  classical
  simp only [groupAlgebraRep_eq_sum, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, permOp_mul_addedSiteInsertion_exterior]

/-- Fixing the new site retains exactly the same real label function on the
original subsystem. In particular, the original full-system replica weights
need not be replaced by weights for either coordinate family.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
theorem labelObservable_mul_addedSiteInsertion_exterior (k : ℕ) (Q : Finset F)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) (b : A → ℂ) :
    labelObservable (subsystemPerm k (addedSiteSpace ι A) (Q.image some)) f *
        addedSiteInsertion ι A k b =
      addedSiteInsertion ι A k b * labelObservable (subsystemPerm k ι Q) f := by
  rw [labelObservable_eq_groupAlgebraRep, labelObservable_eq_groupAlgebraRep]
  exact groupAlgebraRep_mul_addedSiteInsertion_exterior ι A k Q _ b

end TensorPower
