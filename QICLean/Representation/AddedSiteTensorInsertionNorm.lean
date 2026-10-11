/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.AddedSiteTensorInsertion
import QICLean.Algebra.MatrixUnitaryBetween
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# The Gram matrix of a tensor-power insertion

Inserting the same vector at one additional site in each copy multiplies
inner products by the corresponding power of its squared norm. In particular,
the insertion of a unit vector is an isometry. The old coordinates remain
literal coordinates throughout, and no coordinate set is assumed nonempty.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 283–308, at manuscript
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u v

noncomputable section

open Matrix
open scoped BigOperators

namespace TensorPower

variable {F : Type v} [Fintype F] [DecidableEq F]
variable (ι : F → Type u) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (A : Type u) [Fintype A] [DecidableEq A]

/-- Separate the added coordinate from the original coordinates in every
copy, using the standard equivalences for dependent functions.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
def addedSiteConfigEquiv (k : ℕ) :
    Config k (addedSiteSpace ι A) ≃ (Fin k → A) × Config k ι :=
  (Equiv.piCongrRight fun _ : Fin k ↦
    Equiv.piOptionEquivProd (β := addedSiteSpace ι A)).trans
      (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ A)
        (fun _ ↦ (f : F) → ι f))

omit [DecidableEq A] in
/-- The actual insertion has scalar Gram matrix. The formula includes zero
copies and empty coordinate sets.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
theorem addedSiteInsertion_conjTranspose_mul (k : ℕ) (b : A → ℂ) :
    (addedSiteInsertion ι A k b)ᴴ * addedSiteInsertion ι A k b =
      (∑ a, star (b a) * b a) ^ k • (1 : Matrix (Config k ι) (Config k ι) ℂ) := by
  classical
  let : DecidableEq (Config k ι) := fun y z ↦ Classical.propDecidable (y = z)
  have hsum : (∑ a : Fin k → A, star (∏ j, b (a j)) * ∏ j, b (a j)) =
      (∑ a, star (b a) * b a) ^ k := by
    simp_rw [star_prod, ← Finset.prod_mul_distrib]
    exact (Fintype.sum_pow (fun a ↦ star (b a) * b a) k).symm
  ext y z
  change (∑ x, star (addedSiteInsertion ι A k b x y) *
    addedSiteInsertion ι A k b x z) = _
  calc
    _ = ∑ aw : (Fin k → A) × Config k ι,
        star ((∏ j, b (aw.1 j)) * if aw.2 = y then 1 else 0) *
          ((∏ j, b (aw.1 j)) * if aw.2 = z then 1 else 0) := by
      exact Fintype.sum_equiv (addedSiteConfigEquiv ι A k) _ _ (fun _ ↦ rfl)
    _ = (∑ a : Fin k → A, star (∏ j, b (a j)) * ∏ j, b (a j)) *
        (if y = z then 1 else 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      simp [ite_mul, apply_ite, eq_comm]
      by_cases h : y = z <;> simp [h]
    _ = _ := by
      rw [hsum]
      by_cases h : y = z <;> simp [Matrix.smul_apply, smul_eq_mul, h]

omit [DecidableEq A] in
/-- A unit vector inserted at the additional site gives an actual rectangular
isometry, without a supplied isometry hypothesis or a nonempty-site premise.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
theorem isIsometry_addedSiteInsertion (k : ℕ) (b : A → ℂ)
    (hb : ‖WithLp.toLp 2 b‖ = 1) :
    Matrix.IsIsometry (addedSiteInsertion ι A k b) := by
  have hnorm : (∑ a, star (b a) * b a) = 1 := by
    calc
      _ = inner ℂ (WithLp.toLp 2 b) (WithLp.toLp 2 b) := by
        simp only [EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply]
        exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _
      _ = (‖WithLp.toLp 2 b‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
      _ = 1 := by rw [hb]; simp
  change (addedSiteInsertion ι A k b)ᴴ * addedSiteInsertion ι A k b = 1
  rw [addedSiteInsertion_conjTranspose_mul, hnorm]
  simp

end TensorPower
