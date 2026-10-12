/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellPinnedTreeAction
import QICLean.Representation.ReplicaPinnedTreeExpectation
import Mathlib.Data.List.Forall2

/-!
# The ordered product of actual band roots on the Bell pin

The same weighted mean tree is evaluated in every band. Its original and
exterior roots intertwine through the actual Bell-inserted symmetric operator;
this property is preserved by their ordered product. Cross-status nesting
of the physical bands makes the exterior product positive definite by the
existing pinned-tree factorization.

The conclusion does not assert positivity of the unrestricted original
product. Real powers of that product require its actual symmetric restriction,
which is a separate step. All weights here remain those of the original full
site family, and the inserted vector is arbitrary.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 20–37, 299–308 and 370–381,
  `comparator:nesting` and `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open Matrix PermutationRepresentation FiniteProduct
open scoped ComplexOrder MatrixOrder

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R
local notation "ιe" => compressedSiteSpace β X R

/-- The actual ordered original and exterior band products have the same
pinned action. The exterior product is positive definite by the actual
cross-band nesting, rather than by a supplied positivity premise.

Source: area-law manuscript, `07-comparators.tex`, lines 20–37, 299–308
and 370–381, `comparator:nesting` and `comparator:pinned-metric`. -/
theorem replicaMetric_bandProduct_bellPin {S : Type*}
    [∀ v, Nonempty (ι₀ v)] {t : ℝ} (ht : 0 ≤ t) (k K : ℕ)
    (U Y : S → Fin K → Finset V)
    (hdisj : ∀ j g, Disjoint (U j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h)
    (b : (Configuration β X × C) → ℂ) (T : Matrix.MeanTree S) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe (Configuration β X × C) k b).submatrix e id
    let Pe := symProj (copyPerm ((v : Option ↥(Xᶜ)) → ιe v) k)
    let P := J * Pe * Jᴴ
    let W := replicaMetric ι₀ t k
    let Q := fun j g ↦ insert (some none)
      ((X ∪ U j g).image fun v ↦ some (some v))
    let F := fun j g ↦ insert none
      (((X ∪ (U j g ∪ Y j g))ᶜ).image fun v ↦ some (some v))
    let E := fun Z : Finset V ↦ (Z \ X).image fun v ↦ some (some v)
    let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (E (Y j g))) ^ 2
    let D := fun j g ↦ ((W (E (U j g)))⁻¹ *
      (W (E (U j g ∪ Y j g)))⁻¹ * W (E (Y j g))) ^ 2
    let M := (List.ofFn fun g ↦ T.eval (A · g)).prod
    let N := (List.ofFn fun g ↦ T.eval (D · g)).prod
    N.PosDef ∧ Commute M P ∧ Commute N P ∧ M * P = P * N := by
  classical
  intro e J Pe P W Q F E A D M N
  have hband (g : Fin K) :
      Commute (T.eval (A · g)) P ∧ Commute (T.eval (D · g)) P ∧
        T.eval (A · g) * P = P * T.eval (D · g) := by
    have h := replicaMetric_meanTree_bellPin β X C R ht k
      (U · g) (Y · g) (hdisj · g) b T
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hMP : Commute M P := Commute.list_prod_left _ _
    (List.forall_mem_ofFn_iff.mpr fun g ↦ (hband g).1)
  have hNP : Commute N P := Commute.list_prod_left _ _
    (List.forall_mem_ofFn_iff.mpr fun g ↦ (hband g).2.1)
  have hMN : M * P = P * N := by
    apply List.rel_prod (R := fun A D ↦ A * P = P * D) (by simp) ?_ ?_
    · intro a d had a' d' had'
      rw [mul_assoc, had', ← mul_assoc, had, mul_assoc]
    · apply List.forall₂_iff_get.mpr
      refine ⟨by simp, ?_⟩
      intro i hi hi'
      simpa using (hband ⟨i, by simpa using hi⟩).2.2
  have hEunion (Z Z' : Finset V) : E (Z ∪ Z') = E Z ∪ E Z' := by
    simp only [E, Finset.union_sdiff_distrib, Finset.image_union]
  have hEmono {Z Z' : Finset V} (h : Z ⊆ Z') : E Z ⊆ E Z' :=
    Finset.image_subset_image (Finset.sdiff_subset_sdiff_left X h)
  have hdisjE (j : S) (g : Fin K) : Disjoint (E (U j g)) (E (Y j g)) := by
    apply Finset.disjoint_left.mpr
    intro o ho h'o
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ho
    obtain ⟨y, hy, hyu⟩ := Finset.mem_image.mp h'o
    have hyu' : y = u := Option.some.inj (Option.some.inj hyu)
    subst y
    exact Finset.disjoint_left.mp (hdisj j g) (Finset.mem_sdiff.mp hu).1
      (Finset.mem_sdiff.mp hy).1
  have hnestE (j j' : S) (g h : Fin K) (hgh : g < h) :
      E (U j g) ∪ E (Y j g) ⊆ E (U j' h) := by
    rw [← hEunion]
    exact hEmono (hnest j j' g h hgh)
  have hleaf (j : S) : (List.ofFn (D j)).prod.PosDef := by
    simpa only [D, W, hEunion] using posDef_replicaPinnedLeaf ι₀ ht k K
      (fun g ↦ E (U j g)) (fun g ↦ E (Y j g)) (hdisjE j)
      (fun g h hgh ↦ hnestE j j g h hgh)
  have hfactor : T.eval (fun j ↦ (List.ofFn (D j)).prod) = N := by
    simpa only [D, N, W, hEunion] using replicaPinnedTree_eval_eq_prod ι₀ ht k K
      (fun j g ↦ E (U j g)) (fun j g ↦ E (Y j g)) hdisjE hnestE T
  refine ⟨?_, hMP, hNP, hMN⟩
  rw [← hfactor]
  exact Matrix.MeanTree.posDef_eval hleaf T

end TensorPower
