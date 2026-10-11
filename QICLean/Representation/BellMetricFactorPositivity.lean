/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellPinnedMetricCoordinates
import QICLean.Representation.ReplicaLaminarBandMetrics

/-!
# Positivity of the actual Bell metric factors

For disjoint physical regions U and Y, the original pin region, the far
region, and the exterior part of Y are pairwise disjoint. Their positive
replica metrics commute, as do their inverses. The resulting squared factor
is positive definite. The corresponding exterior factor is the single-band
case of the existing positive pinned leaf.

Every metric uses the original full-system weights. The conclusion supplies
both positive matrices in the actual Bell coordinate identity. It requires
neither disjointness from X nor a supplied positivity certificate.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 283–308,
  `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open Matrix PermutationRepresentation FiniteProduct
open scoped ComplexOrder

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R

/-- Both literal squared metric factors in the Bell insertion identity are
positive definite when the two physical regions are disjoint. All metrics
retain the original full-system weights.

Source: area-law manuscript, `07-comparators.tex`, lines 299–308,
`comparator:pinned-metric`. -/
theorem posDef_bellMetric_factors [∀ v, Nonempty (ι₀ v)]
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (U Y : Finset V) (hUY : Disjoint U Y) :
    let W := replicaMetric ι₀ t k
    let P := insert (some none) ((X ∪ U).image fun v ↦ some (some v))
    let F := insert none (((X ∪ (U ∪ Y))ᶜ).image fun v ↦ some (some v))
    let E := fun Q : Finset V ↦ (Q \ X).image fun v ↦ some (some v)
    (((W P)⁻¹ * (W F)⁻¹ * W (E Y)) ^ 2).PosDef ∧
      (((W (E U))⁻¹ * (W (E (U ∪ Y)))⁻¹ * W (E Y)) ^ 2).PosDef := by
  classical
  intro W P F E
  have hPF : Disjoint P F := by
    apply Finset.disjoint_left.mpr
    intro o ho h'o
    cases o with
    | none => simp [P] at ho
    | some o =>
        cases o with
        | none => simp [F, Finset.mem_image] at h'o
        | some v =>
            have hp : v ∈ X ∨ v ∈ U := by simpa [P, Finset.mem_image] using ho
            have hf : v ∉ X ∧ v ∉ U ∧ v ∉ Y := by
              simpa [F, Finset.mem_image, not_or] using h'o
            exact hp.elim hf.1 hf.2.1
  have hPY : Disjoint P (E Y) := by
    apply Finset.disjoint_left.mpr
    intro o ho h'o
    cases o with
    | none => simp [P] at ho
    | some o =>
        cases o with
        | none => simp [E, Finset.mem_image] at h'o
        | some v =>
            have hp : v ∈ X ∨ v ∈ U := by simpa [P, Finset.mem_image] using ho
            have hy : v ∈ Y ∧ v ∉ X := by simpa [E, Finset.mem_image] using h'o
            exact hp.elim hy.2 (fun hu ↦ Finset.disjoint_left.mp hUY hu hy.1)
  have hFY : Disjoint F (E Y) := by
    apply Finset.disjoint_left.mpr
    intro o ho h'o
    cases o with
    | none => simp [E, Finset.mem_image] at h'o
    | some o =>
        cases o with
        | none => simp [E, Finset.mem_image] at h'o
        | some v =>
            have hf : v ∉ X ∧ v ∉ U ∧ v ∉ Y := by
              simpa [F, Finset.mem_image, not_or] using ho
            have hy : v ∈ Y ∧ v ∉ X := by simpa [E, Finset.mem_image] using h'o
            exact hf.2.2 hy.1
  have hEUY : Disjoint (E U) (E Y) := by
    apply Finset.disjoint_left.mpr
    intro o ho h'o
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ho
    obtain ⟨y, hy, hyu⟩ := Finset.mem_image.mp h'o
    have hyu' : y = u := Option.some.inj (Option.some.inj hyu)
    subst y
    exact Finset.disjoint_left.mp hUY (Finset.mem_sdiff.mp hu).1
      (Finset.mem_sdiff.mp hy).1
  have hEunion : E (U ∪ Y) = E U ∪ E Y := by
    simp only [E, Finset.union_sdiff_distrib, Finset.image_union]
  let w : IrrepLabel (Equiv.Perm (Fin k)) → ℝ := replicaLabelWeight ι₀ t
  have hinv (Q : Finset (Option (Option V))) : (W Q)⁻¹ =
      labelObservable (subsystemPerm k ι₀ Q) (fun l ↦ (w l)⁻¹) :=
    labelObservable_inv _ (fun l ↦ (replicaLabelWeight_pos ι₀ ht l).ne')
  have hcPF : Commute (W P)⁻¹ (W F)⁻¹ := by
    rw [hinv, hinv]
    exact commute_labelObservables_subsystemPerm_of_laminar ι₀ k
      (Or.inr (Or.inr hPF)) _ _
  have hcPY : Commute (W P)⁻¹ (W (E Y)) := by
    rw [hinv]
    exact commute_labelObservables_subsystemPerm_of_laminar ι₀ k
      (Or.inr (Or.inr hPY)) _ w
  have hcFY : Commute (W F)⁻¹ (W (E Y)) := by
    rw [hinv]
    exact commute_labelObservables_subsystemPerm_of_laminar ι₀ k
      (Or.inr (Or.inr hFY)) _ w
  constructor
  · have hroot := ((posDef_replicaMetric ι₀ ht k P).inv.mul_of_commute
      (posDef_replicaMetric ι₀ ht k F).inv hcPF).mul_of_commute
        (posDef_replicaMetric ι₀ ht k (E Y)) (hcPY.mul_left hcFY)
    exact (hroot.posSemidef.pow 2).posDef_iff_isUnit.mpr (hroot.isUnit.pow 2)
  · simpa only [W, hEunion] using
      posDef_replicaPinnedFactor ι₀ ht k (E U) (E Y) hEUY

end TensorPower
