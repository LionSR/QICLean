/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.SumSitesProduct
import QICLean.ManyBody.Sites.ReplicaSwap

/-!
# The cores of the exchanged doubled vector are uncorrelated

Let `Ω` be a unit vector on the sites `V`, and `Ψ = Ω ⊗ Ω` the doubled vector on the sites
`V ⊕ V`. The exchange `F_R` of the two replicas on a region `R` moves the content of the first
replica on `R` to the second. In `F_R Ψ`, a core `R₀ ⊆ R` and a core `C₀` disjoint from `R`,
both read in the first replica, come from different factors of `Ψ`, so they have no mutual
information.

Moved from TNLean, `TNLean/Lattice/ReplicaSwap.lean` at commit `e41c3b63`
(`mutualInformation_relabelSites_replicaSwap_eq_zero`), restated with the operator of the
exchange on the sites `V ⊕ V`.

## Main results

* `ManyBody.regionMutualInformation_replicaSwap_eq_zero`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, proof of Lemma 3.3 (`lem:reset`), `02-information.tex`, lines 355–365 and 597–616.
-/

open Matrix ManyBody

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype V] in
private theorem mem_disjSum_iff_replicaSwap {R₀ C₀ R : Finset V} (hR₀ : R₀ ⊆ R)
    (hC₀ : Disjoint C₀ R) (w : V ⊕ V) :
    w ∈ C₀.disjSum R₀ ↔ replicaSwap R w ∈ (R₀ ∪ C₀).disjSum ∅ := by
  have hC (v : V) (hv : v ∈ C₀) : v ∉ R := Finset.disjoint_left.mp hC₀ hv
  rcases w with v | v <;> by_cases hv : v ∈ R
  · rw [replicaSwap_inl_of_mem hv]
    simpa using fun h ↦ hC v h hv
  · rw [replicaSwap_inl_of_notMem hv]
    simpa using fun h ↦ absurd (hR₀ h) hv
  · rw [replicaSwap_inr_of_mem hv]
    simpa using fun h ↦ absurd hv (hC v h)
  · rw [replicaSwap_inr_of_notMem hv]
    simpa using fun h ↦ hv (hR₀ h)

/-- **The cores of the exchanged doubled vector are uncorrelated.** For a unit vector `Ω`,
cores `R₀ ⊆ R` and `C₀` disjoint from `R`, both in the first replica, have no mutual
information in `F_R (Ω ⊗ Ω)`. Polynomial PEPS approximation, `02-information.tex`,
lines 355–365. -/
theorem regionMutualInformation_replicaSwap_eq_zero {Ω : EuclideanSpace ℂ (Config fun _ : V ↦ α)}
    (hΩ : ‖Ω‖ = 1) {R R₀ C₀ : Finset V} (hR₀ : R₀ ⊆ R) (hC₀ : Disjoint C₀ R) :
    regionMutualInformation
      (WithLp.toLp 2 (sitePermOp (replicaSwap R) *ᵥ
        WithLp.ofLp (sumSitesProduct (X := fun _ : V ⊕ V ↦ α) Ω Ω)))
      (R₀.disjSum ∅) (C₀.disjSum ∅) = 0 := by
  set Ψ := sumSitesProduct (X := fun _ : V ⊕ V ↦ α) Ω Ω
  rw [sitePermOp_mulVec_eq_relabelVector]
  have hent (D D' : Finset (V ⊕ V)) (hD : ∀ w, w ∈ D ↔ replicaSwap R w ∈ D') :
      regionEntropy
        (relabelVector (X := fun _ : V ⊕ V ↦ α) (X' := fun _ : V ⊕ V ↦ α) (replicaSwap R)
          (fun _ ↦ Equiv.refl α) Ψ) D' = regionEntropy Ψ D := by
    exact regionEntropy_relabel D D' _ hD _ Ψ
  have hswap (S : Finset V) (hS : Disjoint S R) (w : V ⊕ V) :
      w ∈ S.disjSum ∅ ↔ replicaSwap R w ∈ S.disjSum ∅ := by
    have hS' (v : V) (hv : v ∈ S) : v ∉ R := Finset.disjoint_left.mp hS hv
    rcases w with v | v <;> by_cases hv : v ∈ R
    · rw [replicaSwap_inl_of_mem hv]
      simpa using fun h ↦ hS' v h hv
    · rw [replicaSwap_inl_of_notMem hv]
    · rw [replicaSwap_inr_of_mem hv]
      simpa using fun h ↦ hS' v h hv
    · rw [replicaSwap_inr_of_notMem hv]
  have hR₀' (w : V ⊕ V) : w ∈ (∅ : Finset V).disjSum R₀ ↔ replicaSwap R w ∈ R₀.disjSum ∅ := by
    simpa using mem_disjSum_iff_replicaSwap hR₀ (Finset.disjoint_empty_left R) w
  have hunion : R₀.disjSum (∅ : Finset V) ∪ C₀.disjSum ∅ = (R₀ ∪ C₀).disjSum ∅ := by
    ext w
    rcases w with v | v <;> simp
  rw [regionMutualInformation, hunion, hent _ _ hR₀', hent _ _ (hswap C₀ hC₀),
    hent _ _ (mem_disjSum_iff_replicaSwap hR₀ hC₀)]
  have h₁ := regionEntropy_sumSitesProduct (X := fun _ : V ⊕ V ↦ α) hΩ hΩ ∅ R₀
  have h₂ := regionEntropy_sumSitesProduct (X := fun _ : V ⊕ V ↦ α) hΩ hΩ C₀ ∅
  have h₃ := regionEntropy_sumSitesProduct (X := fun _ : V ⊕ V ↦ α) hΩ hΩ C₀ R₀
  have h₀ := regionEntropy_empty (fun _ : V ↦ α) Ω hΩ
  rw [h₁, h₂, h₃, h₀]
  ring

end ManyBody
