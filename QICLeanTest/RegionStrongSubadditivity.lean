/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.RegionStrongSubadditivity

/-! Regression examples for regional information inequalities. -/

namespace RegionStrongSubadditivityTest

/-- The information inequalities do not need normalization: this product
vector has norm two. -/
private noncomputable def scaledProduct : EuclideanSpace ℂ (Fin 3 → Fin 2) :=
  EuclideanSpace.single (fun _ ↦ 0) 2

example : ‖scaledProduct‖ = 2 := by
  simp [scaledProduct]

example : 0 ≤ ManyBody.conditionalMutualInformation (fun _ : Fin 3 ↦ Fin 2)
    scaledProduct {0} {1} {2} :=
  ManyBody.conditionalMutualInformation_nonneg _ _ _ _ _
    (by decide) (by decide) (by decide)

/-- A nontrivial intersection and union of physical regions, with unequal
local basis dimensions. -/
private def localDimension (v : Fin 3) : ℕ := if v = 0 then 2 else if v = 1 then 3 else 5

example (ψ : EuclideanSpace ℂ ((v : Fin 3) → Fin (localDimension v))) :
    ManyBody.regionEntropy ψ {0, 1, 2} +
        ManyBody.regionEntropy ψ {1} ≤
      ManyBody.regionEntropy ψ {0, 1} +
        ManyBody.regionEntropy ψ {1, 2} := by
  have h := ManyBody.regionEntropy_submodular (fun v ↦ Fin (localDimension v)) ψ {0, 1} {1, 2}
  have hu : ({0, 1} : Finset (Fin 3)) ∪ {1, 2} = {0, 1, 2} := by decide
  have hi : ({0, 1} : Finset (Fin 3)) ∩ {1, 2} = {1} := by decide
  simpa only [hu, hi] using h

/-- A proper retained subregion, with a disjoint information target. -/
example (ψ : EuclideanSpace ℂ ((v : Fin 3) → Fin (localDimension v))) :
    ManyBody.regionMutualInformation ψ {0} {2} ≤
      ManyBody.regionMutualInformation ψ {0, 1} {2} :=
  ManyBody.regionMutualInformation_mono_left _ _ _ _ _ (by decide) (by decide)

/-- Empty regions and empty local bases introduce no nonemptiness premise. -/
example : 0 ≤ ManyBody.conditionalMutualInformation (fun _ : Fin 1 ↦ Fin 0)
    (0 : EuclideanSpace ℂ (Fin 1 → Fin 0)) ∅ ∅ ∅ :=
  ManyBody.conditionalMutualInformation_nonneg _ _ _ _ _
    (by simp) (by simp) (by simp)

end RegionStrongSubadditivityTest
