/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.RegionalReplicaMetric
import Mathlib.Tactic.FinCases

/-!
# The original three regions in the grouped replica metric

Grouping a disjoint physical pair leaves the two auxiliary sites in their
original positions. The three regions used in the inverse-compression
estimate are exactly the first physical region with the first auxiliary,
the remaining physical complement with the second auxiliary, and the
second physical region alone. They form a disjoint cover of all original
sites.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 20–37, 80–110 and 421–456, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Grouped left, far, and middle factors retain the original physical
subsets and auxiliary sites. Source: `07-comparators.tex`, lines 80–110. -/
theorem regionalOriginalRegion_metric_regions (Q Y : Finset V) (hQY : Disjoint Q Y) :
    regionalOriginalRegion Q Y {0, 3} =
      insert (some none) (Q.image fun v => some (some v)) ∧
    regionalOriginalRegion Q Y {2, 4} =
      insert none ((Q ∪ Y)ᶜ.image fun v => some (some v)) ∧
    regionalOriginalRegion Q Y {1} = Y.image (fun v => some (some v)) := by
  classical
  have hd (v : V) : v ∈ Q → v ∈ Y → False := Finset.disjoint_left.mp hQY
  constructor
  · ext v
    rcases v with _ | (_ | v)
    · simp [regionalOriginalRegion, regionalFactorIndex]
    · simp [regionalOriginalRegion, regionalFactorIndex]
    · by_cases hvQ : v ∈ Q <;> by_cases hvY : v ∈ Y <;>
        simp [regionalOriginalRegion, regionalFactorIndex, hvQ, hvY]
  constructor
  · ext v
    rcases v with _ | (_ | v)
    · simp [regionalOriginalRegion, regionalFactorIndex]
    · simp [regionalOriginalRegion, regionalFactorIndex]
    · by_cases hvQ : v ∈ Q <;> by_cases hvY : v ∈ Y <;>
        simp [regionalOriginalRegion, regionalFactorIndex, hvQ, hvY]
  · ext v
    rcases v with _ | (_ | v)
    · simp [regionalOriginalRegion, regionalFactorIndex]
    · simp [regionalOriginalRegion, regionalFactorIndex]
    · by_cases hvQ : v ∈ Q <;> by_cases hvY : v ∈ Y <;>
        simp_all [regionalOriginalRegion, regionalFactorIndex]

/-- The three actual grouped metric regions form a disjoint cover of the
whole physical and auxiliary family. This is a consequence of the region
definition, including when a physical factor is empty.
Source: `07-comparators.tex`, lines 80–110 and 603–615. -/
theorem regionalOriginalRegion_metric_partition (Q Y : Finset V) :
    Disjoint (regionalOriginalRegion Q Y {0, 3}) (regionalOriginalRegion Q Y {1}) ∧
    Disjoint (regionalOriginalRegion Q Y {0, 3}) (regionalOriginalRegion Q Y {2, 4}) ∧
    Disjoint (regionalOriginalRegion Q Y {1}) (regionalOriginalRegion Q Y {2, 4}) ∧
    regionalOriginalRegion Q Y {1} ∪
      (regionalOriginalRegion Q Y {0, 3} ∪ regionalOriginalRegion Q Y {2, 4}) =
      Finset.univ := by
  classical
  have hmem (v : Option (Option V)) (S : Finset (Fin 5)) :
      v ∈ regionalOriginalRegion Q Y S ↔ regionalFactorIndex Q Y v ∈ S := by
    simp [regionalOriginalRegion]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    rw [hmem] at hv hw
    generalize hi : regionalFactorIndex Q Y v = i at hv hw
    fin_cases i <;> simp_all
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    rw [hmem] at hv hw
    generalize hi : regionalFactorIndex Q Y v = i at hv hw
    fin_cases i <;> simp_all
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    rw [hmem] at hv hw
    generalize hi : regionalFactorIndex Q Y v = i at hv hw
    fin_cases i <;> simp_all
  · ext v
    simp only [Finset.mem_union, hmem, Finset.mem_univ, iff_true]
    generalize hi : regionalFactorIndex Q Y v = i
    fin_cases i <;> simp

end TensorPower
