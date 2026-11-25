/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.BandMetric.Energy
import QICLean.ManyBody.Replica.BandMetric.MoveEntropy
import QICLean.ManyBody.Replica.Symbol.CoherentMeasure

/-!
# The entropy of a split of a designated support

A designated support `B` is split by a partition `(P, Y, F)` of the tensor factors when it
meets `Y` and exactly one of `P` and `F`. Its split entropy `splitBandEta` is the conditional
mutual information of `B ∩ Y` with the side it does not meet, given the side it meets
(area-law paper, `06-transport.tex`, lines 336–347). The split entropy `splitEta` of a term at
a terminal leaf of transport data is the split entropy of its exceptional band.

This file proves:

* the split entropy is nonnegative, and for a unit vector it is at most twice the logarithmic
  dimension `log (e · dim B)` of the support, whatever the dimensions of the other factors;
* the sum of the entropies of the two moves of `B ∩ Y`, each counted when `B` meets both `Y`
  and the receiving side, is the split entropy when `B` is split and zero when `B` lies in
  one part;
* at a terminal leaf, the split entropy of a term is continuous in the one-copy vector,
  measurable on the unit sphere, zero when the leaf is not a split leaf of the term,
  nonnegative, and bounded by `2ℓ` when every split support has logarithmic dimension at
  most `ℓ`.

## Main statements

* `TensorPower.ReplicaTransport.splitBandEta_nonneg`,
  `TensorPower.ReplicaTransport.splitBandEta_le_two_mul_logDim`
* `TensorPower.ReplicaTransport.incidence_sum_eq_splitBandEta`
* `TensorPower.ReplicaTransport.TransportData.continuous_splitEta`,
  `TensorPower.ReplicaTransport.TransportData.measurable_splitEta_sphere`
* `TensorPower.ReplicaTransport.TransportData.splitEta_eq_zero_of_not_mem_splitLeaves`,
  `TensorPower.ReplicaTransport.TransportData.splitEta_nonneg`,
  `TensorPower.ReplicaTransport.TransportData.splitEta_le_two_mul_of_logDim_le`

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `06-transport.tex`, lines 336–347; `08-scanner.tex`, lines 331–337, 431–440 and 503–506.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators
open TensorPower Entropy

noncomputable section

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V]

section SplitBand

variable (n : V → ℕ)

/-- The split entropy of a support in one band of a partition is nonnegative, whichever
side receives. -/
theorem splitBandEta_nonneg (π : PYF V) (hπ : π.IsPartition) (B : Finset V)
    (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) : 0 ≤ splitBandEta n π B θ := by
  classical
  unfold splitBandEta
  split_ifs
  · exact moveEta_nonneg n π hπ (.toP (B ∩ π.Y)) Finset.inter_subset_right θ
  · exact moveEta_nonneg n π hπ (.toF (B ∩ π.Y)) Finset.inter_subset_right θ

/-- For a unit vector, the split entropy of a support `B` is at most twice the logarithmic
dimension of `B`: it is bounded by twice the entropy of `B ∩ Y`. The dimensions of the
factors outside `B` do not enter. -/
theorem splitBandEta_le_two_mul_logDim [∀ v, NeZero (n v)] (π : PYF V) (hπ : π.IsPartition)
    (B : Finset V) (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) (hθ : ‖θ‖ = 1) :
    splitBandEta n π B θ ≤ 2 * logDim n B := by
  classical
  have hYP : Disjoint (B ∩ π.Y) π.P := hπ.1.symm.mono_left Finset.inter_subset_right
  have hYF : Disjoint (B ∩ π.Y) π.F := hπ.2.2.1.mono_left Finset.inter_subset_right
  have hcost : splitBandEta n π B θ ≤
      2 * ManyBody.regionEntropy θ (B ∩ π.Y) := by
    unfold splitBandEta
    split_ifs
    · exact ManyBody.conditionalMutualInformation_le_two_regionEntropy _ θ hθ
        (B ∩ π.Y) π.F π.P hYF hYP
    · exact ManyBody.conditionalMutualInformation_le_two_regionEntropy _ θ hθ
        (B ∩ π.Y) π.P π.F hYP hYF
  exact hcost.trans (mul_le_mul_of_nonneg_left
    (regionEntropy_le_logDim_of_subset n θ hθ Finset.inter_subset_left) (by norm_num))

private theorem not_middle_side_of_contains (π : PYF V) (hπ : π.IsPartition)
    (B : Finset V) (hc : π.Contains B) :
    ¬ ((B ∩ π.Y).Nonempty ∧ ((B ∩ π.P).Nonempty ∨ (B ∩ π.F).Nonempty)) := by
  rintro ⟨⟨x, hx⟩, hs⟩
  obtain ⟨hxB, hxY⟩ := Finset.mem_inter.mp hx
  rcases hc with hP | hY | hF
  · exact Finset.disjoint_left.mp hπ.1 (hP hxB) hxY
  · rcases hs with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact Finset.disjoint_left.mp hπ.1 (Finset.mem_inter.mp hy).2
        (hY (Finset.mem_inter.mp hy).1)
    · exact Finset.disjoint_left.mp hπ.2.2.1 (hY (Finset.mem_inter.mp hy).1)
        (Finset.mem_inter.mp hy).2
  · exact Finset.disjoint_left.mp hπ.2.2.1 hxY (hF hxB)

open Classical in
/-- Let the support `B` lie in one part of a partition `(P, Y, F)` or be split with one
receiving side. Then the entropies of the moves of `B ∩ Y` to `F` and to `P`, each counted
when `B` meets both `Y` and that side, add up to the split entropy of `B` if `B` is split,
and to zero if `B` lies in one part (`06-transport.tex`, lines 336–347; `08-scanner.tex`,
lines 331–337). -/
theorem incidence_sum_eq_splitBandEta (π : PYF V) (hπ : π.IsPartition)
    (B : Finset V) (hcase : π.Contains B ∨ π.SplitsToP B ∨ π.SplitsToF B)
    (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    (if (B ∩ π.F).Nonempty ∧ (B ∩ π.Y).Nonempty then
        moveEta n π (.toF (B ∩ π.Y)) θ else 0) +
      (if (B ∩ π.P).Nonempty ∧ (B ∩ π.Y).Nonempty then
        moveEta n π (.toP (B ∩ π.Y)) θ else 0) =
      if π.Contains B then 0 else splitBandEta n π B θ := by
  classical
  by_cases hc : π.Contains B
  · have hn := not_middle_side_of_contains π hπ B hc
    have hP : ¬ ((B ∩ π.P).Nonempty ∧ (B ∩ π.Y).Nonempty) :=
      fun h => hn ⟨h.2, Or.inl h.1⟩
    have hF : ¬ ((B ∩ π.F).Nonempty ∧ (B ∩ π.Y).Nonempty) :=
      fun h => hn ⟨h.2, Or.inr h.1⟩
    simp only [hP, hF, hc, ↓reduceIte, add_zero]
  · rcases hcase with hc' | hP | hF
    · exact (hc hc').elim
    · have hnF : ¬ (B ∩ π.F).Nonempty := by
        rw [Finset.disjoint_iff_inter_eq_empty.mp hP.2.2]
        simp
      simp only [hc, hP.1, hP.2.1, hnF, false_and, and_self, ↓reduceIte,
        zero_add, splitBandEta, hP, moveEta]
    · have hnP : ¬ (B ∩ π.P).Nonempty := by
        rw [Finset.disjoint_iff_inter_eq_empty.mp hF.2.2]
        simp
      have hnSplitP : ¬ π.SplitsToP B := fun hP => hnP hP.2.1
      simp only [hc, hF.1, hF.2.1, hnP, false_and, and_self, ↓reduceIte,
        add_zero, splitBandEta, hnSplitP, moveEta]

end SplitBand

namespace TransportData

variable {K : ℕ} {H : Type*} {C : H → Type*} {ι : Type*}

/-- The split entropy `η_{i,j}` of a term at a terminal leaf is continuous in the one-copy
vector (`06-transport.tex`, lines 342–347). -/
theorem continuous_splitEta (D : TransportData V K H C) (n : V → ℕ)
    (E : EnergyTerms V n ι) (i : ι) (j : Σ h, Option (C h)) :
    Continuous fun θ : (∀ v, Fin (n v)) → ℂ =>
      D.splitEta E i j ((EuclideanSpace.equiv _ ℂ).symm θ) := by
  unfold splitEta
  exact continuous_finsetSum _ fun g _ => continuous_splitBandEta _ _

/-- At a terminal leaf that is not a split leaf of a term, the split entropy of the term
vanishes identically: the sum over exceptional bands is empty (`06-transport.tex`,
lines 342–347). -/
theorem splitEta_eq_zero_of_not_mem_splitLeaves [Fintype H] [∀ h, Fintype (C h)]
    {n : V → ℕ} (D : TransportData V K H C) (E : EnergyTerms V n ι)
    {i : ι} {j : Σ h, Option (C h)}
    (hj : j ∉ D.splitLeaves E i) (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    D.splitEta E i j θ = 0 := by
  classical
  simp [splitEta, D.forall_contains_of_not_mem_splitLeaves E hj]

variable (n : V → ℕ) (D : TransportData V K H C) (E : EnergyTerms V n ι)

/-- The split entropy is nonnegative at every terminal leaf of admissible transport
data. -/
theorem splitEta_nonneg [DecidableEq H] [∀ h, DecidableEq (C h)] (hD : D.IsAdmissible)
    (i : ι) (j : Σ h, Option (C h)) (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    0 ≤ D.splitEta E i j θ := by
  classical
  unfold splitEta
  exact Finset.sum_nonneg fun g _ =>
    splitBandEta_nonneg n _ (D.isPartition_leafPart' hD j g) _ θ

/-- For admissible transport data with compatible designated supports, the split entropy of
a term at a terminal leaf is at most `2ℓ` on unit vectors, when `ℓ ≥ 0` bounds the logarithmic
dimension of every support having a split leaf (`08-scanner.tex`, lines 431–440 and
503–506). Supports without a split leaf are unconstrained: their split entropy vanishes. -/
theorem splitEta_le_two_mul_of_logDim_le [∀ v, NeZero (n v)] [Fintype H] [DecidableEq H]
    [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (hD : D.IsAdmissible)
    (hcompat : D.SupportCompatible E) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hsupp : ∀ i, (D.splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ)
    (i : ι) (j : Σ h, Option (C h)) (θ : CoherentSphere (∀ v, Fin (n v))) :
    D.splitEta E i j θ.1 ≤ 2 * ℓ := by
  classical
  by_cases hj : j ∈ D.splitLeaves E i
  · obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hj).2
    rw [D.splitEta_eq_splitBandEta E hcompat hg]
    exact (splitBandEta_le_two_mul_logDim n _ (D.isPartition_leafPart hD j g)
      _ θ.1 θ.2).trans (mul_le_mul_of_nonneg_left (hsupp i ⟨j, hj⟩) (by norm_num))
  · rw [D.splitEta_eq_zero_of_not_mem_splitLeaves E hj]
    exact mul_nonneg (by norm_num) hℓ

/-- The split entropy of a term at a terminal leaf, restricted to the unit sphere, is
measurable. -/
theorem measurable_splitEta_sphere (i : ι) (j : Σ h, Option (C h)) :
    Measurable (fun θ : CoherentSphere (∀ v, Fin (n v)) => D.splitEta E i j θ.1) :=
  ((D.continuous_splitEta n E i j).comp continuous_coherentSphere_coe).measurable

end TransportData
end TensorPower.ReplicaTransport
