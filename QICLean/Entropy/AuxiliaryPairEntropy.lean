/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RegionEntropy

/-!
# The entropy cancellation in the auxiliary-pair comparison

For a pure vector on a physical partition `X, U, Y, V`, the two regional
entropy expressions occurring before and after the Bell projection differ
by an exact sum of mutual informations. Pure-complement equality proves
this cancellation. For a unit vector, the pre-comparison expression is
nonnegative by subadditivity.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 176–203, `comparator:entropy-identity`, at
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
All entropies are those of the actual regional reduced matrices.

Independently formalized; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Labels: comparator:entropy-identity, comparator:sharp-lower.
-/

namespace ManyBody
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (β : ι → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
private theorem entropy_partition (ψ : EuclideanSpace ℂ ((v : ι) → β v))
    (R T : Finset ι) (hd : Disjoint R T) (hc : R ∪ T = Finset.univ) :
    regionEntropy ψ R = regionEntropy ψ T := by
  have hi : IsCompl R T := IsCompl.of_eq (Finset.disjoint_iff_inter_eq_empty.mp hd) hc
  rw [← hi.compl_eq, regionEntropy_compl]
/-- The exact physical entropy cancellation in the auxiliary-pair comparison.
OpenAI area-law manuscript, `07-comparators.tex`, lines 176–203,
`comparator:entropy-identity`. The expressions are evaluated on the same actual
pure vector; no normalization is needed for this balanced identity. -/
theorem auxiliaryPair_regionEntropyIdentity (ψ : EuclideanSpace ℂ ((v : ι) → β v))
    (X U Y V : Finset ι)
    (hXU : Disjoint X U) (hXY : Disjoint X Y) (hXV : Disjoint X V)
    (hUY : Disjoint U Y) (hUV : Disjoint U V) (hYV : Disjoint Y V)
    (hc : X ∪ U ∪ Y ∪ V = Finset.univ) :
    2 * regionEntropy ψ X +
      (regionEntropy ψ (X ∪ U) + regionEntropy ψ V - regionEntropy ψ Y) -
      (regionEntropy ψ U + regionEntropy ψ (U ∪ Y) - regionEntropy ψ Y) =
        regionMutualInformation ψ X V + regionMutualInformation ψ X (Y ∪ V) := by
  have hXU_YV : regionEntropy ψ (X ∪ U) = regionEntropy ψ (Y ∪ V) := by
    apply entropy_partition β ψ
    · simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
      exact ⟨⟨hXY, hUY⟩, ⟨hXV, hUV⟩⟩
    · simpa only [Finset.union_assoc] using hc
  have hUY_XV : regionEntropy ψ (U ∪ Y) = regionEntropy ψ (X ∪ V) := by
    apply entropy_partition β ψ
    · simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
      exact ⟨⟨hXU.symm, hXY.symm⟩, ⟨hUV, hYV⟩⟩
    · simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hc
  have hU_XYV : regionEntropy ψ U = regionEntropy ψ (X ∪ (Y ∪ V)) := by
    apply entropy_partition β ψ
    · simp only [Finset.disjoint_union_right]
      exact ⟨hXU.symm, hUY, hUV⟩
    · simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hc
  unfold regionMutualInformation
  rw [hXU_YV, hUY_XV, hU_XYV]
  ring

/-- Nonnegativity of the physical pre-comparison entropy expression.
OpenAI area-law manuscript, `07-comparators.tex`, lines 176–187,
`comparator:sharp-lower`. Pure-complement equality turns this expression into
mutual information of the disjoint regions `X ∪ U` and `V`. -/
theorem auxiliaryPair_pre_nonneg (ψ : EuclideanSpace ℂ ((v : ι) → β v)) (hψ : ‖ψ‖ = 1)
    (X U Y V : Finset ι) (hXY : Disjoint X Y) (hXV : Disjoint X V)
    (hUY : Disjoint U Y) (hUV : Disjoint U V) (hYV : Disjoint Y V)
    (hc : X ∪ U ∪ Y ∪ V = Finset.univ) :
    0 ≤ regionEntropy ψ (X ∪ U) + regionEntropy ψ V
        - regionEntropy ψ Y := by
  have hcompl : regionEntropy ψ ((X ∪ U) ∪ V) = regionEntropy ψ Y := by
    apply entropy_partition β ψ
    · simp only [Finset.disjoint_union_left]
      exact ⟨⟨hXY, hUY⟩, hYV.symm⟩
    · simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hc
  have hsub := regionEntropy_union_le β ψ hψ (X ∪ U) V
    (Finset.disjoint_union_left.mpr ⟨hXV, hUV⟩)
  rw [hcompl] at hsub
  linarith
end ManyBody
