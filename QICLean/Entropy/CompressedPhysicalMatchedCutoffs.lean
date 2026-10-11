/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CompressedPhysicalRegions
import QICLean.Representation.MatchedSchurCutoffs

/-!
# Matched cutoffs in the original physical dimensions

The exterior-site lift preserves symmetric differences. For physical
regions disjoint from the selected region, its regional configurations
are exactly the original physical configurations. In particular, the
difference dimension in the nested-label estimate is the original
physical difference dimension, without an auxiliary multiplicity.

The final statement applies the matched-cutoff estimate to the same
Bell-range common-cutoff vector through its already established regional
range equations. Both its entropy bound and its difference-dimension bound
are stated on the original physical sites. No coordinate equality, new
vector, or new auxiliary label is supplied or selected.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 240–247 and 356–365,
  `comparator:actual-cutoffs`, manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix Kronecker symmDiff
open Matrix PermutationRepresentation TensorPower

universe u

noncomputable section

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Lifting to the actual exterior sites preserves symmetric difference,
even before imposing disjointness from the selected region.
Source: `07-comparators.tex`, lines 240–247 and 356–365. -/
theorem exteriorRegion_symmDiff (X B Q : Finset V) :
    exteriorRegion X (B ∆ Q) = exteriorRegion X B ∆ exteriorRegion X Q := by
  ext f
  cases f <;> simp [exteriorRegion, Finset.mem_symmDiff]

section GeneralDimension

variable (β : V → Type u) [∀ v, Fintype (β v)]

/-- The dimension of the difference of two lifted physical regions is
exactly the original physical difference dimension. The auxiliary site
does not occur. Source: `07-comparators.tex`, lines 356–365. -/
theorem card_configuration_exteriorRegion_symmDiff (X B Q : Finset V)
    (R : Type u) [Fintype R] (hXB : Disjoint X B) (hXQ : Disjoint X Q) :
    Fintype.card (Configuration (compressedSiteSpace β X R)
      (exteriorRegion X B ∆ exteriorRegion X Q)) =
        Fintype.card (Configuration β (B ∆ Q)) := by
  have hXD : Disjoint X (B ∆ Q) :=
    (Finset.disjoint_union_right.mpr ⟨hXB, hXQ⟩).mono_right
      Finset.symmDiff_subset_union
  rw [← exteriorRegion_symmDiff]
  exact Fintype.card_congr (exteriorRegionEquiv β X (B ∆ Q) R hXD)

end GeneralDimension

variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
  (E : Finset (Configuration β X)) (k : ℕ)

local notation "ι" => compressedSiteSpace β X (Fin E.card)
local notation "z" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian (reducedPure_posSemidef β Ω X)) E
local notation "L" => Fin k → Configuration β X × E

/-- The same common-cutoff vector satisfies the actual matched-region
cutoff, with the entropy and excess-dimension bounds stated on the
original physical sites. The premise `hcuts` is exactly the already
established family of range equations; only its member `B` is used.
No relation with other target regions or other imposed cutoffs is needed.

Source: `07-comparators.tex`, lines 332–365,
`comparator:rough-overlap` and `comparator:actual-cutoffs`. -/
theorem toEuclideanLin_compressedPhysicalCutoff_of_matched
    (regions : List (Finset V)) {B Q : Finset V} (hB : B ∈ regions)
    (hXB : Disjoint X B) (hXQ : Disjoint X Q) (hnested : B ⊆ Q ∨ Q ⊆ B)
    (hz : 0 < z) {Bsh Bexc : ℝ}
    (hsh : entropy β Ω B ≤ Bsh)
    (hexc : 1 + Real.log (Fintype.card (Configuration β (B ∆ Q))) ≤ Bexc)
    (φ : EuclideanSpace ℂ (L × Config k ι))
    (hcuts : ∀ C ∈ regions,
      toEuclideanLin
        ((1 : Matrix L L ℂ) ⊗ₖ
          labelCutoff (subsystemPerm k ι (exteriorRegion X C))
            (compressedRegionalThreshold β Ω X E k (exteriorRegion X C))) φ = φ) :
    toEuclideanLin
      ((1 : Matrix L L ℂ) ⊗ₖ
        labelCutoff (subsystemPerm k ι (exteriorRegion X Q))
          ((k : ℝ) * (Bsh / z + Bexc))) φ = φ := by
  have hφ := hcuts B hB
  rw [compressedRegionalThreshold_exteriorRegion β Ω X B hXB E k] at hφ
  have hmatch : exteriorRegion X B ⊆ exteriorRegion X Q ∨
      exteriorRegion X Q ⊆ exteriorRegion X B :=
    hnested.imp (monotone_exteriorRegion X) (monotone_exteriorRegion X)
  have hexc' : 1 + Real.log
      (Fintype.card (Configuration ι (exteriorRegion X B ∆ exteriorRegion X Q))) ≤ Bexc := by
    rw [card_configuration_exteriorRegion_symmDiff β X B Q (Fin E.card) hXB hXQ]
    exact hexc
  exact toEuclideanLin_labelCutoff_of_matched ι k hmatch hz hsh hexc' φ hφ

end FiniteProduct
