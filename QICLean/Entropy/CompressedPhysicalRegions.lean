/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CompressedTypicalSiteCoordinates
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Pairwise

/-!
# Physical regions and their actual compressed-state thresholds

An exterior site is either the auxiliary site or an original physical site
outside the selected region. Extracting physical sites discards the former
and retains the latter. Extraction recovers every original region disjoint
from the selected region. Lifting regions preserves inclusion and hence
preserves a nested list; every lifted region is disjoint from the auxiliary
site.

The cutoff threshold on an arbitrary exterior region is defined from its
extracted physical region and the original state's actual selected mass.
Consequently the threshold on a lifted physical region is precisely the
threshold prescribed by the manuscript, with no separate threshold data.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 56–67 and 320–354,
  `comparator:rough-overlap`, source commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped ComplexOrder

noncomputable section

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Retain the original physical sites of an exterior region and discard
its auxiliary site.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 56–67 and 332–343. -/
def extractExteriorRegion (X : Finset V) (D : Finset (Option ↥(Xᶜ))) : Finset V :=
  D.biUnion fun f ↦ match f with
    | none => ∅
    | some v => {(v : V)}

/-- Extracting a lifted physical region recovers that same region whenever
it is disjoint from the selected region.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 56–67 and 332–343. -/
theorem extractExteriorRegion_exteriorRegion (X B : Finset V) (hXB : Disjoint X B) :
    extractExteriorRegion X (exteriorRegion X B) = B := by
  ext v
  simp only [extractExteriorRegion, Finset.mem_biUnion]
  constructor
  · rintro ⟨f, hf, hv⟩
    cases f with
    | none => simp at hv
    | some w =>
      have hw : (w : V) ∈ B := by simpa [exteriorRegion] using hf
      have hvw : v = (w : V) := Finset.mem_singleton.mp hv
      exact hvw.symm ▸ hw
  · intro hv
    let w : ↥(Xᶜ) := ⟨v, Finset.mem_compl.mpr
      (fun hx ↦ Finset.disjoint_left.mp hXB hx hv)⟩
    refine ⟨some w, ?_, ?_⟩
    · simpa [exteriorRegion, w] using hv
    · exact Finset.mem_singleton_self v

/-- Lifting physical regions to exterior sites preserves inclusion.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 56–67 and 332–343. -/
theorem monotone_exteriorRegion (X : Finset V) : Monotone (exteriorRegion X) := by
  classical
  intro B C hBC
  apply Finset.monotone_filter_right
  intro f _ hf
  cases f with
  | none => exact hf
  | some v => exact hBC hf

/-- Every lifted physical region is disjoint from the auxiliary site.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 332–347. -/
theorem exteriorRegion_disjoint_auxiliary (X B : Finset V) :
    Disjoint (exteriorRegion X B) {none} := by
  simp [exteriorRegion]

/-- A nested list of original physical regions remains nested after lifting
to the actual exterior site family.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 56–67 and 332–343. -/
theorem pairwise_exteriorRegion (X : Finset V) (regions : List (Finset V))
    (hnested : regions.Pairwise fun B C ↦ B ⊆ C ∨ C ⊆ B) :
    (regions.map (exteriorRegion X)).Pairwise fun D F ↦ D ⊆ F ∨ F ⊆ D := by
  rw [List.pairwise_map]
  exact hnested.imp fun {B C} h ↦
    h.imp (fun hBC ↦ monotone_exteriorRegion X hBC)
      (fun hCB ↦ monotone_exteriorRegion X hCB)

variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The actual regional cutoff threshold, determined by the original vector,
the selected spectral indices, and the extracted physical region.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 332–343. -/
def compressedRegionalThreshold
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
    (E : Finset (Configuration β X)) (k : ℕ) (D : Finset (Option ↥(Xᶜ))) : ℝ :=
  (k : ℝ) * (entropy β Ω (extractExteriorRegion X D) /
    (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E + 1)

/-- On an actual lifted physical region, the canonical threshold is the
original regional entropy divided by the selected mass, plus one per copy.
The subsequent cutoff estimate uses this identity with positive selected mass.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 332–343. -/
theorem compressedRegionalThreshold_exteriorRegion
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X B : Finset V)
    (hXB : Disjoint X B) (E : Finset (Configuration β X)) (k : ℕ) :
    compressedRegionalThreshold β Ω X E k (exteriorRegion X B) =
      (k : ℝ) * (entropy β Ω B /
        (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E + 1) := by
  simp only [compressedRegionalThreshold, extractExteriorRegion_exteriorRegion X B hXB]

end FiniteProduct
