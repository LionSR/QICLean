/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.FiniteProduct
import QICLean.Entropy.OrderedEntropyAlgebra

/-!
# Two-family entropy cancellation

For a normalized pure state on an arbitrary finite product, partition a region
into a remainder and two disjoint ordered families. A bound on each tile's mutual
information with the exterior and all earlier tiles of its own family gives
entropy at most the remainder entropy plus half the sum of those bounds.

No Hamiltonian, spectral gap, geometric separation, smallness condition, nonempty
region, or sign assumption on the error bounds is required. The mutual information
is the actual regional quantum mutual information, identified with the canonical
matrix definition by `FiniteProduct.mutualInformation_eq_matrix`.

## References and provenance

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, Lemma 11.1 (`geometry:cancellation`), immutable source:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`, preprint
`A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026`,
`build/sections/10-geometry.tex`, lines 26–69.

These proofs are independently written from the paper's mathematical argument;
no OpenAI Lean proof code is copied or adapted.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex
Labels: geometry:cancellation.
Provenance-ID: 8760-qic-two-families-01
Downstream declaration:
FiniteProduct.mutualInformation_past_eq_defect
Provenance-ID: 8760-qic-two-families-02
Downstream declaration:
FiniteProduct.orderedFamily_entropy_chain_lower
Provenance-ID: 8760-qic-two-families-03
Downstream declaration:
FiniteProduct.disjoint_exterior_past
Provenance-ID: 8760-qic-two-families-04
Downstream declaration:
FiniteProduct.entropy_le_remainder_add_half_mutualInformation
Provenance-ID: 8760-qic-two-families-05
Downstream declaration:
FiniteProduct.entropy_le_remainder_add_half_sum
-/

open scoped BigOperators

namespace FiniteProduct

open Entropy.OrderedSetFunction

variable {V ι κ : Type*} [Fintype V] [DecidableEq V] [LinearOrder ι] [LinearOrder κ]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The regional mutual information equals the ordered entropy defect. -/
theorem mutualInformation_past_eq_defect (ψ : EuclideanSpace ℂ ((v : V) → β v))
    (B : Finset V) (X : ι → Finset V) (s : Finset ι) (i : ι) :
    mutualInformation β ψ (X i) (B ∪ past X s i) =
      defect (entropy β ψ) B X s i := by
  simp only [mutualInformation, defect, Finset.union_comm (X i)]

/-- Telescoping along an arbitrary finite total order. Each information estimate
uses the whole exterior together with all earlier tiles of the same family. -/
theorem orderedFamily_entropy_chain_lower
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (B : Finset V)
    (X : ι → Finset V) (s : Finset ι) (ε : ι → ℝ)
    (hε : ∀ i ∈ s, mutualInformation β ψ (X i) (B ∪ past X s i) ≤ ε i) :
    entropy β ψ B + (∑ i ∈ s, entropy β ψ (X i)) - (∑ i ∈ s, ε i) ≤
      entropy β ψ (B ∪ s.biUnion X) := by
  apply chain_lower
  simpa only [mutualInformation_past_eq_defect] using hε

private theorem complement_exterior_union (A D U W : Finset V)
    (hA : A = D ∪ U ∪ W) (hDU : Disjoint D U) (hUW : Disjoint U W) :
    (Aᶜ ∪ U)ᶜ = D ∪ W := by
  ext v
  have hdu : v ∈ D → v ∉ U := fun hd hu ↦ Finset.disjoint_left.mp hDU hd hu
  have huw : v ∈ U → v ∉ W := fun hu hw ↦ Finset.disjoint_left.mp hUW hu hw
  simp only [hA, Finset.mem_compl, Finset.mem_union]
  tauto

/-- A tile is disjoint from the exterior and its earlier same-family tiles in a
pairwise-disjoint decomposition. This validates the physical mutual-information
interpretation of each hypothesis below. -/
theorem disjoint_exterior_past (A : Finset V) (X : ι → Finset V) (s : Finset ι)
    (hsub : ∀ i ∈ s, X i ⊆ A) (hX : (s : Set ι).PairwiseDisjoint X)
    (i : ι) (hi : i ∈ s) : Disjoint (X i) (Aᶜ ∪ past X s i) := by
  apply Finset.disjoint_union_right.mpr
  constructor
  · exact Finset.disjoint_left.mpr fun v hv hvc ↦ Finset.mem_compl.mp hvc (hsub i hi hv)
  · rw [past, Finset.disjoint_biUnion_right]
    intro j hj
    obtain ⟨hjs, hji⟩ := Finset.mem_filter.mp hj
    exact hX hi hjs (ne_of_gt hji)

/-- Two-family entropy cancellation with the exact sum of physical mutual
informations. This is the error-free formulation of OpenAI's area-law Lemma 11.1.
The two families may carry different finite total orders. -/
theorem entropy_le_remainder_add_half_mutualInformation
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (A D : Finset V) (X : ι → Finset V) (s : Finset ι)
    (Y : κ → Finset V) (t : Finset κ)
    (hA : A = D ∪ s.biUnion X ∪ t.biUnion Y)
    (hDX : ∀ i ∈ s, Disjoint D (X i))
    (hDY : ∀ j ∈ t, Disjoint D (Y j))
    (hX : (s : Set ι).PairwiseDisjoint X)
    (hY : (t : Set κ).PairwiseDisjoint Y)
    (hXY : ∀ i ∈ s, ∀ j ∈ t, Disjoint (X i) (Y j)) :
    entropy β ψ A ≤ entropy β ψ D + (1 / 2) *
      ((∑ i ∈ s, mutualInformation β ψ (X i) (Aᶜ ∪ past X s i)) +
        ∑ j ∈ t, mutualInformation β ψ (Y j) (Aᶜ ∪ past Y t j)) := by
  have hDU : Disjoint D (s.biUnion X) := (Finset.disjoint_biUnion_right _ _ _).mpr hDX
  have hDW : Disjoint D (t.biUnion Y) := (Finset.disjoint_biUnion_right _ _ _).mpr hDY
  have hUW : Disjoint (s.biUnion X) (t.biUnion Y) := by
    simp only [Finset.disjoint_biUnion_left, Finset.disjoint_biUnion_right]
    intro j hj i hi
    exact hXY i hi j hj
  have hA' : A = D ∪ t.biUnion Y ∪ s.biUnion X := by
    rw [hA, Finset.union_right_comm]
  have hx : entropy β ψ (Aᶜ ∪ s.biUnion X) ≤
      entropy β ψ D + ∑ j ∈ t, entropy β ψ (Y j) := by
    rw [← entropy_compl β ψ (Aᶜ ∪ s.biUnion X),
      complement_exterior_union A D _ _ hA hDU hUW]
    exact union_biUnion_le_sum (entropy β ψ) (entropy_union_le β ψ hψ) D Y t hDY hY
  have hy : entropy β ψ (Aᶜ ∪ t.biUnion Y) ≤
      entropy β ψ D + ∑ i ∈ s, entropy β ψ (X i) := by
    rw [← entropy_compl β ψ (Aᶜ ∪ t.biUnion Y),
      complement_exterior_union A D _ _ hA' hDW hUW.symm]
    exact union_biUnion_le_sum (entropy β ψ) (entropy_union_le β ψ hψ) D X s hDX hX
  have h := two_family_le_half_sum_defect (entropy β ψ) Aᶜ D X s Y t hx hy
  simpa only [entropy_compl, ← mutualInformation_past_eq_defect] using h

/-- OpenAI's area-law Lemma 11.1: the entropy of the region is bounded by the
remainder entropy plus exactly half the sum of the two ordered families' errors.
No nonnegativity assumption is added to either error function. -/
theorem entropy_le_remainder_add_half_sum
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (A D : Finset V) (X : ι → Finset V) (s : Finset ι)
    (Y : κ → Finset V) (t : Finset κ)
    (hA : A = D ∪ s.biUnion X ∪ t.biUnion Y)
    (hDX : ∀ i ∈ s, Disjoint D (X i))
    (hDY : ∀ j ∈ t, Disjoint D (Y j))
    (hX : (s : Set ι).PairwiseDisjoint X)
    (hY : (t : Set κ).PairwiseDisjoint Y)
    (hXY : ∀ i ∈ s, ∀ j ∈ t, Disjoint (X i) (Y j))
    (ε : ι → ℝ) (δ : κ → ℝ)
    (hε : ∀ i ∈ s, mutualInformation β ψ (X i) (Aᶜ ∪ past X s i) ≤ ε i)
    (hδ : ∀ j ∈ t, mutualInformation β ψ (Y j) (Aᶜ ∪ past Y t j) ≤ δ j) :
    entropy β ψ A ≤ entropy β ψ D + (1 / 2) *
      ((∑ i ∈ s, ε i) + ∑ j ∈ t, δ j) := by
  have h := entropy_le_remainder_add_half_mutualInformation β ψ hψ A D X s Y t
    hA hDX hDY hX hY hXY
  have hx := Finset.sum_le_sum hε
  have hy := Finset.sum_le_sum hδ
  linarith only [h, hx, hy]

end FiniteProduct
