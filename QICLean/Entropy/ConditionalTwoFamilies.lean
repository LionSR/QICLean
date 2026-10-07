/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.TwoFamilies
import QICLean.Entropy.FiniteProductConditional

/-!
# Conditional information from two ordered families

Partition a regional system into two ordered families and an exceptional
remainder. For a normalized pure state, its conditional information is bounded
by the first family's information with the original exterior and past, twice
the remainder entropy, and the second family's information with the complementary
exterior and past. Pure-state duality is applied to the whole second-family block
before its forward chain is expanded.

This is the generic entropy step in the proof of OpenAI's *Polynomial PEPS
approximation of gapped square-grid ground states* (September 24, 2026),
Lemma 3.2, `eq:info-tile-cost`, lines 180–222 of `02-information.tex`.
It does not prove the geometric partition or the polylogarithmic cell bound.
All proofs are independently written; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/
build/sections/02-information.tex
Labels: eq:info-tile-cost.
Provenance-ID: 8765-qic-conditional-01
Downstream declaration:
FiniteProduct.conditionalMutualInformation_union_left
Provenance-ID: 8765-qic-conditional-02
Downstream declaration:
FiniteProduct.mutualInformation_le_two_entropy
Provenance-ID: 8765-qic-conditional-03
Downstream declaration:
FiniteProduct.conditionalMutualInformation_le_two_entropy
Provenance-ID: 8765-qic-conditional-04
Downstream declaration:
FiniteProduct.conditionalMutualInformation_biUnion_le_sum
Provenance-ID: 8765-qic-conditional-05
Downstream declaration:
FiniteProduct.target_union_complement_eq_exterior
Provenance-ID: 8765-qic-conditional-06
Downstream declaration:
FiniteProduct.conditionalMutualInformation_le_two_family_mutualInformation
Provenance-ID: 8765-qic-conditional-07
Downstream declaration:
FiniteProduct.conditionalMutualInformation_le_two_family_sum
-/

open scoped BigOperators

namespace FiniteProduct

open Entropy.OrderedSetFunction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The binary conditional-information chain identity for regional entropy
expressions. In the physical application the regions are disjoint. -/
theorem conditionalMutualInformation_union_left
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (X Y C Z : Finset V) :
    conditionalMutualInformation β ψ (X ∪ Y) C Z =
      conditionalMutualInformation β ψ X C Z +
        conditionalMutualInformation β ψ Y C (Z ∪ X) := by
  simp only [conditionalMutualInformation, Finset.union_left_comm, Finset.union_comm]
  ring

/-- Mutual information of disjoint regions is at most twice the first region's
entropy. The proof uses purity and subadditivity, not a dimension estimate. -/
theorem mutualInformation_le_two_entropy
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (X Y : Finset V) (hXY : Disjoint X Y) :
    mutualInformation β ψ X Y ≤ 2 * entropy β ψ X := by
  have hpart : X ∪ (X ∪ Y)ᶜ = Yᶜ := by
    ext v
    have hxy : v ∈ X → v ∉ Y := fun hx hy ↦ Finset.disjoint_left.mp hXY hx hy
    simp only [Finset.mem_union, Finset.mem_compl]
    tauto
  have hdisj : Disjoint X (X ∪ Y)ᶜ :=
    Finset.disjoint_left.mpr fun v hv hw ↦
      Finset.mem_compl.mp hw (Finset.mem_union_left Y hv)
  have h := entropy_union_le β ψ hψ X (X ∪ Y)ᶜ hdisj
  rw [hpart, entropy_compl, entropy_compl] at h
  unfold mutualInformation
  linarith only [h]

/-- An exceptional regional block costs at most twice its own entropy in a
conditional-information chain. -/
theorem conditionalMutualInformation_le_two_entropy
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (D C Z : Finset V) (hDC : Disjoint D C) (hDZ : Disjoint D Z) :
    conditionalMutualInformation β ψ D C Z ≤ 2 * entropy β ψ D :=
  (conditionalMutualInformation_le_mutualInformation_union β ψ hψ D C Z hDZ).trans
    (mutualInformation_le_two_entropy β ψ hψ D (C ∪ Z)
      (Finset.disjoint_union_right.mpr ⟨hDC, hDZ⟩))

/-- The conditional information of an ordered disjoint family is bounded by
its ordinary information with the entire target, exterior and same-family past. -/
theorem conditionalMutualInformation_biUnion_le_sum
    {ι : Type*} [LinearOrder ι]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (C B : Finset V) (X : ι → Finset V) (s : Finset ι)
    (hB : ∀ i ∈ s, Disjoint B (X i)) (hX : (s : Set ι).PairwiseDisjoint X) :
    conditionalMutualInformation β ψ (s.biUnion X) C B ≤
      ∑ i ∈ s, mutualInformation β ψ (X i) (C ∪ B ∪ past X s i) := by
  rw [← sum_conditionalMutualInformation_past β ψ C B X s]
  apply Finset.sum_le_sum
  intro i hi
  have hsub : ∀ j ∈ s, X j ⊆ Bᶜ := by
    intro j hj v hv
    exact Finset.mem_compl.mpr (fun hb ↦ Finset.disjoint_left.mp (hB j hj) hb hv)
  have hdisj : Disjoint (X i) (B ∪ past X s i) := by
    simpa only [compl_compl] using disjoint_exterior_past Bᶜ X s hsub hX i hi
  simpa only [Finset.union_assoc] using
    conditionalMutualInformation_le_mutualInformation_union β ψ hψ (X i) C
      (B ∪ past X s i) hdisj

/-- The target together with the complementary conditioning region is exactly
the forbidden-color-one exterior in the source proof. -/
theorem target_union_complement_eq_exterior (G B C : Finset V)
    (hGC : Disjoint G C) (hBC : Disjoint B C) :
    C ∪ (G ∪ B ∪ C)ᶜ = (G ∪ B)ᶜ := by
  ext v
  have hgc : v ∈ C → v ∉ G := fun hc hg ↦ Finset.disjoint_left.mp hGC hg hc
  have hbc : v ∈ C → v ∉ B := fun hc hb ↦ Finset.disjoint_left.mp hBC hb hc
  simp only [Finset.mem_union, Finset.mem_compl]
  tauto

/-- The conditional two-family entropy bound used in the proof of the PEPS
cell-information lemma. The exterior for the second family is the complement
of the region, original conditioner and target taken together. -/
theorem conditionalMutualInformation_le_two_family_mutualInformation
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (G B C D : Finset V) (X : ι → Finset V) (s : Finset ι)
    (Y : κ → Finset V) (t : Finset κ)
    (hG : G = D ∪ s.biUnion X ∪ t.biUnion Y)
    (hGB : Disjoint G B) (hGC : Disjoint G C) (hBC : Disjoint B C)
    (hDX : ∀ i ∈ s, Disjoint D (X i))
    (hDY : ∀ j ∈ t, Disjoint D (Y j))
    (hX : (s : Set ι).PairwiseDisjoint X)
    (hY : (t : Set κ).PairwiseDisjoint Y)
    (hXY : ∀ i ∈ s, ∀ j ∈ t, Disjoint (X i) (Y j)) :
    conditionalMutualInformation β ψ G C B ≤
      (∑ i ∈ s, mutualInformation β ψ (X i) (C ∪ B ∪ past X s i)) +
        2 * entropy β ψ D +
          ∑ j ∈ t, mutualInformation β ψ (Y j)
            (C ∪ (G ∪ B ∪ C)ᶜ ∪ past Y t j) := by
  let A₀ := s.biUnion X
  let A₁ := t.biUnion Y
  let F := (G ∪ B ∪ C)ᶜ
  have hD₀ : Disjoint D A₀ := (Finset.disjoint_biUnion_right _ _ _).mpr hDX
  have hD₁ : Disjoint D A₁ := (Finset.disjoint_biUnion_right _ _ _).mpr hDY
  have h₀₁ : Disjoint A₀ A₁ := by
    simp only [A₀, A₁, Finset.disjoint_biUnion_left, Finset.disjoint_biUnion_right]
    intro j hj i hi
    exact hXY i hi j hj
  have hDG : D ⊆ G := by
    rw [hG]
    exact Finset.subset_union_left.trans Finset.subset_union_left
  have h₀G : A₀ ⊆ G := by
    rw [hG]
    exact Finset.subset_union_right.trans Finset.subset_union_left
  have h₁G : A₁ ⊆ G := by
    rw [hG]
    exact Finset.subset_union_right
  have h₀B : Disjoint A₀ B := hGB.mono_left h₀G
  have h₁B : Disjoint A₁ B := hGB.mono_left h₁G
  have hDC : Disjoint D C := hGC.mono_left hDG
  have h₀C : Disjoint A₀ C := hGC.mono_left h₀G
  have h₁C : Disjoint A₁ C := hGC.mono_left h₁G
  have hDB₀ : Disjoint D (B ∪ A₀) :=
    Finset.disjoint_union_right.mpr ⟨hGB.mono_left hDG, hD₀⟩
  have h₁Z : Disjoint A₁ (B ∪ A₀ ∪ D) :=
    Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨h₁B, h₀₁.symm⟩, hD₁.symm⟩
  have hCZ : Disjoint C (B ∪ A₀ ∪ D) :=
    Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨hBC.symm, h₀C.symm⟩, hDC.symm⟩
  have h₁F : Disjoint A₁ F := by
    apply Finset.disjoint_left.mpr
    intro v hv hF
    exact Finset.mem_compl.mp hF
      (Finset.mem_union_left C (Finset.mem_union_left B (h₁G hv)))
  have hchain : conditionalMutualInformation β ψ G C B =
      conditionalMutualInformation β ψ A₀ C B +
        conditionalMutualInformation β ψ D C (B ∪ A₀) +
          conditionalMutualInformation β ψ A₁ C (B ∪ A₀ ∪ D) := by
    have hG' : G = (A₀ ∪ D) ∪ A₁ := by
      rw [hG]
      dsimp only [A₀, A₁]
      ac_rfl
    rw [hG', conditionalMutualInformation_union_left,
      conditionalMutualInformation_union_left]
    simp only [Finset.union_assoc]
  have hfirst := conditionalMutualInformation_biUnion_le_sum β ψ hψ C B X s
    ((Finset.disjoint_biUnion_right B s X).mp h₀B.symm) hX
  have hmiddle := conditionalMutualInformation_le_two_entropy β ψ hψ D C
    (B ∪ A₀) hDC hDB₀
  have hdual := conditionalMutualInformation_pure_duality β ψ A₁ C (B ∪ A₀ ∪ D)
    h₁C h₁Z hCZ
  have hcompl : (A₁ ∪ C ∪ (B ∪ A₀ ∪ D))ᶜ = F := by
    dsimp only [F]
    congr 1
    rw [hG]
    dsimp only [A₀, A₁]
    ac_rfl
  have hlast : conditionalMutualInformation β ψ A₁ C (B ∪ A₀ ∪ D) ≤
      ∑ j ∈ t, mutualInformation β ψ (Y j) (C ∪ F ∪ past Y t j) := by
    rw [hdual, hcompl]
    exact conditionalMutualInformation_biUnion_le_sum β ψ hψ C F Y t
      ((Finset.disjoint_biUnion_right F t Y).mp h₁F.symm) hY
  rw [hchain]
  exact add_le_add (add_le_add hfirst hmiddle) hlast

/-- Conditional two-family cancellation with real pointwise information errors.
There is no sign or smallness requirement on the supplied errors. The exceptional
cost is twice the remainder entropy, rather than a separately assumed dimension bound. -/
theorem conditionalMutualInformation_le_two_family_sum
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (G B C D : Finset V) (X : ι → Finset V) (s : Finset ι)
    (Y : κ → Finset V) (t : Finset κ)
    (hG : G = D ∪ s.biUnion X ∪ t.biUnion Y)
    (hGB : Disjoint G B) (hGC : Disjoint G C) (hBC : Disjoint B C)
    (hDX : ∀ i ∈ s, Disjoint D (X i))
    (hDY : ∀ j ∈ t, Disjoint D (Y j))
    (hX : (s : Set ι).PairwiseDisjoint X)
    (hY : (t : Set κ).PairwiseDisjoint Y)
    (hXY : ∀ i ∈ s, ∀ j ∈ t, Disjoint (X i) (Y j))
    (ε : ι → ℝ) (δ : κ → ℝ)
    (hε : ∀ i ∈ s, mutualInformation β ψ (X i) (C ∪ B ∪ past X s i) ≤ ε i)
    (hδ : ∀ j ∈ t, mutualInformation β ψ (Y j)
      (C ∪ (G ∪ B ∪ C)ᶜ ∪ past Y t j) ≤ δ j) :
    conditionalMutualInformation β ψ G C B ≤
      (∑ i ∈ s, ε i) + 2 * entropy β ψ D + ∑ j ∈ t, δ j := by
  have h := conditionalMutualInformation_le_two_family_mutualInformation β ψ hψ
    G B C D X s Y t hG hGB hGC hBC hDX hDY hX hY hXY
  have h₀ := Finset.sum_le_sum hε
  have h₁ := Finset.sum_le_sum hδ
  linarith only [h, h₀, h₁]

end FiniteProduct
