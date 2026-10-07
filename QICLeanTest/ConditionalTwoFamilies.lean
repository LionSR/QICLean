/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.ConditionalTwoFamilies
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Physical regressions for conditional two-family cancellation. -/

open scoped BigOperators
open FiniteProduct
open Entropy.OrderedSetFunction

-- Both families may be empty; the entire system of interest is exceptional.
example {V : Type*} [Fintype V] [DecidableEq V]
    (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (D B C : Finset V) (hDB : Disjoint D B) (hDC : Disjoint D C)
    (hBC : Disjoint B C) : conditionalMutualInformation β ψ D C B ≤ 2 * entropy β ψ D := by
  have h := conditionalMutualInformation_le_two_family_sum β ψ hψ D B C D
    (fun _ : ℤ ↦ ∅) ∅ (fun _ : OrderDual ℚ ↦ ∅) ∅ (by simp)
    hDB hDC hBC (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun _ ↦ 0) (fun _ ↦ 0) (by simp) (by simp)
  simpa only [Finset.sum_empty, zero_add, add_zero] using h

-- One empty family and an empty remainder still use the complementary exterior.
example {V : Type*} [Fintype V] [DecidableEq V]
    (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (G B C : Finset V) (hGB : Disjoint G B) (hGC : Disjoint G C)
    (hBC : Disjoint B C) (δ : ℝ)
    (hδ : mutualInformation β ψ G (C ∪ (G ∪ B ∪ C)ᶜ) ≤ δ) :
    conditionalMutualInformation β ψ G C B ≤ δ := by
  have h := conditionalMutualInformation_le_two_family_sum β ψ hψ G B C ∅
    (fun _ : ℤ ↦ ∅) ∅ (fun _ : ℤ ↦ G) {0} (by simp)
    hGB hGC hBC (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun _ ↦ 0) (fun _ ↦ δ) (by simp) (by
      intro i hi
      simp only [Finset.mem_singleton] at hi
      subst i
      simpa [past, Finset.filter_singleton] using hδ)
  simpa [entropy_empty β ψ hψ] using h

/-- Creation order need not follow the order of the physical sites. -/
abbrev firstTiles : Fin 2 → Finset (Fin 6) := ![{2}, {0}]

/-- The second family remains nonempty after the exceptional block. -/
abbrev secondTiles : Fin 1 → Finset (Fin 6) := fun _ ↦ {3}

example (ψ : EuclideanSpace ℂ (Fin 6 → Fin 2)) (hψ : ‖ψ‖ = 1)
    (ε₀ ε₁ δ : ℝ)
    (h₀ : mutualInformation (fun _ : Fin 6 ↦ Fin 2) ψ {2} {4, 5} ≤ ε₀)
    (h₁ : mutualInformation (fun _ : Fin 6 ↦ Fin 2) ψ {0} {2, 4, 5} ≤ ε₁)
    (h₂ : mutualInformation (fun _ : Fin 6 ↦ Fin 2) ψ {3} {5} ≤ δ) :
    conditionalMutualInformation (fun _ : Fin 6 ↦ Fin 2) ψ {0, 1, 2, 3} {5} {4} ≤
      ε₀ + ε₁ + 2 * entropy (fun _ : Fin 6 ↦ Fin 2) ψ {1} + δ := by
  have h := conditionalMutualInformation_le_two_family_sum
    (fun _ : Fin 6 ↦ Fin 2) ψ hψ {0, 1, 2, 3} {4} {5} {1}
    firstTiles Finset.univ secondTiles Finset.univ
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (by
      intro i _ j _ hij
      fin_cases i <;> fin_cases j <;> simp_all [firstTiles, Function.onFun])
    (by
      intro i _ j _ hij
      exact (hij (Subsingleton.elim i j)).elim)
    (by decide)
    ![ε₀, ε₁] (fun _ ↦ δ) (by
      intro i hi
      fin_cases i
      · have hR : ({5} : Finset (Fin 6)) ∪ {4} ∪ past firstTiles Finset.univ 0 =
            {4, 5} := by decide
        change mutualInformation _ ψ {2} ({5} ∪ {4} ∪ past firstTiles Finset.univ 0) ≤ ε₀
        rw [hR]
        exact h₀
      · have hR : ({5} : Finset (Fin 6)) ∪ {4} ∪ past firstTiles Finset.univ 1 =
            {2, 4, 5} := by decide
        change mutualInformation _ ψ {0} ({5} ∪ {4} ∪ past firstTiles Finset.univ 1) ≤ ε₁
        rw [hR]
        exact h₁) (by
      intro i hi
      fin_cases i
      have hR : ({5} : Finset (Fin 6)) ∪ ({0, 1, 2, 3} ∪ {4} ∪ {5})ᶜ ∪
          past secondTiles Finset.univ 0 = {5} := by decide
      change mutualInformation _ ψ {3}
        ({5} ∪ ({0, 1, 2, 3} ∪ {4} ∪ {5})ᶜ ∪ past secondTiles Finset.univ 0) ≤ δ
      rw [hR]
      exact h₂)
  simpa [Fin.sum_univ_succ, add_assoc] using h

-- The empty target has zero conditional information, without normalization.
example {V : Type*} [Fintype V] [DecidableEq V]
    (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (G B : Finset V) :
    conditionalMutualInformation β ψ G ∅ B = 0 := by
  simp [conditionalMutualInformation]

/--
info: 'FiniteProduct.conditionalMutualInformation_union_left'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  FiniteProduct.conditionalMutualInformation_union_left

/--
info: 'FiniteProduct.mutualInformation_le_two_entropy'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  FiniteProduct.mutualInformation_le_two_entropy

/--
info: 'FiniteProduct.conditionalMutualInformation_le_two_entropy'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  FiniteProduct.conditionalMutualInformation_le_two_entropy

/--
info: 'FiniteProduct.conditionalMutualInformation_biUnion_le_sum'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  FiniteProduct.conditionalMutualInformation_biUnion_le_sum

/--
info: 'FiniteProduct.conditionalMutualInformation_le_two_family_mutualInformation'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  FiniteProduct.conditionalMutualInformation_le_two_family_mutualInformation

/--
info: 'FiniteProduct.conditionalMutualInformation_le_two_family_sum'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  FiniteProduct.conditionalMutualInformation_le_two_family_sum

/--
info: 'FiniteProduct.target_union_complement_eq_exterior'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  FiniteProduct.target_union_complement_eq_exterior
