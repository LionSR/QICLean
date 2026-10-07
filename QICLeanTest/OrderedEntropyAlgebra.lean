/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.OrderedEntropyAlgebra
import Mathlib.Tactic.NormNum

/-! Regressions for finite ordered entropy algebra, including degenerate families
and genuinely negative algebraic error bounds. -/

open scoped BigOperators
open Entropy.OrderedSetFunction

-- The two families can both be empty without normalizing the set function.
example {V : Type*} [DecidableEq V] (H : Finset V → ℝ) (B D : Finset V)
    (hBD : H B ≤ H D) (ε : ℤ → ℝ) (δ : OrderDual ℤ → ℝ) : H B ≤ H D := by
  simpa using two_family_le_half_sum H B D (fun _ ↦ ∅) ∅ (fun _ ↦ ∅) ∅
    (by simpa using hBD) (by simpa using hBD) ε δ (by simp) (by simp)

-- One empty family still allows an independently ordered nonempty family.
example {V κ : Type*} [DecidableEq V] [LinearOrder κ]
    (H : Finset V → ℝ) (B D : Finset V) (Y : κ → Finset V) (t : Finset κ)
    (hB : H B ≤ H D + ∑ j ∈ t, H (Y j))
    (hY : H (B ∪ t.biUnion Y) ≤ H D) (δ : κ → ℝ)
    (hδ : ∀ j ∈ t, defect H B Y t j ≤ δ j) :
    H B ≤ H D + (1 / 2) * ∑ j ∈ t, δ j := by
  simpa using two_family_le_half_sum H B D (fun _ : OrderDual ℤ ↦ ∅) ∅ Y t
    (by simpa using hB) (by simpa using hY) (fun _ ↦ 0) δ (by simp) hδ

-- Empty tiles and an empty remainder do not require H(∅) = 0.
example (c : ℝ) (hc : 0 ≤ c) (s : Finset ℤ) : c ≤ c + ∑ _i ∈ s, c := by
  simpa using union_biUnion_le_sum (fun _ : Finset Unit ↦ c)
    (fun _ _ _ ↦ by linarith only [hc]) ∅ (fun _ : ℤ ↦ ∅) s
    (by simp) (by intro i hi j hj hij; simp)

-- Filtering a global order retains exactly the earlier members of that family.
example {V ι : Type*} [DecidableEq V] [LinearOrder ι]
    (X : ι → Finset V) (s : Finset ι) (family : ι → Bool) (f : Bool) (i : ι) :
    past X (s.filter (fun j ↦ family j = f)) i =
      (s.filter (fun j ↦ family j = f ∧ j < i)).biUnion X := by
  simp only [past, Finset.filter_filter]

-- Overlapping tiles for an arbitrary set function can have negative defects.
-- This algebraic example deliberately makes no physical disjointness claim.
example : (-1 : ℝ) ≤ 0 + (1 / 2) * (-1 + -1) := by
  have h := two_family_le_half_sum (fun R : Finset Unit ↦ -(R.card : ℝ))
    {()} ∅ (fun _ : ℤ ↦ {()}) {0} (fun _ : OrderDual ℤ ↦ {()}) {0}
    (by norm_num) (by norm_num) (fun _ ↦ -1) (fun _ ↦ -1)
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst i; norm_num [defect, past])
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst i; norm_num [defect, past])
  simpa using h

/--
info: 'Entropy.OrderedSetFunction.union_biUnion_le_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.OrderedSetFunction.union_biUnion_le_sum

/--
info: 'Entropy.OrderedSetFunction.sum_defect' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.OrderedSetFunction.sum_defect

/--
info: 'Entropy.OrderedSetFunction.chain_lower' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.OrderedSetFunction.chain_lower

/--
info: 'Entropy.OrderedSetFunction.two_family_le_half_sum_defect' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.OrderedSetFunction.two_family_le_half_sum_defect

/--
info: 'Entropy.OrderedSetFunction.two_family_le_half_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.OrderedSetFunction.two_family_le_half_sum
