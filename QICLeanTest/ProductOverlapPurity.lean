/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.ProductOverlapPurity
import Mathlib.Tactic.NormNum

/-! Regressions for dimension-free product overlap and exact partial-swap purity. -/

open scoped Matrix BigOperators Matrix.Norms.L2Operator
open Matrix

-- The normalized one-dimensional case has no rank or cardinality side condition.
example (χ : Unit × Unit → ℂ) :
    ‖star (fun _ : Unit × Unit ↦ (1 : ℂ) * 1) ⬝ᵥ χ‖ ^ 4 ≤
      ((partialTraceRight (vecMulVec χ (star χ))) ^ 2).trace.re := by
  apply norm_product_overlap_pow_four_le_purity_of_star_dotProduct_eq_one
    χ (fun _ ↦ 1) (fun _ ↦ 1)
  all_goals simp [dotProduct]

-- An empty factor cannot supply a normalized vector; the theorem needs no
-- additional nonemptiness assumption to exclude this case.
example (a : Fin 0 → ℂ) : star a ⬝ᵥ a ≠ 1 := by simp [dotProduct]

example (b : Fin 0 → ℂ) : star b ⬝ᵥ b ≠ 1 := by simp [dotProduct]

-- The exact identity remains meaningful with an empty left or right factor.
example (χ : Fin 0 × Fin 3 → ℂ) :
    star (fun p : (Fin 0 × Fin 3) × (Fin 0 × Fin 3) ↦ χ p.1 * χ p.2) ⬝ᵥ
        (partialSwap (Fin 0) (Fin 3) *ᵥ (fun p ↦ χ p.1 * χ p.2)) =
      ((partialTraceRight (vecMulVec χ (star χ))) ^ 2).trace :=
  star_doubled_dotProduct_partialSwap_eq_purity χ

example (χ : Fin 3 × Fin 0 → ℂ) :
    star (fun p : (Fin 3 × Fin 0) × (Fin 3 × Fin 0) ↦ χ p.1 * χ p.2) ⬝ᵥ
        (partialSwap (Fin 3) (Fin 0) *ᵥ (fun p ↦ χ p.1 * χ p.2)) =
      ((partialTraceRight (vecMulVec χ (star χ))) ^ 2).trace :=
  star_doubled_dotProduct_partialSwap_eq_purity χ

namespace ProductOverlapPurityTest

-- This vector is deliberately unnormalized and genuinely complex.
private def χ : Bool × Bool → ℂ
  | (false, false) => 1
  | (true, true) => Complex.I
  | _ => 0

example : ((partialTraceRight (vecMulVec χ (star χ))) ^ 2).trace = 2 := by
  norm_num [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    partialTraceRight_apply, vecMulVec_apply, χ, Fintype.sum_bool]

-- An absent conjugation of either factor changes this complex overlap.
example : star (fun _ : Unit × Unit ↦ Complex.I * Complex.I) ⬝ᵥ
    (fun _ : Unit × Unit ↦ Complex.I) = -Complex.I := by
  norm_num [dotProduct]

end ProductOverlapPurityTest

/--
info: 'Matrix.star_product_dotProduct_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.star_product_dotProduct_eq

/--
info: 'Matrix.norm_product_overlap_le_schmidtCoeffMatrix' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_product_overlap_le_schmidtCoeffMatrix

/--
info: 'Matrix.norm_product_overlap_pow_four_le_purity' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_product_overlap_pow_four_le_purity

/--
info: 'Matrix.norm_product_overlap_pow_four_le_purity_of_star_dotProduct_eq_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_product_overlap_pow_four_le_purity_of_star_dotProduct_eq_one

/--
info: 'Matrix.star_doubled_dotProduct_partialSwap_eq_purity' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.star_doubled_dotProduct_partialSwap_eq_purity
