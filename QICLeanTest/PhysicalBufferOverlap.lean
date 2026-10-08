/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.PhysicalBufferOverlap

/-! Consumers and axiom audits for the overlap on the original doubled physical buffer. -/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

/-- A complex phase checks the explicit coordinate action independently of real-valued examples. -/
def bufferPhaseState : (Bool × PUnit) × Bool → ℂ
  | ((false, _), false) => 1
  | ((true, _), true) => Complex.I
  | _ => 0

example : physicalLeftSwap (doubledRegroup bufferPhaseState)
    (((false, PUnit.unit), (true, PUnit.unit)), (true, false)) = Complex.I := by
  norm_num [physicalLeftSwap, doubledRegroup, bufferPhaseState]

/-- Doubling preserves normalization, including when the reference factor is one-dimensional. -/
example {Q : Type*} [Fintype Q] (Ω : PUnit × Q → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1) :
    star (doubledRegroup Ω) ⬝ᵥ doubledRegroup Ω = 1 := by
  rw [star_doubledRegroup_dotProduct, hΩ, one_pow]

/-- The endpoint works with a one-dimensional left register, a qutrit right register,
and a qubit physical buffer. Its result still has exactly two qubit buffer indices. -/
example (Ω : (Fin 1 × Fin 3) × Fin 2 → ℂ) (hΩ : star Ω ⬝ᵥ Ω = 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : quantumRelativeEntropy
      (partialTraceRight (vecMulVec Ω (star Ω)))
      (partialTraceRight (partialTraceRight (vecMulVec Ω (star Ω))) ⊗ₖ
        partialTraceLeft (partialTraceRight (vecMulVec Ω (star Ω)))) ≤ b) :
    ∃ (W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (z : ℝ),
      W.IsHermitian ∧ ‖W‖ ≤ 1 ∧ Real.exp (-2 * b) ≤ z ∧
      star (physicalLeftSwap (doubledRegroup Ω)) ⬝ᵥ
        (((1 : Matrix ((Fin 1 × Fin 3) × (Fin 1 × Fin 3))
          ((Fin 1 × Fin 3) × (Fin 1 × Fin 3)) ℂ) ⊗ₖ W) *ᵥ
            doubledRegroup Ω) = (z : ℂ) :=
  exists_hermitian_contraction_physicalBuffer_overlap Ω hΩ hb hbound

/-- Empty auxiliary factors are valid for the purely algebraic transport identity. -/
example (V : Matrix (Empty × Fin 2) (Fin 0) ℂ)
    (Ω : (Fin 1 × Fin 3) × Fin 0 → ℂ) :
    star (physicalLeftSwap (doubledRegroup Ω)) ⬝ᵥ
        (((1 : Matrix ((Fin 1 × Fin 3) × (Fin 1 × Fin 3))
          ((Fin 1 × Fin 3) × (Fin 1 × Fin 3)) ℂ) ⊗ₖ compressedPartialSwap V) *ᵥ
            doubledRegroup Ω) =
      ((partialTraceRight (vecMulVec
        (regroupPurification
          (((1 : Matrix (Fin 1 × Fin 3) (Fin 1 × Fin 3) ℂ) ⊗ₖ V) *ᵥ Ω))
        (star (regroupPurification
          (((1 : Matrix (Fin 1 × Fin 3) (Fin 1 × Fin 3) ℂ) ⊗ₖ V) *ᵥ Ω))))) ^ 2).trace :=
  physicalLeftSwap_compressedPartialSwap_overlap_eq_purity V Ω

/--
info: 'Equiv.bipartiteRegroup' does not depend on any axioms
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Equiv.bipartiteRegroup

/--
info: 'Equiv.doubledRegroup' does not depend on any axioms
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Equiv.doubledRegroup

/--
info: 'Matrix.doubledRegroup' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.doubledRegroup

/--
info: 'Matrix.physicalLeftSwap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.physicalLeftSwap

/--
info: 'Matrix.regroupPurification' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.regroupPurification

/--
info: 'Matrix.one_kronecker_mulVec_apply' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.one_kronecker_mulVec_apply

/--
info: 'Matrix.doubledRegroup_one_kronecker_mulVec' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.doubledRegroup_one_kronecker_mulVec

/--
info: 'Matrix.star_doubledRegroup_dotProduct' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.star_doubledRegroup_dotProduct

/--
info: 'Matrix.star_regroupPurification_dotProduct' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.star_regroupPurification_dotProduct

/--
info: 'Matrix.star_tensorPurification_dotProduct_eq_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.star_tensorPurification_dotProduct_eq_one

/--
info: 'Matrix.exp_neg_half_le_re_overlap_of_norm_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exp_neg_half_le_re_overlap_of_norm_sub_le

/--
info: 'Matrix.physicalLeftSwap_eq_mulVec' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.physicalLeftSwap_eq_mulVec

/--
info: 'Matrix.star_doubledRegroup_dotProduct_partialSwaps_eq_purity' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.star_doubledRegroup_dotProduct_partialSwaps_eq_purity

/--
info: 'Matrix.physicalLeftSwap_compressedPartialSwap_overlap_eq_purity' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.physicalLeftSwap_compressedPartialSwap_overlap_eq_purity

/--
info: 'Matrix.exists_hermitian_contraction_physicalBuffer_overlap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_hermitian_contraction_physicalBuffer_overlap
