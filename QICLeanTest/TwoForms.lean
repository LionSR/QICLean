/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Projection.TwoForms

/-!
# Tests and axiom guards for two-form spectral projection splitting

This file checks:
1. Strict transitive axiom guards allowing only `[propext, Classical.choice, Quot.sound]`
   for the declarations in `QICLean.Spectral.Projection.TwoForms`.
2. Concrete instantiations of `Matrix.exists_twoForms_bipartite_split` covering:
   * `H = 0` (`E₀ = E₁ = 0`),
   * singular nonzero `H = E₀ + E₁` with non-commuting `E₀, E₁`,
   * positive-definite `H = E₀ + E₁` with non-commuting `E₀, E₁`,
   * empty index type `Empty`.
-/

set_option linter.hashCommand false

open scoped Matrix ComplexOrder Kronecker

/-! ## Strict transitive axiom guards -/

/--
info: 'Matrix.isStarProjection_nonnegSpectralProj' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.isStarProjection_nonnegSpectralProj

/--
info: 'Matrix.nonnegSpectralProj_mul_mul_posSemidef' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.nonnegSpectralProj_mul_mul_posSemidef

/--
info: 'Matrix.one_sub_nonnegSpectralProj_mul_neg_mul_posSemidef' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.one_sub_nonnegSpectralProj_mul_neg_mul_posSemidef

/--
info: 'Matrix.commute_of_add_eq_isStarProjection' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.commute_of_add_eq_isStarProjection

/--
info: 'Matrix.one_sub_nonnegSpectralProj_mul_left_mul_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.one_sub_nonnegSpectralProj_mul_left_mul_eq_zero

/--
info: 'Matrix.one_sub_nonnegSpectralProj_mul_right_mul_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.one_sub_nonnegSpectralProj_mul_right_mul_eq_zero

/--
info: 'Matrix.PosSemidef.supportWhitening_mul_supportWhiteningInv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.supportWhitening_mul_supportWhiteningInv

/--
info: 'Matrix.PosSemidef.supportWhiteningInv_mul_supportWhitening' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.supportWhiteningInv_mul_supportWhitening

/--
info: 'Matrix.PosSemidef.supportWhitening_posDef' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.supportWhitening_posDef

/--
info: 'Matrix.PosSemidef.supportWhitening_mul_self_mul_supportWhitening' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.supportWhitening_mul_self_mul_supportWhitening

/--
info: 'Matrix.twoFormSplitProj_mul_self' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.twoFormSplitProj_mul_self

/--
info: 'Matrix.one_sub_twoFormSplitProj_conjTranspose_mul_left_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.one_sub_twoFormSplitProj_conjTranspose_mul_left_mul

/--
info: 'Matrix.one_sub_twoFormSplitProj_conjTranspose_mul_right_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.one_sub_twoFormSplitProj_conjTranspose_mul_right_mul

/--
info: 'Matrix.twoFormSplitProj_conjTranspose_mul_sub_mul_posSemidef' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.twoFormSplitProj_conjTranspose_mul_sub_mul_posSemidef

/--
info: 'Matrix.one_sub_twoFormSplitProj_conjTranspose_mul_sub_mul_posSemidef' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.one_sub_twoFormSplitProj_conjTranspose_mul_sub_mul_posSemidef

/--
info: 'Matrix.twoFormSplitLeft_add_twoFormSplitRight' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.twoFormSplitLeft_add_twoFormSplitRight

/--
info: 'Matrix.twoFormSplit_quad_zero_eq_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.twoFormSplit_quad_zero_eq_add

/--
info: 'Matrix.twoFormSplit_quad_one_eq_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.twoFormSplit_quad_one_eq_add

/--
info: 'Matrix.twoFormSplit_left_diff_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.twoFormSplit_left_diff_nonneg

/--
info: 'Matrix.twoFormSplit_right_diff_nonneg' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.twoFormSplit_right_diff_nonneg

/--
info: 'Matrix.exists_twoForms_bipartite_split' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_twoForms_bipartite_split

/-! ## Concrete test cases (H = 0, singular nonzero H, positive-definite H, empty basis) -/

namespace QICLeanTest.TwoForms

/-- Helper: `B * Bᴴ` is positive semidefinite. -/
private theorem posSemidef_mul_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) : (B * Bᴴ).PosSemidef := by
  simpa only [Matrix.mul_one] using
    (Matrix.PosSemidef.one (n := n) (R := ℂ)).mul_mul_conjTranspose_same B

/-- Case 1: `H = 0` (`E₀ = 0`, `E₁ = 0`) on `Fin 2 × Fin 3`. -/
example (u : Fin 2 × Fin 3 → ℂ) (F : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ)
    (hF : ∀ j, (F j).PosSemidef) :
    ∃ v w : Fin 2 × Fin 3 → ℂ,
      v + w = u ∧
      (∀ j, star w ⬝ᵥ ((0 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F j) *ᵥ v = 0 ∧
            star w ⬝ᵥ ((0 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F j) *ᵥ v = 0 ∧
            star v ⬝ᵥ ((0 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F j) *ᵥ w = 0 ∧
            star v ⬝ᵥ ((0 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F j) *ᵥ w = 0) ∧
      (∀ j, 0 ≤ star v ⬝ᵥ (((0 : Matrix (Fin 2) (Fin 2) ℂ) - 0) ⊗ₖ F j) *ᵥ v ∧
            0 ≤ star w ⬝ᵥ (((0 : Matrix (Fin 2) (Fin 2) ℂ) - 0) ⊗ₖ F j) *ᵥ w) :=
  Matrix.exists_twoForms_bipartite_split Matrix.PosSemidef.zero Matrix.PosSemidef.zero u F hF

/-- For `H = 0`, the support whitening operator is still positive definite and invertible. -/
example : (Matrix.PosSemidef.zero (n := Fin 2) (R := ℂ)).supportWhitening.PosDef :=
  Matrix.PosSemidef.zero.supportWhitening_posDef

/-- Case 2: Singular nonzero `H = E₀ + E₁` on `Fin 3` with non-commuting `E₀, E₁`. -/
private def singB0 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
private def singB1 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 1, 0, 0; 0, 0, 0]
private def singE0 : Matrix (Fin 3) (Fin 3) ℂ := singB0 * singB0ᴴ
private def singE1 : Matrix (Fin 3) (Fin 3) ℂ := singB1 * singB1ᴴ

private theorem singE0_posSemidef : singE0.PosSemidef := posSemidef_mul_conjTranspose singB0
private theorem singE1_posSemidef : singE1.PosSemidef := posSemidef_mul_conjTranspose singB1

/-- Confirm `singE0` and `singE1` do not commute. -/
example : singE0 * singE1 ≠ singE1 * singE0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [singE0, singE1, singB0, singB1, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_three] at h01

/-- Confirm `H = singE0 + singE1` is singular (kills `e₂`) and nonzero. -/
example : (singE0 + singE1) *ᵥ ![0, 0, 1] = 0 ∧ (singE0 + singE1) 0 0 ≠ 0 := by
  constructor
  · ext i
    fin_cases i <;>
      simp [singE0, singE1, singB0, singB1, Matrix.mulVec, Matrix.vecMul, dotProduct,
        Fin.sum_univ_three]
  · simp [singE0, singE1, singB0, singB1, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

/-- Full bipartite split applies to the singular non-commuting pair `(singE0, singE1)`. -/
example (u : Fin 3 × Fin 2 → ℂ) :
    let F : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
      ![1, !![1, Complex.I; 0, 0] * (!![1, Complex.I; 0, 0])ᴴ]
    ∃ v w : Fin 3 × Fin 2 → ℂ,
      v + w = u ∧
      (∀ j, star w ⬝ᵥ (singE0 ⊗ₖ F j) *ᵥ v = 0 ∧
            star w ⬝ᵥ (singE1 ⊗ₖ F j) *ᵥ v = 0 ∧
            star v ⬝ᵥ (singE0 ⊗ₖ F j) *ᵥ w = 0 ∧
            star v ⬝ᵥ (singE1 ⊗ₖ F j) *ᵥ w = 0) ∧
      (∀ j, 0 ≤ star v ⬝ᵥ ((singE0 - singE1) ⊗ₖ F j) *ᵥ v ∧
            0 ≤ star w ⬝ᵥ ((singE1 - singE0) ⊗ₖ F j) *ᵥ w) := by
  intro F
  refine Matrix.exists_twoForms_bipartite_split singE0_posSemidef singE1_posSemidef u F ?_
  intro j
  fin_cases j
  · simpa [F] using (Matrix.PosSemidef.one (n := Fin 2) (R := ℂ))
  · simpa [F] using posSemidef_mul_conjTranspose !![(1 : ℂ), Complex.I; 0, 0]

/-- Case 3: Positive-definite `H = E₀ + E₁` with non-commuting `E₀, E₁` on `Fin 2`. -/
private def pdE0 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2, 0; 0, 1] * (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
private def pdE1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 1, 0] * (!![1, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ

example (u : Fin 2 × Fin 2 → ℂ) (F : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ)
    (hF : ∀ j, (F j).PosSemidef) :
    ∃ v w : Fin 2 × Fin 2 → ℂ,
      v + w = u ∧
      (∀ j, star w ⬝ᵥ (pdE0 ⊗ₖ F j) *ᵥ v = 0 ∧
            star w ⬝ᵥ (pdE1 ⊗ₖ F j) *ᵥ v = 0 ∧
            star v ⬝ᵥ (pdE0 ⊗ₖ F j) *ᵥ w = 0 ∧
            star v ⬝ᵥ (pdE1 ⊗ₖ F j) *ᵥ w = 0) ∧
      (∀ j, 0 ≤ star v ⬝ᵥ ((pdE0 - pdE1) ⊗ₖ F j) *ᵥ v ∧
            0 ≤ star w ⬝ᵥ ((pdE1 - pdE0) ⊗ₖ F j) *ᵥ w) :=
  Matrix.exists_twoForms_bipartite_split
    (posSemidef_mul_conjTranspose _) (posSemidef_mul_conjTranspose _) u F hF

/-- Case 4: Empty index type `A = Empty`. -/
example (u : Empty × Fin 2 → ℂ) (F : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ)
    (hF : ∀ j, (F j).PosSemidef) :
    ∃ v w : Empty × Fin 2 → ℂ,
      v + w = u ∧
      (∀ j, star w ⬝ᵥ ((0 : Matrix Empty Empty ℂ) ⊗ₖ F j) *ᵥ v = 0 ∧
            star w ⬝ᵥ ((0 : Matrix Empty Empty ℂ) ⊗ₖ F j) *ᵥ v = 0 ∧
            star v ⬝ᵥ ((0 : Matrix Empty Empty ℂ) ⊗ₖ F j) *ᵥ w = 0 ∧
            star v ⬝ᵥ ((0 : Matrix Empty Empty ℂ) ⊗ₖ F j) *ᵥ w = 0) ∧
      (∀ j, 0 ≤ star v ⬝ᵥ (((0 : Matrix Empty Empty ℂ) - 0) ⊗ₖ F j) *ᵥ v ∧
            0 ≤ star w ⬝ᵥ (((0 : Matrix Empty Empty ℂ) - 0) ⊗ₖ F j) *ᵥ w) :=
  Matrix.exists_twoForms_bipartite_split Matrix.PosSemidef.zero Matrix.PosSemidef.zero u F hF

end QICLeanTest.TwoForms
