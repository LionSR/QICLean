/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.TrimmingEnergy

/-! # Axiom check for the energy of a trimmed vector -/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped Kronecker ComplexOrder

/-- info:
'Matrix.PosSemidef.abs_re_inner_toEuclideanLin_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.abs_re_inner_toEuclideanLin_le

/-- info:
'Matrix.PosSemidef.mul_sq_norm_le_re_inner_toEuclideanLin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.mul_sq_norm_le_re_inner_toEuclideanLin

/-- info:
'Matrix.toEuclideanLin_kronecker_one_apply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.toEuclideanLin_kronecker_one_apply

/-- info:
'Matrix.toEuclideanLin_one_kronecker_apply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.toEuclideanLin_one_kronecker_apply

/-- info:
'Matrix.exists_isometry_mul_conjTranspose_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_isometry_mul_conjTranspose_eq

/-- info:
'Matrix.IsTrimmingProjection.norm_leftApply_sq_add_norm_sub_sq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.norm_leftApply_sq_add_norm_sub_sq

/-- info:
'Matrix.IsTrimmingProjection.inner_toEuclideanLin_eq_add'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.inner_toEuclideanLin_eq_add

/-- info:
'Matrix.IsTrimmingProjection.re_inner_leftApply_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.re_inner_leftApply_le

/-- info:
'Matrix.IsTrimmingProjection.re_inner_normalized_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.re_inner_normalized_le

/-- info:
'Matrix.IsTrimmingProjection.re_inner_normalized_le_of_le_half'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.re_inner_normalized_le_of_le_half

/-- info:
'Matrix.IsTrimmingProjection.norm_sub_leftApply_sq_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.norm_sub_leftApply_sq_le

/-- info:
'Matrix.IsTrimmingProjection.re_inner_normalized_le_of_norm_inner'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.re_inner_normalized_le_of_norm_inner

/-- info:
'Matrix.IsTrimmingProjection.exists_isometry_leftApply_eq_rightApply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsTrimmingProjection.exists_isometry_leftApply_eq_rightApply

section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

-- The corrected Lemma `l:2` for a trimming projection supplied by the existence theorem.
example (ψ u : EuclideanSpace ℂ (m × n)) (D : ℕ) (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (K : Matrix (m × n) (m × n) ℂ) (E₀ δ η : ℝ)
    (hH : (A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B + K -
      (E₀ : ℂ) • 1).PosSemidef)
    (hK0 : K.PosSemidef) (hK1 : (1 - K).PosSemidef) (hψ : ‖ψ‖ = 1)
    (hE : (inner ℂ ψ (Matrix.toEuclideanLin
      (A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B + K) ψ)).re ≤ E₀ + δ)
    (hu : ‖u‖ = 1) (huD : Matrix.HasSchmidtRankLE D (WithLp.ofLp u))
    (hη : 1 - η ≤ ‖inner ℂ u ψ‖) (hη2 : 2 * η < 1) :
    ∃ P : Matrix m m ℂ,
      (inner ℂ (‖Matrix.leftApply P ψ‖⁻¹ • Matrix.leftApply P ψ)
        (Matrix.toEuclideanLin (A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B + K)
          (‖Matrix.leftApply P ψ‖⁻¹ • Matrix.leftApply P ψ))).re ≤
        E₀ + (δ + 2 * √(2 * η)) / (1 - 2 * η) := by
  obtain ⟨P, hP⟩ := Matrix.exists_isTrimmingProjection ψ D
  exact ⟨P, hP.re_inner_normalized_le_of_norm_inner rfl hH hK0 hK1 hψ hE hu huD hη hη2⟩

end
