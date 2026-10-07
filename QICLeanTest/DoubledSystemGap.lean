/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.DoubledSystemGap
import QICLean.Analysis.GlobalGap

/-! Regression checks for the doubled full-system gap and the physical partial swap. -/

open scoped Matrix Kronecker ComplexOrder InnerProductSpace
open Matrix

namespace DoubledSystemGapTest

-- A complex phase is squared, rather than discarded, by doubling.
example : doubledVector (fun _ : Unit ↦ Complex.I) = fun _ ↦ (-1 : ℂ) := by
  ext p
  simp [doubledVector]

-- Normalization also covers a one-dimensional physical space.
example : ‖WithLp.toLp 2 (doubledVector (fun _ : Unit ↦ Complex.I))‖ = 1 := by
  apply norm_doubledVector
  simp

private noncomputable def complexGround : Bool × Bool → ℂ :=
  fun p ↦ if p = (false, false) then 3 / 5 else
    if p = (true, true) then 4 * Complex.I / 5 else 0

private theorem complexGround_normalized : ∑ p, ‖complexGround p‖ ^ 2 = 1 := by
  simp only [← Complex.normSq_eq_norm_sq]
  norm_num [complexGround, Fintype.sum_prod_type, Fintype.sum_bool, Complex.normSq_apply]

private theorem complexGround_projector :
    vecMulVec complexGround (star complexGround) *ᵥ complexGround = complexGround := by
  ext ⟨i, j⟩
  cases i <;> cases j <;>
    norm_num [complexGround, mulVec, dotProduct, vecMulVec, Fintype.sum_prod_type,
      Fintype.sum_bool, map_ofNat, Complex.ext_iff]

private noncomputable def modelHamiltonian (E₀ Δ : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (E₀ : ℂ) • 1 + (Δ : ℂ) • (1 - vecMulVec complexGround (star complexGround))

private theorem modelHamiltonian_gap (E₀ Δ : ℝ) :
    (modelHamiltonian E₀ Δ - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec complexGround (star complexGround))).PosSemidef := by
  convert (PosSemidef.zero : (0 : Matrix (Bool × Bool) (Bool × Bool) ℂ).PosSemidef) using 1
  unfold modelHamiltonian
  module

private theorem modelHamiltonian_eigenvector (E₀ Δ : ℝ) :
    modelHamiltonian E₀ Δ *ᵥ complexGround = (E₀ : ℂ) • complexGround := by
  simp [modelHamiltonian, add_mulVec, sub_mulVec, smul_mulVec, complexGround_projector]

-- A strictly positive lower-gap bound survives doubling at a negative ground energy.
example :
    (doubledHamiltonian (modelHamiltonian (-3) 2) - (-6 : ℂ) • 1 -
      (2 : ℂ) • (1 - vecMulVec (doubledVector complexGround)
        (star (doubledVector complexGround)))).PosSemidef := by
  have h := (modelHamiltonian_gap (-3) 2).doubled_gap complexGround_normalized
    (show (0 : ℝ) ≤ 2 by norm_num)
  norm_num at h ⊢
  exact h

-- The zero-gap endpoint is admitted without any uniqueness claim.
example :
    (doubledHamiltonian (modelHamiltonian (-3) 0) - (-6 : ℂ) • 1).PosSemidef := by
  have h := (modelHamiltonian_gap (-3) 0).doubled_gap complexGround_normalized
    (show (0 : ℝ) ≤ 0 by rfl)
  norm_num at h ⊢
  exact h

-- At zero gap the entire nontrivial space can consist of ground vectors.
example (ψ : Bool × Bool → ℂ) :
    modelHamiltonian (-3) 0 *ᵥ ψ = (-3 : ℂ) • ψ := by
  simp only [modelHamiltonian, Complex.ofReal_zero, zero_smul, add_zero, Matrix.smul_mulVec,
    one_mulVec, Complex.ofReal_neg, Complex.ofReal_ofNat]

-- The eigen equation retains the factor two and the negative energy shift.
example : doubledHamiltonian (modelHamiltonian (-3) 2) *ᵥ doubledVector complexGround =
    (-6 : ℂ) • doubledVector complexGround := by
  have h := doubledHamiltonian_mulVec (modelHamiltonian_eigenvector (-3) 2)
  norm_num at h ⊢
  exact h

-- The existing full-system quadratic-form API consumes the new doubled defect directly.
example (ψ : EuclideanSpace ℂ ((Bool × Bool) × (Bool × Bool))) :
    2 * (‖ψ‖ ^ 2 - ‖⟪WithLp.toLp 2 (doubledVector complexGround), ψ⟫_ℂ‖ ^ 2) ≤
      (⟪ψ, toEuclideanLin (doubledHamiltonian (modelHamiltonian (-3) 2)) ψ⟫_ℂ).re +
        6 * ‖ψ‖ ^ 2 := by
  have hg := (modelHamiltonian_gap (-3) 2).doubled_gap complexGround_normalized
    (show (0 : ℝ) ≤ 2 by norm_num)
  have h := PosSemidef.gap_le (Ω := WithLp.toLp 2 (doubledVector complexGround)) hg ψ
  convert h using 1
  norm_num

-- An actual partial swap changes this entangled complex vector on the physical space.
example : (partialSwap Bool Bool *ᵥ doubledVector complexGround)
    ((false, true), (true, false)) = 12 * Complex.I / 25 := by
  rw [partialSwap_mulVec]
  norm_num [Function.comp_apply, doubledVector, complexGround]
  ring

example : doubledVector complexGround ((false, true), (true, false)) = 0 := by
  norm_num [doubledVector, complexGround]

-- All three swapped-Hamiltonian conclusions hold together for this concrete model.
example :
    let F := partialSwap Bool Bool
    let Φ := F *ᵥ doubledVector complexGround
    let H' := F * doubledHamiltonian (modelHamiltonian (-3) 2) * Fᴴ
    ‖WithLp.toLp 2 Φ‖ = 1 ∧ H' *ᵥ Φ = (-6 : ℂ) • Φ ∧
      (H' - (-6 : ℂ) • 1 - (2 : ℂ) • (1 - vecMulVec Φ (star Φ))).PosSemidef := by
  have h := doubled_gap_partialSwap (modelHamiltonian_gap (-3) 2)
    complexGround_normalized (modelHamiltonian_eigenvector (-3) 2)
    (show (0 : ℝ) ≤ 2 by norm_num)
  norm_num at h ⊢
  exact h

-- Algebraic transport permits empty index types; normalized vectors exclude them themselves.
example (H U : Matrix Empty Empty ℂ) (Ω : Empty → ℂ) (E₀ Δ : ℝ) :
    U * H * Uᴴ - (E₀ : ℂ) • 1 -
        (Δ : ℂ) • (1 - vecMulVec (U *ᵥ Ω) (star (U *ᵥ Ω))) =
      U * (H - (E₀ : ℂ) • 1 - (Δ : ℂ) • (1 - vecMulVec Ω (star Ω))) * Uᴴ := by
  apply gap_unitary_conj_eq
  exact mem_unitaryGroup_iff.mpr (Subsingleton.elim _ _)

end DoubledSystemGapTest

/--
info: 'Matrix.doubledVector' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.doubledVector

/--
info: 'Matrix.doubledHamiltonian' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.doubledHamiltonian

/--
info: 'Matrix.vecMulVec_doubledVector' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.vecMulVec_doubledVector

/--
info: 'Matrix.sum_normSq_doubledVector' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.sum_normSq_doubledVector

/--
info: 'Matrix.norm_doubledVector' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_doubledVector

/--
info: 'Matrix.doubledHamiltonian_mulVec' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.doubledHamiltonian_mulVec

/--
info: 'Matrix.doubledHamiltonian_gap_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.doubledHamiltonian_gap_eq

/--
info: 'Matrix.PosSemidef.doubled_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.doubled_gap

/--
info: 'Matrix.norm_toLp_mulVec_of_unitary' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_toLp_mulVec_of_unitary

/--
info: 'Matrix.gap_unitary_conj_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.gap_unitary_conj_eq

/--
info: 'Matrix.PosSemidef.gap_unitary_conj' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.gap_unitary_conj

/--
info: 'Matrix.mulVec_unitary_conj_eigenvector' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.mulVec_unitary_conj_eigenvector

/--
info: 'Matrix.doubled_gap_partialSwap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.doubled_gap_partialSwap
