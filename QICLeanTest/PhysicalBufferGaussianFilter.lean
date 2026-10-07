/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.PhysicalBuffer

/-! Consumers on three nontrivial physical registers, with a complex ground state,
negative ground energy, and one buffer witness for full and truncated filters. -/

open Matrix GaussianFilter
open scoped Kronecker ComplexOrder InnerProductSpace Matrix.Norms.L2Operator NNReal

namespace PhysicalBufferGaussianFilterTest

private noncomputable def state : (Bool × Bool) × Bool → ℂ :=
  fun p ↦ if p = ((false, false), false) then 3 / 5 else
    if p = ((true, true), true) then 4 * Complex.I / 5 else 0

private theorem state_normalized : star state ⬝ᵥ state = 1 := by
  norm_num [state, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool,
    Pi.star_apply, map_ofNat, Complex.ext_iff]

private theorem state_projector : vecMulVec state (star state) *ᵥ state = state := by
  rw [vecMulVec_mulVec, state_normalized]
  simp

private noncomputable def hamiltonian : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ :=
  ((-3 : ℝ) : ℂ) • 1 + ((2 : ℝ) : ℂ) • (1 - vecMulVec state (star state))

private theorem hamiltonian_gap :
    (hamiltonian - ((-3 : ℝ) : ℂ) • 1 -
      ((2 : ℝ) : ℂ) • (1 - vecMulVec state (star state))).PosSemidef := by
  simpa only [hamiltonian, add_sub_cancel_left, sub_self] using
    (PosSemidef.zero : (0 : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ).PosSemidef)

private theorem hamiltonian_eigenvector : hamiltonian *ᵥ state = ((-3 : ℝ) : ℂ) • state := by
  simp only [hamiltonian, add_mulVec, sub_mulVec, smul_mulVec, one_mulVec,
    state_projector, sub_self, smul_zero, add_zero]

-- Both B and Q coordinates stay fixed. Swapping the whole A × B register would
-- give zero at this coordinate, so this checks the intended physical swap.
example : physicalLeftSwap (doubledRegroup state)
    (((true, false), (false, true)), (false, true)) = 12 * Complex.I / 25 := by
  norm_num [physicalLeftSwap, doubledRegroup, state]
  ring

example : doubledRegroup state
    (((false, true), (true, false)), (false, true)) = 0 := by
  norm_num [doubledRegroup, state]

-- The sole original gap hypothesis also provides the Hermiticity needed by the integral.
example : hamiltonian.IsHermitian :=
  isHermitian_of_posSemidef_gap (H := hamiltonian) (Ω := state)
    (E₀ := -3) (Δ := 2) hamiltonian_gap

-- The same original two-qubit buffer witness controls the full filter at variance 2
-- and its cutoff-3 truncation. No paired ground-state or gap hypotheses are supplied.
example {b : ℝ} (hb : 0 ≤ b)
    (hbound : quantumRelativeEntropy
      (partialTraceRight (vecMulVec state (star state)))
      (partialTraceRight (partialTraceRight (vecMulVec state (star state))) ⊗ₖ
        partialTraceLeft (partialTraceRight (vecMulVec state (star state)))) ≤ b) :
    let e := Equiv.doubledRegroup (Bool × Bool) Bool
    let K := reindex e e (doubledHamiltonian hamiltonian)
    let S := partialSwap Bool Bool ⊗ₖ (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    let K' := S * K * Sᴴ
    let Ψ := WithLp.toLp 2 (doubledRegroup state)
    let Φ := WithLp.toLp 2 (physicalLeftSwap (doubledRegroup state))
    ∃ (W : Matrix (Bool × Bool) (Bool × Bool) ℂ) (z : ℝ),
      let V := (1 : Matrix ((Bool × Bool) × (Bool × Bool))
        ((Bool × Bool) × (Bool × Bool)) ℂ) ⊗ₖ W
      let M := gaussianIntertwiner 2 K' K V
      let N := gaussianIntertwinerTruncated 2 3 K' K V
      W.IsHermitian ∧ 0 < z ∧ ‖M‖ ≤ 1 ∧
      ‖toEuclideanLin M Ψ - (z : ℂ) • Φ‖ ≤ Real.exp (-4) ∧
      ‖toEuclideanLin Mᴴ Φ - (z : ℂ) • Ψ‖ ≤ Real.exp (-4) ∧
      ‖N‖ ≤ 1 ∧
      ‖toEuclideanLin N Ψ - (z : ℂ) • Φ‖ ≤ Real.exp (-4) + 2 * Real.exp (-9 / 4) ∧
      ‖toEuclideanLin Nᴴ Φ - (z : ℂ) • Ψ‖ ≤ Real.exp (-4) + 2 * Real.exp (-9 / 4) := by
  obtain ⟨W, z, hWherm, _, hz, _, hall⟩ := exists_physicalBuffer_gaussian_filter
    hamiltonian state (E₀ := -3) (Δ := 2) state_normalized hamiltonian_eigenvector
    hamiltonian_gap (by norm_num) hb hbound
  obtain ⟨hM, hf, hr, htruncated⟩ := hall 2
  obtain ⟨hN, hfT, hrT⟩ := htruncated 3 (by norm_num)
  refine ⟨W, z, hWherm, (Real.exp_pos _).trans_le hz, hM, ?_, ?_, hN, ?_, ?_⟩
  · norm_num at hf ⊢
    exact hf
  · norm_num at hr ⊢
    exact hr
  · norm_num at hfT ⊢
    exact hfT
  · norm_num at hrT ⊢
    exact hrT

-- Zero variance uses the probability measure, and remains the actual input contraction.
example (K' K : Matrix (((Bool × Bool) × (Bool × Bool)) × (Bool × Bool))
    (((Bool × Bool) × (Bool × Bool)) × (Bool × Bool)) ℂ)
    (W : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    gaussianIntertwiner 0 K' K ((1 : Matrix ((Bool × Bool) × (Bool × Bool))
      ((Bool × Bool) × (Bool × Bool)) ℂ) ⊗ₖ W) =
      (1 : Matrix ((Bool × Bool) × (Bool × Bool)) ((Bool × Bool) × (Bool × Bool)) ℂ) ⊗ₖ W :=
  gaussianIntertwiner_zero_variance _ _ _

end PhysicalBufferGaussianFilterTest

/--
info: 'Matrix.isHermitian_of_posSemidef_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.isHermitian_of_posSemidef_gap

/--
info: 'Matrix.physicalBuffer_ground_pair' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.physicalBuffer_ground_pair

/--
info: 'GaussianFilter.exists_physicalBuffer_gaussian_filter' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.exists_physicalBuffer_gaussian_filter
