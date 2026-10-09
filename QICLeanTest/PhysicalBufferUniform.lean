/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.PhysicalBufferUniform

/-!
# Consumers of the uniform original-buffer Gaussian approximation

One pair of constants works in every finite dimension at exponent `1 / 2`.
For each original Hamiltonian and ground vector, one buffer operator and one
positive real overlap are used at both `L = 1` and `L = 4`. A second example
proves all original hypotheses for a one-dimensional complex-phase state at
negative ground energy, with zero entropy and zero decay exponent.

The nontrivial-register coordinate and doubled-gap calculations are covered in
`QICLeanTest/PhysicalBufferGaussianFilter.lean`; these consumers test the new
order of choices and the positive-variance and zero-exponent boundary cases.
-/

open Matrix GaussianFilter
open scoped Kronecker ComplexOrder InnerProductSpace Matrix.Norms.L2Operator NNReal

namespace PhysicalBufferUniformTest

-- The constants are selected before all register types and original system data.
-- The two actual integrals use the same W,z, not independently chosen witnesses.
example :
    ∃ a T₀ : ℝ, 0 < a ∧ 0 < T₀ ∧
      ∀ (R C Q : Type) [Fintype R] [Fintype C] [Fintype Q]
        [DecidableEq R] [DecidableEq C] [DecidableEq Q]
        (H : Matrix ((R × C) × Q) ((R × C) × Q) ℂ)
        (Ω : (R × C) × Q → ℂ) (E₀ b : ℝ),
        star Ω ⬝ᵥ Ω = 1 → H *ᵥ Ω = (E₀ : ℂ) • Ω →
        (H - (E₀ : ℂ) • 1 -
          (2 : ℂ) • (1 - vecMulVec Ω (star Ω))).PosSemidef → 0 ≤ b →
        quantumRelativeEntropy
          (partialTraceRight (vecMulVec Ω (star Ω)))
          (partialTraceRight (partialTraceRight (vecMulVec Ω (star Ω))) ⊗ₖ
            partialTraceLeft (partialTraceRight (vecMulVec Ω (star Ω)))) ≤ b →
        let e := Equiv.doubledRegroup (R × C) Q
        let K := reindex e e (doubledHamiltonian H)
        let S := partialSwap R C ⊗ₖ (1 : Matrix (Q × Q) (Q × Q) ℂ)
        let K' := S * K * Sᴴ
        let Ψ := WithLp.toLp 2 (doubledRegroup Ω)
        let Φ := WithLp.toLp 2 (physicalLeftSwap (doubledRegroup Ω))
        ∃ (W : Matrix (Q × Q) (Q × Q) ℂ) (z : ℝ),
          let V := (1 : Matrix ((R × C) × (R × C)) ((R × C) × (R × C)) ℂ) ⊗ₖ W
          let M₁ := gaussianIntertwinerTruncated (Real.toNNReal (a * (1 + b)))
            (T₀ * (1 + b)) K' K V
          let M₄ := gaussianIntertwinerTruncated
            (Real.toNNReal (a * (1 + b + Real.log 4)))
            (T₀ * (1 + b + Real.log 4)) K' K V
          let ε₁ := 3 * Real.exp (-10 * b)
          let ε₄ := 3 * Real.exp (-10 * b) * (4 : ℝ) ^ (-(1 / 2 : ℝ))
          W.IsHermitian ∧ ‖W‖ ≤ 1 ∧ Real.exp (-2 * b) ≤ z ∧ 0 < z ∧
            ‖M₁‖ ≤ 1 ∧ ‖toEuclideanLin M₁ Ψ - (z : ℂ) • Φ‖ ≤ ε₁ ∧
            ‖toEuclideanLin M₁ᴴ Φ - (z : ℂ) • Ψ‖ ≤ ε₁ ∧
            ‖M₄‖ ≤ 1 ∧ ‖toEuclideanLin M₄ Ψ - (z : ℂ) • Φ‖ ≤ ε₄ ∧
            ‖toEuclideanLin M₄ᴴ Φ - (z : ℂ) • Ψ‖ ≤ ε₄ := by
  obtain ⟨a, T₀, ha, hT₀, hsystem⟩ :=
    exists_uniform_physicalBuffer_filter two_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine ⟨a, T₀, ha, hT₀, ?_⟩
  intro R C Q _ _ _ _ _ _ H Ω E₀ b hΩ heigen hgap hb hbound
  obtain ⟨W, z, hWherm, hW, hz, _, hscale⟩ :=
    hsystem R C Q H Ω E₀ b hΩ heigen hgap hb hbound
  have hfirst := hscale 1 (by norm_num)
  have hfourth := hscale 4 (by norm_num)
  simp only [Real.log_one, add_zero, Real.one_rpow, mul_one] at hfirst
  exact ⟨W, z, hWherm, hW, hz, (Real.exp_pos _).trans_le hz,
    hfirst.2.2.2.1, hfirst.2.2.2.2.1, hfirst.2.2.2.2.2,
    hfourth.2.2.2.1, hfourth.2.2.2.2⟩

private noncomputable def phase : (Unit × Unit) × Unit → ℂ := fun _ ↦ Complex.I

private theorem phase_normalized : star phase ⬝ᵥ phase = 1 := by
  norm_num [phase, dotProduct, Fintype.sum_prod_type, Pi.star_apply]

private theorem phase_projector : vecMulVec phase (star phase) = 1 := by
  ext i j
  rw [Subsingleton.elim j i]
  simp [phase, vecMulVec_apply, Pi.star_apply]

private theorem phase_product_marginal :
    partialTraceRight (vecMulVec phase (star phase)) =
      partialTraceRight (partialTraceRight (vecMulVec phase (star phase))) ⊗ₖ
        partialTraceLeft (partialTraceRight (vecMulVec phase (star phase))) := by
  ext i j
  simp [phase, partialTraceRight_apply, partialTraceLeft_apply, vecMulVec_apply,
    Pi.star_apply]

-- At b = r = 0 the variance is still strictly positive, even at L = 1.
-- Normalization, eigenvector, gap, and entropy hypotheses are all proved here.
example :
    let H : Matrix ((Unit × Unit) × Unit) ((Unit × Unit) × Unit) ℂ := (-3 : ℂ) • 1
    let e := Equiv.doubledRegroup (Unit × Unit) Unit
    let K := reindex e e (doubledHamiltonian H)
    let S := partialSwap Unit Unit ⊗ₖ (1 : Matrix (Unit × Unit) (Unit × Unit) ℂ)
    let K' := S * K * Sᴴ
    let Ψ := WithLp.toLp 2 (doubledRegroup phase)
    let Φ := WithLp.toLp 2 (physicalLeftSwap (doubledRegroup phase))
    ∃ (a T₀ : ℝ) (W : Matrix (Unit × Unit) (Unit × Unit) ℂ) (z : ℝ),
      0 < a ∧ 0 < T₀ ∧ W.IsHermitian ∧ ‖W‖ ≤ 1 ∧ 1 ≤ z ∧
        ∀ L : ℝ, 1 ≤ L →
          let h := Real.toNNReal (a * (1 + Real.log L))
          let T := T₀ * (1 + Real.log L)
          let V := (1 : Matrix ((Unit × Unit) × (Unit × Unit))
            ((Unit × Unit) × (Unit × Unit)) ℂ) ⊗ₖ W
          let M := gaussianIntertwinerTruncated h T K' K V
          (h : ℝ) = a * (1 + Real.log L) ∧ 0 < (h : ℝ) ∧ 0 ≤ T ∧ ‖M‖ ≤ 1 ∧
            ‖toEuclideanLin M Ψ - (z : ℂ) • Φ‖ ≤ 3 ∧
            ‖toEuclideanLin Mᴴ Φ - (z : ℂ) • Ψ‖ ≤ 3 := by
  let H : Matrix ((Unit × Unit) × Unit) ((Unit × Unit) × Unit) ℂ := (-3 : ℂ) • 1
  have heigen : H *ᵥ phase = ((-3 : ℝ) : ℂ) • phase := by
    dsimp only [H]
    rw [smul_mulVec, one_mulVec]
    norm_num
  have hgap : (H - ((-3 : ℝ) : ℂ) • 1 -
      ((2 : ℝ) : ℂ) • (1 - vecMulVec phase (star phase))).PosSemidef := by
    simpa [H, phase_projector] using
      (PosSemidef.zero : (0 : Matrix ((Unit × Unit) × Unit)
        ((Unit × Unit) × Unit) ℂ).PosSemidef)
  have hbound : quantumRelativeEntropy
      (partialTraceRight (vecMulVec phase (star phase)))
      (partialTraceRight (partialTraceRight (vecMulVec phase (star phase))) ⊗ₖ
        partialTraceLeft (partialTraceRight (vecMulVec phase (star phase)))) ≤ 0 := by
    rw [← phase_product_marginal, quantumRelativeEntropy_self]
  obtain ⟨a, T₀, ha, hT₀, hsystem⟩ :=
    exists_uniform_physicalBuffer_filter two_pos (le_refl (0 : ℝ))
  obtain ⟨W, z, hWherm, hW, hz, _, hscale⟩ := hsystem Unit Unit Unit H phase (-3) 0
    phase_normalized heigen hgap (le_refl 0) hbound
  have hz' : 1 ≤ z := by simpa using hz
  refine ⟨a, T₀, W, z, ha, hT₀, hWherm, hW, hz', ?_⟩
  intro L hL
  simpa only [add_zero, mul_zero, neg_zero, Real.exp_zero, Real.rpow_zero, mul_one]
    using hscale L hL

-- Empty physical factors cannot satisfy the normalized-state premise.
example (Ω : (Bool × Bool) × Empty → ℂ) : star Ω ⬝ᵥ Ω ≠ 1 := by
  simp [dotProduct]

end PhysicalBufferUniformTest

/--
info: 'GaussianFilter.exists_uniform_physicalBuffer_filter' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.exists_uniform_physicalBuffer_filter
