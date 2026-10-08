/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.UniformGroundEstimate

/-!
# Consumers of the uniform truncated Gaussian ground-vector estimate

The shifted-projector Hamiltonians have ground energy `-7` and gap `2`.
One choice of constants serves every finite dimension, every pair of unit
ground vectors, every contraction, and all admissible scales. A second
consumer applies one choice at `(b, L) = (0, 1)` in dimension one and at
`(2, 4)` in dimension two. The exponent `1 / 2` is not an integer.

The phase `I` gives overlap `-I` for the identity input, so the forward and
adjoint estimates have different coefficients even for a Hermitian input.
The Hamiltonian construction is adapted from
`QICLeanTest/GaussianGroundEstimate.lean`.
-/

open Complex Matrix GaussianFilter
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal ComplexOrder

namespace GaussianUniformGroundEstimateTest

variable {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable def H (Ω : EuclideanSpace ℂ n) : Matrix n n ℂ :=
  ((-7 : ℝ) : ℂ) • 1 + ((2 : ℝ) : ℂ) •
    (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))

omit [Fintype n] in
private theorem hermitian (Ω : EuclideanSpace ℂ n) : (H Ω).IsHermitian := by
  have hp : (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).IsHermitian := by
    rw [IsHermitian, conjTranspose_vecMulVec, star_star]
  exact (isHermitian_one.smul (Complex.conj_ofReal (-7))).add
    ((isHermitian_one.sub hp).smul (Complex.conj_ofReal 2))

omit [Fintype n] in
private theorem gap (Ω : EuclideanSpace ℂ n) :
    (H Ω - ((-7 : ℝ) : ℂ) • 1 - ((2 : ℝ) : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
  rw [H, add_sub_cancel_left, sub_self]
  exact PosSemidef.zero

private theorem ground (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1) :
    H Ω *ᵥ WithLp.ofLp Ω = ((-7 : ℝ) : ℂ) • WithLp.ofLp Ω := by
  have hself : ⟪Ω, Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    simp
  have hlin : toEuclideanLin (H Ω) Ω = ((-7 : ℝ) : ℂ) • Ω := by
    simp only [H, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, toLpLin_one, LinearMap.id_apply,
      toEuclideanLin_vecMulVec_star_self_apply, hself, one_smul, sub_self, smul_zero,
      add_zero]
  exact congrArg WithLp.ofLp hlin

private theorem phase_overlap (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1) :
    ⟪I • Ω, toEuclideanLin (1 : Matrix n n ℂ) Ω⟫_ℂ = -I := by
  simp [inner_smul_left, inner_self_eq_norm_sq_to_K, hΩ]

-- Hermitian input does not make the overlap real.
example (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1) :
    ⟪I • Ω, toEuclideanLin (1 : Matrix n n ℂ) Ω⟫_ℂ ≠
      star ⟪I • Ω, toEuclideanLin (1 : Matrix n n ℂ) Ω⟫_ℂ := by
  rw [phase_overlap Ω hΩ]
  intro heq
  have him := congrArg Complex.im heq
  norm_num at him

-- Constants are chosen before the scale, dimension, vectors, and input matrix.
-- Ground and gap hypotheses are proved for the constructed Hamiltonians.
example :
    ∃ A T₀ : ℝ, 0 < A ∧ 0 < T₀ ∧
      ∀ b L : ℝ, 0 ≤ b → 1 ≤ L →
        let h := Real.toNNReal (A * (1 + b + Real.log L))
        let T := T₀ * (1 + b + Real.log L)
        (h : ℝ) = A * (1 + b + Real.log L) ∧ 0 < (h : ℝ) ∧ 0 ≤ T ∧
          ∀ (m : Type) [Fintype m] [DecidableEq m] (Ψ Φ : EuclideanSpace ℂ m),
            ‖Ψ‖ = 1 → ‖Φ‖ = 1 → ∀ W : Matrix m m ℂ, ‖W‖ ≤ 1 →
              let M := gaussianIntertwinerTruncated h T (H Φ) (H Ψ) W
              let z := ⟪Φ, toEuclideanLin W Ψ⟫_ℂ
              ‖M‖ ≤ 1 ∧
                ‖toEuclideanLin M Ψ - z • Φ‖ ≤
                  3 * Real.exp (-10 * b) * L ^ (-(1 / 2 : ℝ)) ∧
                ‖toEuclideanLin Mᴴ Φ - star z • Ψ‖ ≤
                  3 * Real.exp (-10 * b) * L ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨A, T₀, hA, hT₀, hscale⟩ :=
    exists_uniform_truncated_ground_estimate two_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine ⟨A, T₀, hA, hT₀, ?_⟩
  intro b L hb hL
  have hs := hscale b L hb hL
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩
  intro m _ _ Ψ Φ hΨ hΦ W hW
  exact hs.2.2.2 m (H Φ) (H Ψ) W (hermitian Φ) (hermitian Ψ) hW
    (-7) Ψ Φ hΨ hΦ (ground Ψ hΨ) (ground Φ hΦ) (gap Ψ) (gap Φ)

private noncomputable def Ψ₁ : EuclideanSpace ℂ Unit := PiLp.single 2 () 1

private noncomputable def Ψ₂ : EuclideanSpace ℂ Bool := PiLp.single 2 true 1

private theorem norm_Ψ₁ : ‖Ψ₁‖ = 1 := by simp [Ψ₁]

private theorem norm_Ψ₂ : ‖Ψ₂‖ = 1 := by simp [Ψ₂]

-- One witness pair serves different dimensions and scales. The reverse phase
-- is +I, while the forward phase is -I, at both scales.
example :
    ∃ A T₀ : ℝ, 0 < A ∧ 0 < T₀ ∧
      let M₁ := gaussianIntertwinerTruncated (Real.toNNReal A) T₀ (H (I • Ψ₁)) (H Ψ₁) 1
      let M₂ := gaussianIntertwinerTruncated (Real.toNNReal (A * (3 + Real.log 4)))
        (T₀ * (3 + Real.log 4)) (H (I • Ψ₂)) (H Ψ₂) 1
      let ε := 3 * Real.exp (-20) * (4 : ℝ) ^ (-(1 / 2 : ℝ))
      ‖M₁‖ ≤ 1 ∧ ‖toEuclideanLin M₁ Ψ₁ - (-I) • (I • Ψ₁)‖ ≤ 3 ∧
        ‖toEuclideanLin M₁ᴴ (I • Ψ₁) - I • Ψ₁‖ ≤ 3 ∧
        ‖M₂‖ ≤ 1 ∧ ‖toEuclideanLin M₂ Ψ₂ - (-I) • (I • Ψ₂)‖ ≤ ε ∧
        ‖toEuclideanLin M₂ᴴ (I • Ψ₂) - I • Ψ₂‖ ≤ ε := by
  obtain ⟨A, T₀, hA, hT₀, hscale⟩ :=
    exists_uniform_truncated_ground_estimate two_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hΦ₁ : ‖I • Ψ₁‖ = 1 := by simp [norm_smul, norm_Ψ₁]
  have hΦ₂ : ‖I • Ψ₂‖ = 1 := by simp [norm_smul, norm_Ψ₂]
  have hfirst := (hscale 0 1 (by norm_num) (by norm_num)).2.2.2 Unit
    (H (I • Ψ₁)) (H Ψ₁) 1 (hermitian _) (hermitian _) (by simp)
    (-7) Ψ₁ (I • Ψ₁) norm_Ψ₁ hΦ₁ (ground _ norm_Ψ₁) (ground _ hΦ₁) (gap _) (gap _)
  have hsecond := (hscale 2 4 (by norm_num) (by norm_num)).2.2.2 Bool
    (H (I • Ψ₂)) (H Ψ₂) 1 (hermitian _) (hermitian _) (by simp)
    (-7) Ψ₂ (I • Ψ₂) norm_Ψ₂ hΦ₂ (ground _ norm_Ψ₂) (ground _ hΦ₂) (gap _) (gap _)
  refine ⟨A, T₀, hA, hT₀, ?_⟩
  simp only [phase_overlap Ψ₁ norm_Ψ₁] at hfirst
  simp only [phase_overlap Ψ₂ norm_Ψ₂] at hsecond
  norm_num [Complex.star_def] at hfirst hsecond ⊢
  exact ⟨hfirst.1, hfirst.2.1, hfirst.2.2, hsecond⟩

end GaussianUniformGroundEstimateTest

/--
info: 'GaussianFilter.exists_uniform_truncated_ground_estimate' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.exists_uniform_truncated_ground_estimate
