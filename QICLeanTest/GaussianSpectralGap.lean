/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.SpectralGap

/-!
# Consumers of the Gaussian spectral gap estimate

These checks include arbitrary input norm, zero Gaussian width, an exactly
synthesized Gaussian vector, and a two-dimensional Hamiltonian at negative
energy with a non-real, unnormalized input. The shifted projector fixture adapts
`QICLeanTest/PositiveGapUniqueness.lean`; no Gaussian integral is assumed here.
-/

open Complex Matrix
open scoped InnerProductSpace ComplexOrder

namespace GaussianSpectralGapTest

variable {n : Type*} [Fintype n] [DecidableEq n]

-- The endpoint h = 0 gives the ordinary bound for an orthogonal projection residual.
example {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ Δ : ℝ}
    {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : H *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω)
    (hgap : (H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) (x : EuclideanSpace ℂ n) :
    ‖x - ⟪Ω, x⟫_ℂ • Ω‖ ≤ ‖x‖ := by
  simpa using GaussianFilter.norm_sub_ground_le_of_coefficients hH hΩ hHΩ hgap
    hΔ (h := 0) le_rfl (x := x) (y := x) (fun _ => by simp)

private noncomputable def gaussianVector {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (E₀ h : ℝ) (x : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  hH.eigenvectorBasis.repr.symm (WithLp.toLp 2 fun k =>
    (Real.exp (-h * (hH.eigenvalues k - E₀) ^ 2 / 2) : ℂ) *
      ⟪hH.eigenvectorBasis k, x⟫_ℂ)

private theorem gaussianVector_coeff {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (E₀ h : ℝ) (x : EuclideanSpace ℂ n) (k : n) :
    ⟪hH.eigenvectorBasis k, gaussianVector hH E₀ h x⟫_ℂ =
      (Real.exp (-h * (hH.eigenvalues k - E₀) ^ 2 / 2) : ℂ) *
        ⟪hH.eigenvectorBasis k, x⟫_ℂ := by
  rw [← hH.eigenvectorBasis.repr_apply_apply, gaussianVector,
    LinearIsometryEquiv.apply_symm_apply]

-- Coefficients are verified from an explicit synthesized vector, not postulated.
example {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ Δ h : ℝ}
    {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : H *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω)
    (hgap : (H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) (hh : 0 ≤ h) (x : EuclideanSpace ℂ n) :
    ‖gaussianVector hH E₀ h x - ⟪Ω, x⟫_ℂ • Ω‖ ≤
      Real.exp (-h * Δ ^ 2 / 2) * ‖x‖ :=
  GaussianFilter.norm_sub_ground_le_of_coefficients hH hΩ hHΩ hgap hΔ hh
    (gaussianVector_coeff hH E₀ h x)

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

-- The Hamiltonian has energies -7 and -5. The input has norm two and a complex phase.
example :
    let Ω := EuclideanSpace.basisFun Bool ℂ false
    let x := (2 * I) • EuclideanSpace.basisFun Bool ℂ true
    ‖gaussianVector (hermitian Ω) (-7) 2 x - ⟪Ω, x⟫_ℂ • Ω‖ ≤
      Real.exp (-4) * 2 := by
  dsimp only
  have hΩ : ‖EuclideanSpace.basisFun Bool ℂ false‖ = 1 :=
    (EuclideanSpace.basisFun Bool ℂ).orthonormal.1 false
  have hx : ‖(2 * I) • EuclideanSpace.basisFun Bool ℂ true‖ = 2 := by
    rw [norm_smul, (EuclideanSpace.basisFun Bool ℂ).orthonormal.1 true]
    norm_num [norm_mul]
  have h := GaussianFilter.norm_sub_ground_le_of_coefficients
    (hermitian _) hΩ (ground _ hΩ) (gap _) two_pos (by norm_num : (0 : ℝ) ≤ 2)
    (gaussianVector_coeff (hermitian _) (-7) 2
      ((2 * I) • EuclideanSpace.basisFun Bool ℂ true))
  simpa only [hx, show (- (2 : ℝ) * 2 ^ 2 / 2) = -4 by norm_num] using h

end GaussianSpectralGapTest

/--
info: 'GaussianFilter.eigenvector_ground_or_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.eigenvector_ground_or_gap

/--
info: 'GaussianFilter.norm_sub_ground_le_of_coefficients' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.norm_sub_ground_le_of_coefficients
