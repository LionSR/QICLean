/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowEnergyPerturbation
import QICLean.Analysis.GroundEnergyBounds

/-!
# An attained energy and a restricted residual

A unit eigenvector below a cutoff belongs to the actual closed spectral span. Its
restricted residual therefore controls the difference between an original lower energy
and its eigenvalue. These are finite-dimensional auxiliary estimates for ALVV,
arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255, and `t:aisefficient`,
lines 1373–1392. No small residual, successful spectral comparison or gap is supplied
as a conclusion of an independently assumed approximation.
-/

open scoped InnerProductSpace

/-- A lower quadratic-form bound and a residual at one unit eigenvector
give a lower bound for its real eigenvalue. Auxiliary to ALVV,
arXiv:1602.08828v2, lines 955–968 and 1010–1024. -/
theorem real_eigenvalue_ge_of_unit_residual {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B : E → E) (x : E) (e lam ξ : ℝ) (hx : ‖x‖ = 1)
    (hBx : B x = (lam : ℂ) • x)
    (hlower : e * ‖x‖ ^ 2 ≤ (⟪x, A x⟫_ℂ).re)
    (hres : ‖A x - B x‖ ≤ ξ) : e - ξ ≤ lam := by
  have hlam : (⟪x, B x⟫_ℂ).re = lam := by
    rw [hBx, inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
    simp
  have hdiff : (⟪x, A x⟫_ℂ).re - lam ≤ ξ := by
    calc
      (⟪x, A x⟫_ℂ).re - lam = (⟪x, A x - B x⟫_ℂ).re := by
        rw [inner_sub_right, Complex.sub_re, hlam]
      _ ≤ ‖x‖ * ‖A x - B x‖ := re_inner_le_norm (𝕜 := ℂ) x (A x - B x)
      _ ≤ ξ := by simpa only [hx, one_mul] using hres
  have he : e ≤ (⟪x, A x⟫_ℂ).re := by
    simpa only [hx, one_pow, mul_one] using hlower
  linarith


namespace Submodule

/-- An actual eigenvector belongs to every closed spectral span whose cutoff is at
least its eigenvalue, independently of its coordinates in the chosen complete eigenbasis.
Auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem mem_spectralSpanLE_of_eigenvector
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (a : ι → ℝ) (H : E →ₗ[ℂ] E)
    (hH : ∀ j, H (b j) = (a j : ℂ) • b j) (x : E) (mu c : ℝ)
    (hx : H x = (mu : ℂ) • x) (hcut : mu ≤ c) :
    x ∈ spectralSpanLE b a c := by
  apply (mem_spectralSpanLE_iff b a c x).mpr
  intro j hj
  have hcoord := b.repr_apply_of_eigen a hH x j
  rw [hx, map_smul] at hcoord
  change (mu : ℂ) * b.repr x j = (a j : ℂ) * b.repr x j at hcoord
  have hne : (mu : ℂ) ≠ (a j : ℂ) :=
    Complex.ofReal_injective.ne (ne_of_lt (lt_of_le_of_lt hcut hj))
  have hzero : ((mu : ℂ) - (a j : ℂ)) * b.repr x j = 0 := by
    rw [sub_mul, hcoord, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

end Submodule

namespace ContinuousLinearMap

/-- The actual restricted residual bounds an attained eigenvalue's distance below an
original lower quadratic-form bound. No residual estimate or spectral gap is assumed.
Auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem energy_sub_eigenvalue_le_norm_domRestrict
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]
    (A B : E →L[ℂ] E) (b : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (hB : ∀ j, B (b j) = (a j : ℂ) • b j)
    (x : E) (e mu c : ℝ) (hx : ‖x‖ = 1) (hBx : B x = (mu : ℂ) • x)
    (hlower : e * ‖x‖ ^ 2 ≤ (⟪x, A x⟫_ℂ).re) (hcut : mu ≤ c) :
    e - mu ≤ ‖(A - B).domRestrict (Submodule.spectralSpanLE b a c)‖ := by
  have hxS := Submodule.mem_spectralSpanLE_of_eigenvector b a B.toLinearMap hB x mu c hBx hcut
  have hres := ((A - B).domRestrict (Submodule.spectralSpanLE b a c)).le_opNorm ⟨x, hxS⟩
  have hres' : ‖A x - B x‖ ≤ ‖(A - B).domRestrict (Submodule.spectralSpanLE b a c)‖ := by
    change ‖A x - B x‖ ≤
      ‖(A - B).domRestrict (Submodule.spectralSpanLE b a c)‖ * ‖x‖ at hres
    simpa only [hx, mul_one] using hres
  have hbound := real_eigenvalue_ge_of_unit_residual A B x e mu
    ‖(A - B).domRestrict (Submodule.spectralSpanLE b a c)‖ hx hBx hlower hres'
  linarith only [hbound]

end ContinuousLinearMap


open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

/-- An original positive-semidefinite lower bound and an actual unit eigenvector of the
second matrix give an energy-shift bound by the actual restricted residual. The vector's
membership in the low spectral span and the quadratic-form lower bound are derived.
Auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem energy_sub_eigenvalue_le_norm_spectral_residual
    {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (A B : Matrix n n ℂ) (e mu c : ℝ)
    (hlower : (A - (e : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ n)) (a : ι → ℝ)
    (hB : ∀ j, toEuclideanCLM (n := n) (𝕜 := ℂ) B (b j) = (a j : ℂ) • b j)
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1)
    (hBx : toEuclideanCLM (n := n) (𝕜 := ℂ) B x = (mu : ℂ) • x) (hcut : mu ≤ c) :
    e - mu ≤ ‖(toEuclideanCLM (n := n) (𝕜 := ℂ) (A - B)).domRestrict
      (Submodule.spectralSpanLE b a c)‖ := by
  have hform : e * ‖x‖ ^ 2 ≤ (⟪x, toEuclideanCLM (n := n) (𝕜 := ℂ) A x⟫_ℂ).re := by
    have hp := (isPositive_toEuclideanLin_iff.mpr hlower).re_inner_nonneg_right x
    change 0 ≤ (⟪x, toEuclideanCLM (n := n) (𝕜 := ℂ)
      (A - (e : ℂ) • 1) x⟫_ℂ).re at hp
    rw [map_sub, map_smul, map_one, _root_.sub_apply, _root_.smul_apply, one_apply_eq_self,
      inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hx] at hp
    norm_num at hp
    simpa only [hx, one_pow, mul_one] using hp
  have hbound := ContinuousLinearMap.energy_sub_eigenvalue_le_norm_domRestrict
    (toEuclideanCLM (n := n) (𝕜 := ℂ) A) (toEuclideanCLM (n := n) (𝕜 := ℂ) B)
    b a hB x e mu c hx hBx hform hcut
  simpa only [map_sub] using hbound

end Matrix
