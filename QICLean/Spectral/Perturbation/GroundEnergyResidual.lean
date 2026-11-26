/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Order.LowEnergyPerturbation
import QICLean.Spectral.Eigenvalue.GroundEnergyBounds

/-!
# An attained energy and a restricted residual

A unit eigenvector below a cutoff belongs to the actual closed spectral span. Its
restricted residual therefore controls the difference between an original lower energy
and its eigenvalue. These are finite-dimensional auxiliary estimates for ALVV,
arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255, and `t:aisefficient`,
lines 1373–1392. No small residual, successful spectral comparison or gap is supplied
as a conclusion of an independently assumed approximation.

It also contains the following results.

* `Matrix.ground_shift_and_isCloseTo_pair_of_restricted_residuals`: spectral comparisons with a
  derived ground-energy shift.
-/

section GroundEnergyResidual

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

end GroundEnergyResidual

section GroundShiftSpectralComparison

/-!
## Spectral comparisons with a derived ground-energy shift

Two actual restricted residuals and an actual normalized ground eigenvector determine
an energy shift and both directed buffered spectral comparisons. The finite window count
uses the width above a proved lower energy, not the absolute value of a ground energy.
These are corrected finite-dimensional auxiliaries for ALVV, arXiv:1602.08828v2,
`lem:exp-approx` and `t:aisefficient`, lines 1195–1255 and 1373–1392.
No energy-shift estimate, spectral gap or successful subspace approximation is assumed.
-/

open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

private theorem lower_le_eigenvalue_of_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (e : ℝ)
    (hlo : (A - (e : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (a : n → ℝ)
    (hA : ∀ j, toEuclideanCLM (n := n) (𝕜 := ℂ) A (b j) = (a j : ℂ) • b j) (j : n) :
    e ≤ a j := by
  have h := energy_sub_eigenvalue_le_norm_spectral_residual A A e (a j) (a j)
    hlo b a hA (b j) (b.norm_eq_one j) (hA j) le_rfl
  have hzero : e - a j ≤ 0 := by simpa [ContinuousLinearMap.domRestrict] using h
  exact sub_nonpos.mp hzero

private theorem restricted_residual_apply_bound
    {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ n)) (xi : ℝ)
    (hres : ‖(toEuclideanCLM (n := n) (𝕜 := ℂ) (A - B)).domRestrict S‖ ≤ xi)
    (x : EuclideanSpace ℂ n) (hx : x ∈ S) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A x -
        toEuclideanCLM (n := n) (𝕜 := ℂ) B x‖ ≤ xi * ‖x‖ := by
  have h := ((toEuclideanCLM (n := n) (𝕜 := ℂ) (A - B)).domRestrict S).le_opNorm ⟨x, hx⟩
  change ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (A - B) x‖ ≤
    ‖(toEuclideanCLM (n := n) (𝕜 := ℂ) (A - B)).domRestrict S‖ * ‖x‖ at h
  rw [map_sub, _root_.sub_apply] at h
  rw [map_sub] at hres
  exact h.trans (mul_le_mul_of_nonneg_right hres (norm_nonneg x))

private theorem window_loss_bound {k : ℕ} {xi w h d : ℝ}
    (hw : 0 < w) (hh : 0 < h) (hd : w ≤ d) :
    (k : ℝ) * (xi + h) ^ 2 ≤
      ((k : ℝ) * (xi + h) ^ 2 / (w + h) ^ 2) * (d + h) ^ 2 := by
  have hden : 0 < (w + h) ^ 2 := sq_pos_of_pos (add_pos hw hh)
  have hpow : (w + h) ^ 2 ≤ (d + h) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hd]) 2
  calc
    _ = ((k : ℝ) * (xi + h) ^ 2 / (w + h) ^ 2) * (w + h) ^ 2 :=
      (div_mul_cancel₀ _ hden.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Actual lower energy matrices and a normalized ground eigenvector derive the energy
shift before the two buffered low-space comparisons. Both residuals concern the actual
matrices on their actual eigenbasis spans. The positive window width covers zero source
width without an empty-window count. Corrected auxiliary to ALVV, arXiv:1602.08828v2,
`lem:exp-approx` and `t:aisefficient`, lines 1195–1255 and 1373–1392. -/
theorem ground_shift_and_isCloseTo_pair_of_restricted_residuals
    {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ)
    (e mu eta xiA xiB h w : ℝ)
    (hAlo : (A - (e : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hBlo : (B - (mu : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (bA bB : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (aA aB : n → ℝ)
    (hA : ∀ j, toEuclideanCLM (n := n) (𝕜 := ℂ) A (bA j) = (aA j : ℂ) • bA j)
    (hB : ∀ j, toEuclideanCLM (n := n) (𝕜 := ℂ) B (bB j) = (aB j : ℂ) • bB j)
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1)
    (hBx : toEuclideanCLM (n := n) (𝕜 := ℂ) B x = (mu : ℂ) • x)
    (hmue : mu ≤ e) (heta : 0 ≤ eta) (hh : 0 < h) (hw : 0 < w)
    (hresA : ‖(toEuclideanCLM (n := n) (𝕜 := ℂ) (A - B)).domRestrict
      (Submodule.spectralSpanLE bA aA (e + eta))‖ ≤ xiA)
    (hresB : ‖(toEuclideanCLM (n := n) (𝕜 := ℂ) (A - B)).domRestrict
      (Submodule.spectralSpanLE bB aB (mu + eta))‖ ≤ xiB) :
    let k := ⌈(eta + h) / (2 * h)⌉₊
    let lossA := (k : ℝ) * (xiA + h) ^ 2 / (w + h) ^ 2
    let lossB := (k : ℝ) * (xiB + h) ^ 2 / (w + h) ^ 2
    0 ≤ e - mu ∧ e - mu ≤ xiB ∧
      Submodule.IsCloseTo lossA
        (Submodule.spectralSpanLE bB aB (mu + eta + xiB + w))
        (Submodule.spectralSpanLE bA aA (e + eta)) ∧
      Submodule.IsCloseTo lossB
        (Submodule.spectralSpanLE bA aA (e + eta + w))
        (Submodule.spectralSpanLE bB aB (mu + eta)) := by
  intro k lossA lossB
  have hshift : e - mu ≤ xiB :=
    (energy_sub_eigenvalue_le_norm_spectral_residual A B e mu (mu + eta)
      hAlo bB aB hB x hx hBx (by linarith only [heta])).trans hresB
  have hpointA := restricted_residual_apply_bound A B
    (Submodule.spectralSpanLE bA aA (e + eta)) xiA hresA
  have hpointB (v : EuclideanSpace ℂ n)
      (hv : v ∈ Submodule.spectralSpanLE bB aB (mu + eta)) :
      ‖toEuclideanCLM (n := n) (𝕜 := ℂ) B v -
        toEuclideanCLM (n := n) (𝕜 := ℂ) A v‖ ≤ xiB * ‖v‖ := by
    simpa only [norm_sub_rev] using restricted_residual_apply_bound A B
      (Submodule.spectralSpanLE bB aB (mu + eta)) xiB hresB v hv
  refine ⟨sub_nonneg.mpr hmue, hshift, ?_, ?_⟩
  · refine Submodule.isCloseTo_spectralSpanLE_of_perturbation bA bB aA aB
      (m := e - h) hA hB hpointA hh ?_ (by linarith only [heta, hh])
        (by linarith only [hshift, hw]) ?_
    · intro j _
      exact (sub_le_self e hh.le).trans (lower_le_eigenvalue_of_posSemidef A e hAlo bA aA hA j)
    · have hc : (e + eta) - (e - h) = eta + h := by ring
      change (⌈((e + eta) - (e - h)) / (2 * h)⌉₊ : ℝ) * (xiA + h) ^ 2 ≤
        lossA * ((mu + eta + xiB + w) - (e + eta) + h) ^ 2
      rw [hc]
      exact window_loss_bound hw hh (by linarith only [hshift])
  · refine Submodule.isCloseTo_spectralSpanLE_of_perturbation bB bA aB aA
      (m := mu - h) hB hA hpointB hh ?_ (by linarith only [heta, hh])
        (by linarith only [hmue, hw]) ?_
    · intro j _
      exact (sub_le_self mu hh.le).trans (lower_le_eigenvalue_of_posSemidef B mu hBlo bB aB hB j)
    · have hc : (mu + eta) - (mu - h) = eta + h := by ring
      change (⌈((mu + eta) - (mu - h)) / (2 * h)⌉₊ : ℝ) * (xiB + h) ^ 2 ≤
        lossB * ((e + eta + w) - (mu + eta) + h) ^ 2
      rw [hc]
      exact window_loss_bound hw hh (by linarith only [hmue])

end Matrix

end GroundShiftSpectralComparison
