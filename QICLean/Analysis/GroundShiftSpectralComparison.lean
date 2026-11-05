/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GroundEnergyResidual

/-!
# Spectral comparisons with a derived ground-energy shift

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
