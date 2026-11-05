/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import QICLean.Analysis.EuclideanEigenvectorBasis
import QICLean.Analysis.LowEnergyPerturbation

/-!
# Buffered low-energy subspaces under a global norm perturbation

A global operator-norm error gives two directed low-energy comparisons after enlarging the
energy cutoff by a positive buffer. The spectrum between the cutoffs is unrestricted. The
proof reuses the finite-window perturbation theorem and the canonical Hermitian eigenbasis.
This is a quantitative auxiliary to ALVV, arXiv:1602.08828v2, `lem:hard-trunc`, lines 955–968,
and the approximating Hamiltonian in `t:aisefficient`, lines 1412–1420. The finite window count
is retained as in `docs/paper-gaps/alvv16_hard_truncation_windows.tex`.
-/

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

private theorem buffered_spectral_norm_perturbation
    {ι : Type*} [Fintype ι] [DecidableEq ι] {H B : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hB : B.IsHermitian) (U c xi w : ℝ)
    (hHU : ‖H‖ ≤ U) (hxi : 0 < xi) (hw : 0 < w) (herr : ‖H - B‖ ≤ xi) :
    let a := min (c - 1) (-U)
    let n := ⌈(c - a) / (2 * xi)⌉₊
    let delta := (n : ℝ) * (2 * xi) ^ 2 / (w + xi) ^ 2
    Submodule.IsCloseTo delta
      (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues (c + w))
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues c) := by
  intro a n delta
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) H
  let S := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) B
  have hD : ‖T - S‖ ≤ xi := by
    simpa only [T, S, Matrix.cstar_norm_def, map_sub] using herr
  have hlow (j : ι) : a ≤ hH.eigenvalues j := by
    let : Nonempty ι := ⟨j⟩
    have hb : |hH.eigenvalues j| ≤ ‖H‖ := by
      simpa only [Real.norm_eq_abs] using
        spectrum.norm_le_norm_of_mem (hH.eigenvalues_mem_spectrum_real j)
    exact (min_le_right _ _).trans ((neg_le_neg hHU).trans (abs_le.mp hb).1)
  refine Submodule.isCloseTo_spectralSpanLE_of_perturbation
    (H := T.toLinearMap) (H' := S.toLinearMap) (c := c) (c' := c + w)
    (ξ := xi) (h := xi) (m := a) (δ := delta)
    hH.eigenvectorBasis hB.eigenvectorBasis hH.eigenvalues hB.eigenvalues
    (fun j ↦ hH.toEuclideanCLM_eigenvectorBasis j)
    (fun j ↦ hB.toEuclideanCLM_eigenvectorBasis j)
    ?_ hxi (fun j _ ↦ hlow j)
    ((min_le_left (c - 1) (-U)).trans_lt (by linarith))
    (le_add_of_nonneg_right hw.le) ?_
  · intro phi _hphi
    exact ((T - S).le_opNorm phi).trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg phi))
  · dsimp only [delta, n]
    rw [show c + w - c + xi = w + xi by ring,
      div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt (add_pos hw hxi)))]
    nlinarith only []

/-- A global norm approximation gives both directed buffered low-energy comparisons.
The loss depends on the original matrix and the error budget, before the approximant.
No gap or eigenvalue-count assumption is imposed between the cutoffs. Auxiliary to ALVV,
arXiv:1602.08828v2, `lem:hard-trunc` and `t:aisefficient`, lines 955–968 and 1412–1420. -/
theorem IsHermitian.isCloseTo_spectralSpanLE_pair_of_norm_sub_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {H B : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hB : B.IsHermitian) (c xi w : ℝ)
    (hxi : 0 < xi) (hw : 0 < w) (herr : ‖H - B‖ ≤ xi) :
    let U := ‖H‖ + xi
    let a := min (c - 1) (-U)
    let n := ⌈(c - a) / (2 * xi)⌉₊
    let delta := (n : ℝ) * (2 * xi) ^ 2 / (w + xi) ^ 2
    Submodule.IsCloseTo delta
      (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues (c + w))
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues c) ∧
    Submodule.IsCloseTo delta
      (Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues (c + w))
      (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues c) := by
  intro U a n delta
  have herrRev : ‖B - H‖ ≤ xi := by
    rw [norm_sub_rev]
    exact herr
  have hBU : ‖B‖ ≤ U := by
    calc
      ‖B‖ = ‖(B - H) + H‖ := by rw [sub_add_cancel]
      _ ≤ ‖B - H‖ + ‖H‖ := norm_add_le _ _
      _ ≤ xi + ‖H‖ := _root_.add_le_add herrRev (le_refl ‖H‖)
      _ = U := by dsimp only [U]; ring
  constructor
  · exact buffered_spectral_norm_perturbation hH hB U c xi w
      (le_add_of_nonneg_right hxi.le) hxi hw herr
  · exact buffered_spectral_norm_perturbation hB hH U c xi w
      hBU hxi hw herrRev

end Matrix
