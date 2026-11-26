/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Order.LowEnergyPerturbation
import QICLean.Analysis.Subspace.ViableSubspace
import Mathlib.Analysis.Matrix.Order
import QICLean.Spectral.Eigenvalue.EuclideanEigenvectorBasis

/-!
# Stability of a finite low spectral cluster under norm perturbation

Two buffered comparisons transfer a separated low cluster to the actual
Hermitian approximating matrix. The directed losses retain their two
finite window counts. A dimension comparison identifies the approximant's
own low space at every intermediate cutoff; no residual on that new space
is supplied.

This is a finite-dimensional auxiliary for ALVV, arXiv:1602.08828v2,
`t:aisefficient`, lines 1412–1420. It concerns the approximating matrix's
own invariant target, rather than asserting that the exact soft target is
invariant under an approximate matrix. The corrected window count is
recorded in `docs/paper-gaps/alvv16_hard_truncation_windows.tex`.

It also contains the following results.

* `Matrix.IsHermitian.isCloseTo_spectralSpanLE_pair_of_norm_sub_le`: buffered low-energy subspaces
  under a global norm perturbation.
-/

section BufferedSpectralNormPerturbation

/-!
## Buffered low-energy subspaces under a global norm perturbation

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

end BufferedSpectralNormPerturbation

section ClusterNormPerturbation

open scoped Matrix.Norms.L2Operator

namespace Matrix.IsHermitian

/-- A global norm approximation preserves a separated low cluster after
inward movement of its endpoints. Both directed projection losses retain
their actual finite window counts. The new low cluster has the same
dimension and is the same space at every intervening cutoff. Negative
spectra, repeated eigenvalues and empty index types are allowed.
Auxiliary to ALVV, arXiv:1602.08828v2, `t:aisefficient`, lines 1412–1420;
the approximating operator, rather than the exact soft operator, determines
its invariant target. -/
theorem spectral_cluster_of_norm_sub_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (a b c d xi : ℝ)
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) (hxi : 0 < xi)
    (herr : ‖A - B‖ ≤ xi)
    (hcluster : Submodule.spectralSpanLE hA.eigenvectorBasis hA.eigenvalues a =
      Submodule.spectralSpanLE hA.eigenvectorBasis hA.eigenvalues d) :
    let U := ‖A‖ + xi
    let nLo := ⌈(a - min (a - 1) (-U)) / (2 * xi)⌉₊
    let nHi := ⌈(c - min (c - 1) (-U)) / (2 * xi)⌉₊
    let deltaLo := (nLo : ℝ) * (2 * xi) ^ 2 / (b - a + xi) ^ 2
    let deltaHi := (nHi : ℝ) * (2 * xi) ^ 2 / (d - c + xi) ^ 2
    deltaLo < 1 → deltaHi < 1 →
    let original := Submodule.spectralSpanLE hA.eigenvectorBasis hA.eigenvalues a
    let low := Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues b
    let high := Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues c
    low = high ∧ Module.finrank ℂ low = Module.finrank ℂ original ∧
      Submodule.IsCloseTo deltaLo low original ∧
      Submodule.IsCloseTo deltaHi original low ∧
      ∀ cutoff : ℝ, b ≤ cutoff → cutoff ≤ c →
        Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues cutoff = low ∧
        Submodule.IsCloseTo deltaLo
          (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues cutoff) original ∧
        Submodule.IsCloseTo deltaHi original
          (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues cutoff) := by
  intro U nLo nHi deltaLo deltaHi hLo hHi original low high
  have hlow : Submodule.IsCloseTo deltaLo low original := by
    simpa only [show a + (b - a) = b by ring] using
      (hA.isCloseTo_spectralSpanLE_pair_of_norm_sub_le hB a xi (b - a)
        hxi (sub_pos.mpr hab) herr).1
  have hhigh : Submodule.IsCloseTo deltaHi original high := by
    simpa only [show c + (d - c) = d by ring, ← hcluster] using
      (hA.isCloseTo_spectralSpanLE_pair_of_norm_sub_le hB c xi (d - c)
        hxi (sub_pos.mpr hcd) herr).2
  obtain ⟨heq, hintermediate⟩ := Submodule.eq_and_isCloseTo_of_le
    (Submodule.spectralSpanLE_mono_cutoff hB.eigenvectorBasis hB.eigenvalues hbc)
    hlow hhigh hLo hHi
  have hreverse : Submodule.IsCloseTo deltaHi original low :=
    (hintermediate low le_rfl (le_of_eq heq)).2.2
  refine ⟨heq, le_antisymm (hreverse.finrank_le hHi) (hlow.finrank_le hLo),
    hlow, hreverse, ?_⟩
  exact fun cutoff hlo hhi ↦ hintermediate _
    (Submodule.spectralSpanLE_mono_cutoff hB.eigenvectorBasis hB.eigenvalues hlo)
    (Submodule.spectralSpanLE_mono_cutoff hB.eigenvectorBasis hB.eigenvalues hhi)

end Matrix.IsHermitian

end ClusterNormPerturbation
