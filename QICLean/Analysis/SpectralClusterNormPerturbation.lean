/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.BufferedSpectralNormPerturbation
import QICLean.Analysis.LowEnergyOrder
import QICLean.Analysis.ViableSubspaceDimension

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
-/

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
