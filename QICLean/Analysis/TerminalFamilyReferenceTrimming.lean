/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableHalfSamplingParameters
import QICLean.Analysis.ViableSubspaceOrder
import QICLean.Analysis.ViableSubspaceSpectralProjector
import QICLean.Analysis.ViableSubspaceReferenceTrimming
import QICLean.Analysis.ViableSubspaceTrimmingInvariance

/-!
# A deterministic terminal family image with original-target reference trimming

After a stopped resampling loop, including a loop that takes no active round,
the same full improving family is applied once before collective trimming.
Its exact improving-target error is retained. All target and reference data
are fixed before the current input space; no further sample is selected.

This supports ALVV, arXiv:1602.08828v2, the resampling description at
lines 749–755 and the reference argument at lines 1801–1813.
This module treats a repeated-resampling variant of the merge procedure
sketched at arXiv:1602.08828v2, lines 711–755; Figure `fig:merge-prime` and
Theorem `t:alg1` are not formalized here. See
`docs/paper-gaps/alvv16_bootstrap_constants.tex`.
**Local fix (trimming constant):** The estimate retains the corrected
increment recorded in `docs/paper-gaps/alvv16_trimming_constant.tex`.
-/

open Module

namespace Entropy

variable {V β X ι : Type*} [Fintype V] [DecidableEq V]
  [Fintype β] [Fintype ι] {n : V → ℕ}

/-- A full finite-family image and its literal collective trim have the
same unconditional cardinality-times-dimension bound. No target, viability,
monotone-cut or positive-threshold premise is needed. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:er`, lines 597–622, and trimming, lines 648–655. -/
theorem finrank_family_image_trim_le
    (C : ℕ → Finset V) (xi : ℝ) (m : ℕ)
    (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n))
    (W : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))) :
    let image : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) :=
      ⨆ i, W.map (A i : _ →ₗ[ℂ] _)
    let output := trimSubspace C xi
      (fun i ↦ (stdOrthonormalBasis ℂ image i : EuclideanSpace ℂ (SiteConfig n))) m
    finrank ℂ image ≤ Fintype.card ι * finrank ℂ W ∧
      finrank ℂ output ≤ Fintype.card ι * finrank ℂ W := by
  intro image output
  have hdim : finrank ℂ image ≤ Fintype.card ι * finrank ℂ W :=
    Submodule.finrank_iSup_map_le_card_mul W (fun i ↦ (A i).toLinearMap)
  refine ⟨hdim, ?_⟩
  change finrank ℂ (trimSubspace C xi
    (fun i ↦ (stdOrthonormalBasis ℂ image i : EuclideanSpace ℂ (SiteConfig n))) m) ≤ _
  rw [trimSubspace_eq_map_of_orthonormalBasis]
  exact (Submodule.finrank_map_le _ _).trans hdim

/-- One application of the same full family and the same original-reference
trim restores the original-target error after a stopped resampling loop.
The exact improving-target error is retained, without a sign assumption on
Delta. This is a conditional terminal auxiliary to ALVV,
arXiv:1602.08828v2, lines 749–755 and 1801–1813, not a runtime theorem. -/
theorem isCloseTo_terminal_family_reference_trim
    {D m bRef : ℕ} {Delta epsilonRef xi : ℝ}
    {Graw R : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β))}
    (x0 : X) (T : X → Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β)))
    (A : ι → EuclideanSpace ℂ (SiteConfig n) →L[ℂ] EuclideanSpace ℂ (SiteConfig n))
    (hcard : Fintype.card ι ≤ D ^ 2)
    (hRawSoft : ∀ x, Submodule.IsCloseTo (1 / 200) Graw (T x))
    (hSoftRaw : ∀ x, Submodule.IsCloseTo (1 / 200) (T x) Graw)
    (hA : ∀ x delta, delta < 1 →
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)),
      Submodule.IsCloseTo delta (Submodule.prodExt S β) (T x) →
      Submodule.IsCloseTo (Delta / (1 - delta) ^ 2)
        (Submodule.prodExt (⨆ i, S.map (A i : _ →ₗ[ℂ] _)) β) (T x))
    (hD : 2 ≤ D) (hDelta : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (C : ℕ → Finset V) (hC : Monotone C) (hxi : 0 < xi)
    (hepsilonRef0 : 0 ≤ epsilonRef) (hepsilonRef : epsilonRef ≤ 1 / 100000)
    (hRawRef : Submodule.IsCloseTo epsilonRef Graw R)
    (hRefRaw : Submodule.IsCloseTo epsilonRef R Graw)
    (hRank : ∀ t ∈ R, ∀ j < m,
      Matrix.schmidtRank (WithLp.ofLp (cutEnvVector (C j) t)) ≤ bRef)
    (hbudget : xi * Real.sqrt ((m : ℝ) * (bRef : ℝ)) ≤ 1 / 1000)
    (W : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)))
    (hW : Submodule.IsCloseTo 0.04 (Submodule.prodExt W β) Graw) :
    let image : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) :=
      ⨆ i, W.map (A i : _ →ₗ[ℂ] _)
    let output := trimSubspace C xi
      (fun i ↦ (stdOrthonormalBasis ℂ image i : EuclideanSpace ℂ (SiteConfig n))) m
    (∀ x, Submodule.IsCloseTo (Delta / (91 / 100 : ℝ) ^ 2)
      (Submodule.prodExt image β) (T x)) ∧
    Submodule.IsCloseTo (27 / 2500) (Submodule.prodExt image β) Graw ∧
    Submodule.IsCloseTo (3 / 200) (Submodule.prodExt output β) Graw ∧
    finrank ℂ image ≤ D ^ 2 * finrank ℂ W ∧
    finrank ℂ output ≤ D ^ 2 * finrank ℂ W := by
  intro image output
  have hImageTarget (x) :
      Submodule.IsCloseTo (Delta / (91 / 100 : ℝ) ^ 2)
        (Submodule.prodExt image β) (T x) := by
    have hInput : Submodule.IsCloseTo (9 / 100)
        (Submodule.prodExt W β) (T x) :=
      by
        simpa only [show (2 * (0.04 + 1 / 200) : ℝ) = 9 / 100 by norm_num] using
          Submodule.IsCloseTo.trans hW (hRawSoft x) (by norm_num)
    have hh := hA x (9 / 100) (by norm_num) W hInput
    simpa only [show (1 - 9 / 100 : ℝ) = 91 / 100 by norm_num] using hh
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hsq : (4 : ℝ) ≤ (D : ℝ) ^ 2 := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (D : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hDreal 2
  have hfilter : Delta / (91 / 100 : ℝ) ^ 2 ≤ 1 / 10000 :=
    Real.half_sampling_filter_error_le hDreal hDelta
      ((div_le_iff₀ (by linarith only [hsq] : (0 : ℝ) < (D : ℝ) ^ 2)).mpr
        (by nlinarith only [hsq]))
  have hImageSmall : Submodule.IsCloseTo (1 / 10000)
      (Submodule.prodExt image β) (T x0) :=
    (hImageTarget x0).of_le hfilter
  have hImageBack : Submodule.IsCloseTo (2 * ((1 / 10000) + (1 / 200)))
      (Submodule.prodExt image β) Graw :=
    Submodule.IsCloseTo.trans hImageSmall (hSoftRaw x0) (by norm_num)
  have hImageRaw : Submodule.IsCloseTo (27 / 2500)
      (Submodule.prodExt image β) Graw := hImageBack.of_le (by norm_num)
  have hOutputRaw : Submodule.IsCloseTo (3 / 200)
      (Submodule.prodExt output β) Graw := by
    have ht := isCloseTo_prodExt_trimSubspace_of_reference_weighted hC hxi
      (by norm_num : (0 : ℝ) ≤ 27 / 2500) hepsilonRef0
      (by norm_num : (0 : ℝ) < 1 / 20)
      (stdOrthonormalBasis ℂ image) hImageRaw hRawRef hRefRaw hRank
    exact ht.of_le (Real.half_sampling_trim_error_le le_rfl hepsilonRef hbudget)
  obtain ⟨hImageDim, hOutputDim⟩ := finrank_family_image_trim_le C xi m A W
  have hcount : Fintype.card ι * finrank ℂ W ≤ D ^ 2 * finrank ℂ W :=
    Nat.mul_le_mul_right _ hcard
  exact ⟨hImageTarget, hImageRaw, hOutputRaw,
    hImageDim.trans hcount, hOutputDim.trans hcount⟩

end Entropy
