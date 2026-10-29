/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.ViableSubspaceBootstrap

/-!
# Sampling between two improving targets

This conditional auxiliary retains the actual Haar-coordinate sample and its
actual image under a fixed finite family. The input approximates the original
upper target. It is transferred to the nearby upper improving target before
sampling, improved toward the lower improving target, and only then transferred
to the original lower target. The probability and error estimates remain explicit
premises; no physical filter or low-density dimension bound is asserted.

The source is ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`,
lines 1112–1128, using Lemma `l:rs`, lines 532–552, and Theorem `t:aisgapless`,
lines 1027–1041.

**Local fix (strict dimension decrease and sampling constants):** the integer
sample size is `p / (2 * D^2)`, so the actual image has dimension at most `p/2`.
The branch `p ≥ 4D²` makes the sample nonzero. The corrected complex-sphere
exponent is retained. See `docs/paper-gaps/alvv16_bootstrap_constants.tex` and
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

open scoped TensorProduct InnerProductSpace
open Module

namespace Submodule

variable {M F : Type*}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- A successful actual Haar sample, followed by one chosen improving family,
gives the corrected dimension decrease between two original targets. The
probability and final error premises are explicit. This is an abstract
auxiliary to ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`,
lines 1112–1128; it does not construct the physical family or calibrate a
dyadic count envelope. -/
theorem exists_isViable_nested_randomSubspace_finrank_le_half
    {D p : ℕ} {Delta : ℝ}
    {Gplus Gminus Thi Tlo : Submodule ℂ (M ⊗[ℂ] F)}
    (hupper : IsCloseTo (1 / 200) Gplus Thi)
    (hlower : IsCloseTo (1 / 200) Tlo Gminus)
    (A : Fin (D ^ 2) → M →L[ℂ] M)
    (himprove : ∀ delta < 1, ∀ S : Submodule ℂ M,
      IsViable delta S Thi →
      IsViable (Delta / (1 - delta) ^ 2)
        (⨆ i, S.map (A i : M →ₗ[ℂ] M)) Tlo)
    (hD : 2 ≤ D) (hDelta : 0 ≤ Delta) (hp : 4 * D ^ 2 ≤ p)
    {W : Submodule ℂ M} (hW : IsViable (3 / 200) W Gplus)
    (hpW : p ≤ Module.finrank ℂ W) :
    let Q : ℕ := Module.finrank ℂ W
    let s : ℕ := p / (2 * D ^ 2)
    let alpha : ℝ := (1 - 1 / 25) * (s : ℝ) / (8 * (Q : ℝ))
    (1 + 2 / Real.sqrt alpha) ^ (2 * Module.finrank ℂ Thi) * Q *
      Real.exp (-((s : ℝ) / 16)) < 1 →
    Delta / alpha ^ 2 ≤ 1 / 400 →
    let Coord : Finset (Fin Q) := Finset.univ.map
      (Fin.castLEEmb ((Nat.div_le_self p (2 * D ^ 2)).trans hpW))
    ∃ U : Matrix.unitaryGroup (Fin Q) ℂ,
      let sample := randomSubspace (stdOrthonormalBasis ℂ W) Coord U
      let image : Submodule ℂ M := ⨆ i, sample.map (A i : M →ₗ[ℂ] M)
      1 ≤ s ∧ 0 < alpha ∧ sample ≤ W ∧ Module.finrank ℂ sample = s ∧
      IsViable (1 - alpha) sample Thi ∧ Module.finrank ℂ image ≤ p / 2 ∧
      IsViable (2 * (Delta / alpha ^ 2 + 1 / 200)) image Gminus ∧
      IsViable (3 / 200) image Gminus := by
  intro Q s alpha hfailure herror Coord
  have hden : 0 < 2 * D ^ 2 := by positivity
  have hs1 : 1 ≤ s := (Nat.le_div_iff_mul_le hden).mpr (by nlinarith)
  have hsQ : s ≤ Q := (Nat.div_le_self p (2 * D ^ 2)).trans hpW
  have hQpos : (0 : ℝ) < Q := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hs1.trans hsQ))
  have halpha : 0 < alpha := by positivity
  have hWplus : IsViable (1 / 25) W Thi :=
    (IsCloseTo.trans hW hupper (by norm_num)).of_le (by norm_num)
  have hcard : Coord.card = s := by simp [Coord, s]
  have hfailure' :
      (1 + 2 / Real.sqrt ((1 - (1 / 25 : ℝ)) * Coord.card /
        (8 * Fintype.card (Fin Q)))) ^ (2 * Module.finrank ℂ Thi) *
        Fintype.card (Fin Q) * Real.exp (-((Coord.card : ℝ) / 16)) < 1 := by
    simpa only [hcard, Fintype.card_fin, alpha] using hfailure
  obtain ⟨U, hU⟩ := exists_isViable_randomSubspace
    (stdOrthonormalBasis ℂ W) Coord hWplus hfailure'
  let sample := randomSubspace (stdOrthonormalBasis ℂ W) Coord U
  have hsample : IsViable (1 - alpha) sample Thi := by
    simpa only [hcard, Fintype.card_fin, alpha] using hU
  let image : Submodule ℂ M := ⨆ i, sample.map (A i : M →ₗ[ℂ] M)
  have hraw : IsViable (Delta / alpha ^ 2) image Tlo := by
    simpa only [sub_sub_cancel] using
      himprove (1 - alpha) (by linarith) sample hsample
  have hresult : IsViable (2 * (Delta / alpha ^ 2 + 1 / 200)) image Gminus :=
    IsCloseTo.trans hraw hlower (div_nonneg hDelta (sq_nonneg _))
  have hsampledim : Module.finrank ℂ sample = s := by
    simpa only [hcard] using finrank_randomSubspace (stdOrthonormalBasis ℂ W) Coord U
  have hmaps (i : Fin (D ^ 2)) :
      Module.finrank ℂ (sample.map (A i : M →ₗ[ℂ] M)) ≤ s :=
    (finrank_map_le _ _).trans hsampledim.le
  have himagedim : Module.finrank ℂ image ≤ D ^ 2 * s :=
    (finrank_iSup_le_sum _).trans (by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hmaps i))
  have hdiv : s * (2 * D ^ 2) ≤ p := Nat.div_mul_le_self p (2 * D ^ 2)
  have hhalf : D ^ 2 * s ≤ p / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr (by nlinarith only [hdiv])
  exact ⟨U, hs1, halpha, randomSubspace_le (stdOrthonormalBasis ℂ W) Coord U,
    hsampledim, hsample, himagedim.trans hhalf, hresult,
    hresult.of_le (by linarith only [herror])⟩

end Submodule
