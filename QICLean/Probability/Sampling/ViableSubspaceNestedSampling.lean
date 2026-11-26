/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Probability.Sampling.ViableSubspaceBootstrap
import QICLean.Analysis.Parameter.NestedSamplingParameters
import QICLean.Probability.Sampling.ViableSubspaceMinimum
import QICLean.Analysis.Subspace.ViableSubspace
import QICLean.Analysis.Parameter.PolynomialFilterCounts

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
exponent is retained. See `docs/paper-gaps/alvv16_low_density_sampling.tex` and
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.

It also contains the following results.

* `Real.nested_sampling_natural_conditions`: the natural half-size sample for nested targets.
* `Submodule.exists_isViable_finrank_le_of_dyadic_families`,
  `Submodule.exists_isViable_finrank_le_of_dyadic_filter_families`: a strict dimension comparison
  for nested viable targets.
* `Submodule.exists_isViable_nested_sample_of_count_comparison`: an actual nested-target sample from
  a dyadic count comparison.
-/

section ViableSubspaceNestedSampling

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

end ViableSubspaceNestedSampling

section NestedSamplingNaturalParameters

/-!
## The natural half-size sample for nested targets

The sample dimension is the actual natural quotient, rather than an
independently supplied real parameter. The count comparison and calibrated
suppression then imply both numerical sampling conditions. This supports
ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines 1112–1128.

**Local fix (strict decrease and complex sphere nets):** The half-size
quotient permits an image of dimension at most half the lower viable
dimension. The corrected complex-sphere exponent is retained. See
`docs/paper-gaps/alvv16_low_density_sampling.tex` and
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

namespace Real

/-- The actual natural sample size satisfies the strict failure bound and
the final error budget at a bad-to-good dyadic dimension comparison.
This is a numerical auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128; it does not construct the physical
family or identify its target spaces. -/
theorem nested_sampling_natural_conditions {D Dnext r p Q t : ℕ} {Delta : ℝ}
    (hlogD : 100 ≤ log (D : ℝ)) (hr : 1 ≤ r) (ht : t ≤ r)
    (hcount : log (Dnext : ℝ) ≤ (13 / 6) * log (D : ℝ))
    (hbad : r * D ^ 3 < p) (hpQ : p ≤ Q) (hupper : Q ≤ r * Dnext ^ 3)
    (htrade : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000) :
    let s : ℕ := p / (2 * D ^ 2)
    let alpha : ℝ := (1 - 1 / 25) * (s : ℝ) / (8 * (Q : ℝ))
    8 ≤ D ∧ 4 * D ^ 2 ≤ p ∧ 1 ≤ s ∧ 0 < alpha ∧
      (1 + 2 / sqrt alpha) ^ (2 * t) * Q * exp (-((s : ℝ) / 16)) < 1 ∧
      Delta / alpha ^ 2 ≤ 1 / 400 := by
  intro s alpha
  have hDne : D ≠ 0 := by
    intro hz
    norm_num [hz] at hlogD
  have hDn : 0 < D := Nat.pos_of_ne_zero hDne
  have hD0 : (0 : ℝ) < D := Nat.cast_pos.mpr hDn
  have hDR : (8 : ℝ) ≤ D := by
    have hb := log_le_sub_one_of_pos hD0
    linarith only [hlogD, hb]
  have hD8 : 8 ≤ D := by exact_mod_cast hDR
  have hp4 : 4 * D ^ 2 ≤ p := by
    calc
      4 * D ^ 2 ≤ D * D ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = D ^ 3 := by ring
      _ ≤ r * D ^ 3 := by
        have hb := Nat.mul_le_mul_right (D ^ 3) hr
        simpa only [one_mul] using hb
      _ ≤ p := hbad.le
  have hden : 0 < 2 * D ^ 2 := by positivity
  have hs1 : 1 ≤ s := (Nat.le_div_iff_mul_le hden).mpr (by nlinarith only [hp4])
  have hpn : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hbad
  have hQn : 0 < Q := hpn.trans_le hpQ
  have hQ0 : (0 : ℝ) < Q := Nat.cast_pos.mpr hQn
  have hs0 : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
  have hnext : Dnext ≠ 0 := by
    intro hz
    have hb : Q ≤ 0 := by simpa [hz] using hupper
    omega
  have hnext0 : (0 : ℝ) < Dnext := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnext)
  have hfloor := Submodule.bootstrap_sample_floor_lower_bound D p (by omega) hp4
  have hps : (p : ℝ) ≤ 4 * (D : ℝ) ^ 2 * (s : ℝ) := by
    have hb := (div_le_iff₀ (by positivity : 0 < 4 * (D : ℝ) ^ 2)).mp hfloor
    change (p : ℝ) ≤ (s : ℝ) * (4 * (D : ℝ) ^ 2) at hb
    nlinarith only [hb]
  have hbadR : (r : ℝ) * (D : ℝ) ^ 3 < p := by exact_mod_cast hbad
  have hupperR : (Q : ℝ) ≤ (r : ℝ) * (Dnext : ℝ) ^ 3 := by exact_mod_cast hupper
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have htR : (t : ℝ) ≤ r := by exact_mod_cast ht
  have halpha : alpha = 3 * (s : ℝ) / (25 * (Q : ℝ)) := by
    dsimp only [alpha]
    ring
  have hnumeric := nested_sampling_conditions hDR hlogD hnext0 hrR htR hQ0 hs0
    hcount hbadR hupperR hps htrade
  refine ⟨hD8, hp4, hs1, ?_, ?_⟩
  · dsimp only [alpha]
    positivity
  · simpa only [halpha] using hnumeric

end Real

end NestedSamplingNaturalParameters

section ViableSubspaceNestedCountSampling

/-!
## An actual nested-target sample from a dyadic count comparison

The natural quotient, failure estimate and final error are derived from
the count comparison and the calibrated suppression of the same chosen
family. The conclusion retains the actual Haar unitary, sample and image.
This supports ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`,
lines 1112–1128. The physical target comparisons and improving family
remain hypotheses of this abstract auxiliary.

**Local fix (strict dimension decrease):** The sample has dimension
`p / (2 * D^2)`, and its image has dimension at most `p/2`. See
`docs/paper-gaps/alvv16_low_density_sampling.tex` and the complex-sphere
correction in `docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

open scoped TensorProduct InnerProductSpace

namespace Submodule

variable {M F : Type*}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- At a bad-to-good dyadic count comparison, one actual half-size sample
and its improving image retain the lower original target. Both numerical
sampling premises are consequences of the displayed count and suppression
bounds. Auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. -/
theorem exists_isViable_nested_sample_of_count_comparison
    {D Dnext r p : ℕ} {Delta : ℝ}
    {Gplus Gminus Thi Tlo : Submodule ℂ (M ⊗[ℂ] F)}
    (hupper : IsCloseTo (1 / 200) Gplus Thi)
    (hlower : IsCloseTo (1 / 200) Tlo Gminus)
    (A : Fin (D ^ 2) → M →L[ℂ] M)
    (himprove : ∀ delta < 1, ∀ S : Submodule ℂ M,
      IsViable delta S Thi →
      IsViable (Delta / (1 - delta) ^ 2)
        (⨆ i, S.map (A i : M →ₗ[ℂ] M)) Tlo)
    (hDelta : 0 ≤ Delta) (hlogD : 100 ≤ Real.log (D : ℝ)) (hr : 1 ≤ r)
    (htarget : Module.finrank ℂ Thi ≤ r)
    (hcount : Real.log (Dnext : ℝ) ≤ (13 / 6) * Real.log (D : ℝ))
    (hbad : r * D ^ 3 < p)
    {W : Submodule ℂ M} (hW : IsViable (3 / 200) W Gplus)
    (hpW : p ≤ Module.finrank ℂ W)
    (hupperDim : Module.finrank ℂ W ≤ r * Dnext ^ 3)
    (htrade : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000) :
    let Q : ℕ := Module.finrank ℂ W
    let s : ℕ := p / (2 * D ^ 2)
    let alpha : ℝ := (1 - 1 / 25) * (s : ℝ) / (8 * (Q : ℝ))
    let Coord : Finset (Fin Q) := Finset.univ.map
      (Fin.castLEEmb ((Nat.div_le_self p (2 * D ^ 2)).trans hpW))
    ∃ U : Matrix.unitaryGroup (Fin Q) ℂ,
      let sample := randomSubspace (stdOrthonormalBasis ℂ W) Coord U
      let image : Submodule ℂ M := ⨆ i, sample.map (A i : M →ₗ[ℂ] M)
      1 ≤ s ∧ 0 < alpha ∧ sample ≤ W ∧ Module.finrank ℂ sample = s ∧
      IsViable (1 - alpha) sample Thi ∧ Module.finrank ℂ image ≤ p / 2 ∧
      Module.finrank ℂ image < p ∧
      IsViable (2 * (Delta / alpha ^ 2 + 1 / 200)) image Gminus ∧
      IsViable (3 / 200) image Gminus := by
  intro Q s alpha Coord
  obtain ⟨hD, hp4, _hs1, _halpha, hfailure, herror⟩ :=
    Real.nested_sampling_natural_conditions hlogD hr htarget hcount hbad hpW hupperDim
      htrade
  obtain ⟨U, hs1, halpha, hsample, hsampledim, hsampleviable, hhalf, hraw, hfinal⟩ :=
    exists_isViable_nested_randomSubspace_finrank_le_half hupper hlower A himprove
      (by omega) hDelta hp4 hW hpW hfailure herror
  refine ⟨U, hs1, halpha, hsample, hsampledim, hsampleviable, hhalf, ?_, hraw, hfinal⟩
  exact hhalf.trans_lt (Nat.div_lt_self (lt_of_le_of_lt (Nat.zero_le _) hbad) (by decide))

end Submodule

end ViableSubspaceNestedCountSampling

section ViableSubspaceDyadicBootstrap

/-!
## A strict dimension comparison for nested viable targets

Actual minimizing spaces and a finite first count comparison reduce the
low-density argument to the calibrated nested-target sample. The previous
minimum determines the sample size; the next optimal space is the space
in which the sample is drawn. Its actual improving image has dimension
strictly smaller than the previous minimum, giving a contradiction.

This is an auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. The nested improving families,
count comparisons and a finite count cap are explicit premises here.
Their derivation from a physical Hamiltonian is a separate theorem.

**Local fix (strict dimension decrease):** The actual sample size is
`p / (2 * D^2)`, with `p` the previous minimum, rather than the
dimension of the next optimal space. Its image has dimension below `p`.
See `docs/paper-gaps/alvv16_low_density_sampling.tex`.
-/

open scoped TensorProduct InnerProductSpace

namespace Submodule

variable {M F : Type*}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Nested actual improving families give a viable subspace at the initial
count. The proof selects actual natural minima and invokes the literal
calibrated Haar sample at the first bad-to-good pair. Auxiliary to ALVV,
arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines 1112–1128. -/
theorem exists_isViable_finrank_le_of_dyadic_families
    (T : ℕ → Submodule ℂ (M ⊗[ℂ] F)) (D : ℕ → ℕ) (r : ℕ)
    (hT : ∀ j, T j ≤ T (j + 1)) (hr : 1 ≤ r)
    (htarget : ∀ j, Module.finrank ℂ (T j) ≤ r)
    (hlogD : ∀ j, 100 ≤ Real.log (D j : ℝ))
    (hcount : ∀ j, Real.log (D (j + 1) : ℝ) ≤ (13 / 6) * Real.log (D j : ℝ))
    (hcap : ∃ j, Module.finrank ℂ M ≤ r * D j ^ 3)
    (hfamily : ∀ j,
      ∃ (A : Fin (D j ^ 2) → M →L[ℂ] M)
        (Tlo Thi : Submodule ℂ (M ⊗[ℂ] F)) (Delta : ℝ),
        IsCloseTo (1 / 200) (T (j + 1)) Thi ∧
        IsCloseTo (1 / 200) Tlo (T j) ∧ 0 ≤ Delta ∧
        (D j : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∀ delta < 1, ∀ S : Submodule ℂ M, IsViable delta S Thi →
          IsViable (Delta / (1 - delta) ^ 2)
            (⨆ i, S.map (A i : M →ₗ[ℂ] M)) Tlo) :
    ∃ W : Submodule ℂ M,
      Module.finrank ℂ W ≤ r * D 0 ^ 3 ∧ IsViable (3 / 200) W (T 0) := by
  classical
  obtain ⟨p, W, hW⟩ := exists_isViable_minimal_sequence (3 / 200) (by norm_num) T hT
  have hex : ∃ j, p j ≤ r * D j ^ 3 := by
    obtain ⟨j, hj⟩ := hcap
    exact ⟨j, (hW j).2.2.2.1.trans hj⟩
  obtain ⟨j, hgood, hfirst⟩ : ∃ j, p j ≤ r * D j ^ 3 ∧
      ∀ i < j, r * D i ^ 3 < p i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun _ hi ↦ lt_of_not_ge (Nat.find_min hex hi)⟩
  cases j with
  | zero =>
    refine ⟨W 0, ?_, (hW 0).2.1⟩
    simpa only [(hW 0).1] using hgood
  | succ j =>
    obtain ⟨A, Tlo, Thi, Delta, hupper, hlower, hDelta, htrade, himprove⟩ := hfamily j
    have hpW : p j ≤ Module.finrank ℂ (W (j + 1)) := by
      simpa only [(hW (j + 1)).1] using (hW j).2.2.2.2
    have hupperDim : Module.finrank ℂ (W (j + 1)) ≤ r * D (j + 1) ^ 3 := by
      simpa only [(hW (j + 1)).1] using hgood
    have hThi : Module.finrank ℂ Thi ≤ r :=
      (hupper.finrank_le (by norm_num)).trans (htarget (j + 1))
    obtain ⟨U, _hs1, _halpha, _hsample, _hdims, _hsv, _hhalf, hlt, _hraw, hfinal⟩ :=
      exists_isViable_nested_sample_of_count_comparison hupper hlower A himprove
        hDelta (hlogD j) hr hThi (hcount j) (hfirst j (Nat.lt_succ_self j))
        ((hW (j + 1)).2.1) hpW hupperDim htrade
    exact False.elim (not_lt_of_ge ((hW j).2.2.1 _ hfinal) hlt)

/-- For the actual natural ceiling counts, both the finite count cap and
the logarithmic comparisons follow from their definitions. Only the
nested improving families and target inclusions remain premises.
Auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. -/
theorem exists_isViable_finrank_le_of_dyadic_filter_families
    (C v : ℝ) (m r : ℕ) (hC : 100 ≤ C) (hv : 0 < v) (hm : 2 ≤ m)
    (hlogm : 100 ≤ Real.log (m : ℝ))
    (T : ℕ → Submodule ℂ (M ⊗[ℂ] F))
    (hT : ∀ j, T j ≤ T (j + 1)) (hr : 1 ≤ r)
    (htarget : ∀ j, Module.finrank ℂ (T j) ≤ r) :
    let w := fun j : ℕ ↦ v / (6 * (2 : ℝ) ^ j)
    let g := fun j ↦ min (w j) 1
    let u := fun j ↦ 1 + Real.log (m : ℝ) + Real.log (1 / g j)
    let ell := fun j ↦ ⌈C * u j ^ 2 / g j⌉₊
    let D := fun j ↦ (m * ell j ^ 2) ^ (22 * ell j)
    (∀ j, ∃ (A : Fin (D j ^ 2) → M →L[ℂ] M)
      (Tlo Thi : Submodule ℂ (M ⊗[ℂ] F)) (Delta : ℝ),
      IsCloseTo (1 / 200) (T (j + 1)) Thi ∧
      IsCloseTo (1 / 200) Tlo (T j) ∧ 0 ≤ Delta ∧
      (D j : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
      ∀ delta < 1, ∀ S : Submodule ℂ M, IsViable delta S Thi →
        IsViable (Delta / (1 - delta) ^ 2)
          (⨆ i, S.map (A i : M →ₗ[ℂ] M)) Tlo) →
    ∃ W : Submodule ℂ M,
      Module.finrank ℂ W ≤ r * D 0 ^ 3 ∧ IsViable (3 / 200) W (T 0) := by
  intro w g u ell D hfamily
  have hw (j : ℕ) : 0 < w j := by dsimp only [w]; positivity
  have hhalf (j : ℕ) : w (j + 1) = w j / 2 := by
    dsimp only [w]
    rw [pow_succ]
    ring
  have hg (j : ℕ) : 0 < g j := lt_min (hw j) zero_lt_one
  have hratio (j : ℕ) : g j ≤ 2 * g (j + 1) := by
    by_cases hh : w (j + 1) ≤ 1
    · rw [show g (j + 1) = w (j + 1) from min_eq_left hh]
      calc
        g j ≤ w j := min_le_left _ _
        _ = 2 * w (j + 1) := by rw [hhalf]; ring
    · rw [show g (j + 1) = 1 from min_eq_right (le_of_not_ge hh)]
      exact (min_le_right _ _).trans (by norm_num)
  have hcounts (j : ℕ) : 100 ≤ Real.log (D j : ℝ) ∧
      Real.log (D (j + 1) : ℝ) ≤ (13 / 6) * Real.log (D j : ℝ) :=
    Real.log_polynomial_filter_count_half_step C m (g j) (g (j + 1)) hC hlogm
      (hg j) (min_le_right _ _) (hg (j + 1)) (min_le_right _ _) (hratio j)
  have hcap : ∃ j, Module.finrank ℂ M ≤ r * D j ^ 3 := by
    obtain ⟨j, _hell, hD⟩ := Real.exists_dyadic_polynomial_filter_count_ge C v m
      (Module.finrank ℂ M) ((by norm_num : (1 : ℝ) ≤ 100).trans hC) hv hm
    refine ⟨j, hD.trans ?_⟩
    exact (Nat.le_self_pow (by decide : 3 ≠ 0) (D j)).trans
      (by simpa only [one_mul] using Nat.mul_le_mul_right (D j ^ 3) hr)
  exact exists_isViable_finrank_le_of_dyadic_families T D r hT hr htarget
    (fun j ↦ (hcounts j).1) (fun j ↦ (hcounts j).2) hcap hfamily

end Submodule

end ViableSubspaceDyadicBootstrap
