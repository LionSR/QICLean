/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Eigenvalue.MatrixSpectralDecomp
import QICLean.Spectral.Eigenvalue.GroundEnergyBounds
import QICLean.Spectral.Eigenvalue.HermitianExtremalEigenvalues
import QICLean.Spectral.LowEnergy.RelativeLowEnergyCloseness
import QICLean.Spectral.LowEnergy.WeightedLowRestriction
import QICLean.Analysis.Order.WeylMonotonicity
import QICLean.ManyBody.Dynamics.BoundedDegreeImaginaryTime
import QICLean.ManyBody.Hamiltonian.DisjointRegionalGround
import QICLean.ManyBody.Sites.Cut

/-!
# Hard truncation of a region of an interaction of bounded support and degree

Let `Φ` be an interaction whose terms are positive contractions `0 ≤ hᵢ ≤ 1`, each supported on
at most `k` sites, with every site in the supports of at most `g` terms. For a region `Λ`, the
terms supported in `Λ` form `H_in`, the terms supported outside `Λ` form `H_out`, and the `b`
terms crossing the cut at `Λ` form `Y`, so that `H = H_in + H_out + Y` is the Hamiltonian of `Φ`.
Let `e_in`, `e_out` be the minimum eigenvalues of `H_in`, `H_out`. Clipping `H_in` at
`e_in + t` gives the hard truncation `F = min(H_in, e_in + t) + H_out + Y`; both `H` and `F`
are centered at `e_in + e_out`.

For `η > 0` and `t ≥ η + 3 b + 1`, the restrictions of `H - F` to the spectral spaces of `H`
and of `F` below `E + η`, where `E` is the ground energy of the centered `H`, have norm at most
`ξ = 4 g k (b + 1) exp(-(t - η - 3 b - 1) / (2 g k))`. The ordered eigenvalues below that
window shift by at most `ξ`, the ground energy by at most `ξ`, and the low spectral spaces are
close in both directions after an enlargement of the window. The ground space may be
degenerate.

The proof uses a common unit vector attaining both regional minima (the regions `Λ` and its
complement are disjoint), the conjugation bound `‖e^{s(H_in - c)} Y e^{-s(H_in - c)}‖ ≤ 2 b`
for `s = 1 / (2 g k)`, and the weighted restriction estimate for the clipping error.

**Local fix (cutoff, constants and window count):** the cutoff is the sufficient
`t ≥ η + 3 b + 1` in place of the printed `t > η`, the decay rate is `1 / (2 g k)` with the
displayed prefactor in place of the printed constants, and the enlargement of the window
includes the ceiling window count and the ground shift. For an interval `Λ` of a
nearest-neighbour chain, `b ≤ 2` and the cutoff is `η + 7`. See
`docs/paper-gaps/alvv16_hard_truncation_windows.tex`.

**Scope restriction (contractions, count degree):** the terms are contractions `0 ≤ hᵢ ≤ 1`
and the degree `g` counts the terms whose support contains a site, where AKL14 assume
`h_X ≥ 0` with `∑_{X ∋ i} ‖h_X‖ ≤ g`. See `docs/paper-gaps/akl14_hadamard_bound_scope.tex`.

Moved from TNLean, `TNLean/Lattice/HardTruncation.lean` at commit `e41c3b63`, restated for an
interaction on a system of sites with nonempty basis types; the crossing terms are
`crossingTerms T Λ`, and the hypotheses `0 < k`, `0 < g` are combined into `0 < g k`.

## Main results

* `ManyBody.Interaction.exists_region_hard_truncation_spectral_comparison`

## References

* Arad, Kuwahara and Landau, arXiv:1406.3898, Definition `def:Ht`, `low70.tex`,
  lines 684–697, and Theorem `thm:lowspec`, lines 719–748.
* Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Definition 4.3, Proposition 4.4 and
  Lemma 4.5, `local_alg_arxiv_v2.tex`, lines 873–968.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace ManyBody.Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] [∀ v, Nonempty (X v)] {ι : Type*} [Fintype ι] {T : ι → Finset V}

private theorem residual_coefficient_le {κ b E η t : ℝ} (hκ : 0 < κ) (hb : 0 ≤ b)
    (hE : E ≤ b) :
    (Real.exp (-(1 / (2 * κ)) * (t - (η + 3 * b + 1)) - 1) / (1 / (2 * κ))) *
        ((2 * b) / ((η + 3 * b + 1) - (E + η) - 2 * b)) ≤
      4 * κ * (b + 1) * Real.exp (-(t - (η + 3 * b + 1)) / (2 * κ)) := by
  have hd : 1 ≤ (η + 3 * b + 1) - (E + η) - 2 * b := by linarith
  have hq : (2 * b) / ((η + 3 * b + 1) - (E + η) - 2 * b) ≤ 2 * (b + 1) := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith
  have hexp : -(1 / (2 * κ)) * (t - (η + 3 * b + 1)) - 1 =
      -(t - (η + 3 * b + 1)) / (2 * κ) + (-1) := by
    field_simp
    ring
  have h1 : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hX : 0 < Real.exp (-(t - (η + 3 * b + 1)) / (2 * κ)) := Real.exp_pos _
  calc
    _ ≤ (Real.exp (-(1 / (2 * κ)) * (t - (η + 3 * b + 1)) - 1) / (1 / (2 * κ))) *
        (2 * (b + 1)) := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 4 * κ * (b + 1) * Real.exp (-(t - (η + 3 * b + 1)) / (2 * κ)) *
        Real.exp (-1) := by
      rw [hexp, Real.exp_add]
      field_simp
      ring
    _ ≤ 4 * κ * (b + 1) * Real.exp (-(t - (η + 3 * b + 1)) / (2 * κ)) * 1 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := mul_one _

omit [Fintype V] in
/-- The terms crossing the cut at `Λ` are those supported neither in `Λ` nor outside it. -/
private theorem crossingTerms_eq_filter (Λ : Finset V) :
    crossingTerms T Λ = Finset.univ.filter fun i ↦ ¬T i ⊆ Λ ∧ ¬Disjoint (T i) Λ := by
  classical
  ext i
  simp only [crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.not_subset, Finset.not_disjoint_iff]
  exact ⟨fun ⟨⟨v, hv, hvΛ⟩, ⟨w, hw, hwΛ⟩⟩ ↦ ⟨⟨w, hw, hwΛ⟩, ⟨v, hv, hvΛ⟩⟩,
    fun ⟨⟨w, hw, hwΛ⟩, ⟨v, hv, hvΛ⟩⟩ ↦ ⟨⟨v, hv, hvΛ⟩, ⟨w, hw, hwΛ⟩⟩⟩

/-- The restricted errors of a regional hard truncation. AKL14, arXiv:1406.3898, `def:Ht`,
lines 684–697, and `thm:lowspec`, lines 719–748, as Proposition 4.4(1) of ALVV,
arXiv:1602.08828v2, lines 894–921, within the module's local fix. -/
private theorem exists_region_hard_truncation_residuals (Φ : Interaction X T) {k g : ℕ}
    (hgk : 0 < g * k) (hpos : ∀ i, 0 ≤ Φ.term i) (hle : ∀ i, Φ.term i ≤ 1)
    (hk : ∀ i, (T i).card ≤ k) (hg : ∀ v, (Finset.univ.filter fun i ↦ v ∈ T i).card ≤ g)
    (Λ : Finset V) :
    let Hin := ∑ i ∈ Finset.univ.filter (fun i ↦ T i ⊆ Λ), Φ.term i
    let Hout := ∑ i ∈ Finset.univ.filter (fun i ↦ ¬T i ⊆ Λ ∧ Disjoint (T i) Λ), Φ.term i
    let Y := ∑ i ∈ crossingTerms T Λ, Φ.term i
    let b : ℝ := (crossingTerms T Λ).card
    let κ : ℝ := ((g * k : ℕ) : ℝ)
    ∃ (ein eout : ℝ) (x z : Config X → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ Hin *ᵥ x = (ein : ℂ) • x ∧ Hout *ᵥ x = (eout : ℂ) • x ∧
      (Hin - (ein : ℂ) • 1).PosSemidef ∧ (Hout - (eout : ℂ) • 1).PosSemidef ∧
      0 ≤ ein ∧ 0 ≤ eout ∧
      let H := Φ.hamiltonian - ((ein + eout : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ b ∧
      ∀ η t : ℝ, 0 < η → η + 3 * b + 1 ≤ t →
        let F := energyTruncation Hin (ein + t) + Hout + Y - ((ein + eout : ℝ) : ℂ) • 1
        ∃ (hH : H.IsHermitian) (hF : F.IsHermitian) (E' : ℝ) (z' : Config X → ℂ),
          F ≤ H ∧ star z' ⬝ᵥ z' = 1 ∧ F *ᵥ z' = (E' : ℂ) • z' ∧
          (F - (E' : ℂ) • (1 : Matrix (Config X) (Config X) ℂ)).PosSemidef ∧
          0 ≤ E' ∧ E' ≤ b ∧
          let ξ : ℝ := (4 : ℝ) * κ * (b + (1 : ℝ)) *
            Real.exp (-(t - (η + (3 : ℝ) * b + (1 : ℝ))) / ((2 : ℝ) * κ))
          ‖((toEuclideanCLM (n := Config X) (𝕜 := ℂ)) H -
              (toEuclideanCLM (n := Config X) (𝕜 := ℂ)) F).domRestrict
            (Submodule.spectralSpanLE
              ((isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
                finrank_euclideanSpace) hH.eigenvalues₀ (E + η))‖ ≤ ξ ∧
          ‖((toEuclideanCLM (n := Config X) (𝕜 := ℂ)) H -
              (toEuclideanCLM (n := Config X) (𝕜 := ℂ)) F).domRestrict
            (Submodule.spectralSpanLE
              ((isSymmetric_toEuclideanLin_iff.mpr hF).eigenvectorBasis
                finrank_euclideanSpace) hF.eigenvalues₀ (E + η))‖ ≤ ξ := by
  intro Hin Hout Y b κ
  classical
  let Iin := Finset.univ.filter fun i ↦ T i ⊆ Λ
  let Iout := Finset.univ.filter fun i ↦ ¬T i ⊆ Λ ∧ Disjoint (T i) Λ
  have sum_supported_of_subset (s : Finset ι) (R : Finset V) (hR : ∀ i ∈ s, T i ⊆ R) :
      ∑ i ∈ s, Φ.term i ∈ supportedOperators X R :=
    sum_mem fun i hi ↦ supportedOperators_mono (hR i hi) (Φ.mem i)
  let A : Fin 2 → Matrix (Config X) (Config X) ℂ := ![Hin, Hout]
  let R : Fin 2 → Finset V := ![Λ, Λᶜ]
  let c : Fin 2 → ℕ := ![Iin.card, Iout.card]
  have hR : Pairwise fun i j ↦ Disjoint (R i) (R j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [R, disjoint_compl_right, disjoint_compl_left]
  have hsA (j : Fin 2) : A j ∈ supportedOperators X (R j) := by
    fin_cases j
    · exact sum_supported_of_subset Iin Λ fun i hi ↦ (Finset.mem_filter.mp hi).2
    · refine sum_supported_of_subset Iout Λᶜ fun i hi ↦ ?_
      exact Finset.subset_compl_iff_disjoint_right.mpr (Finset.mem_filter.mp hi).2.2
  have hA (j : Fin 2) : (A j).PosSemidef ∧ A j ≤ (c j : ℝ) • 1 := by
    fin_cases j
    · exact sum_posSemidef_and_le_card_of_positive_unit_terms Iin Φ.term
        (fun i _ ↦ hpos i) (fun i _ ↦ hle i)
    · exact sum_posSemidef_and_le_card_of_positive_unit_terms Iout Φ.term
        (fun i _ ↦ hpos i) (fun i _ ↦ hle i)
  obtain ⟨hY, hYC⟩ := sum_posSemidef_and_le_card_of_positive_unit_terms (crossingTerms T Λ)
    Φ.term (fun i _ ↦ hpos i) (fun i _ ↦ hle i)
  have hsum : Φ.hamiltonian = (∑ j, A j) + Y := by
    rw [Fin.sum_univ_two]
    change ∑ i, Φ.term i = Hin + Hout + Y
    simp only [Hin, Hout, Y, crossingTerms_eq_filter]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ T i ⊆ Λ),
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun i ↦ ¬T i ⊆ Λ)
        (fun i ↦ Disjoint (T i) Λ), Finset.filter_filter, Finset.filter_filter, add_assoc]
  obtain ⟨e, x, hx, hxe, he, hclip⟩ :=
    exists_disjoint_regional_clipping_structure R A c hR hsA
      (fun j ↦ (hA j).1) (fun j ↦ (hA j).2) Y (crossingTerms T Λ).card hY hYC
  let B (t : ℝ) (U : Finset (Fin 2)) :=
    (∑ j, ((if j ∈ U then cfc (fun r : ℝ ↦ min r (e j + t)) (A j) else A j) -
      (e j : ℂ) • 1)) + Y
  let H := Φ.hamiltonian - ((e 0 + e 1 : ℝ) : ℂ) • 1
  have hcenter (t : ℝ) : B t ∅ = H := by
    simp only [B, H, Finset.notMem_empty, ite_false, Finset.sum_sub_distrib, hsum,
      Fin.sum_univ_two]
    push_cast
    rw [add_smul]
    abel
  obtain ⟨hX0, -, -, -, -, -, E, z, hz, hHz, hE, hE0, hEJ⟩ := hclip 0 le_rfl ∅
  have hHpos : H.PosSemidef := by
    rw [← hcenter 0]
    exact hX0.add hY
  have hHz' : H *ᵥ z = (E : ℂ) • z := by
    rw [← hcenter 0]
    exact hHz
  have hE' : (H - (E : ℂ) • 1).PosSemidef := by
    rw [← hcenter 0]
    exact hE
  refine ⟨e 0, e 1, x, z, E, hx, hxe 0, hxe 1, he 0, he 1,
    (hA 0).1.nonneg_of_normalized_eigenvector (e 0) x (hxe 0) hx,
    (hA 1).1.nonneg_of_normalized_eigenvector (e 1) x (hxe 1) hx,
    hz, hHz', hE', hE0, hEJ, ?_⟩
  intro η t hη ht F
  have hb0 : 0 ≤ b := Nat.cast_nonneg _
  have ht0 : 0 ≤ t := by linarith
  have hmiddle : B t {0} = F := by
    simp only [B, Fin.sum_univ_two, Finset.mem_singleton, Fin.isValue, ite_true,
      Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
    dsimp only [F, energyTruncation]
    push_cast
    rw [add_smul]
    simp only [A, Matrix.cons_val_zero, Matrix.cons_val_one]
    abel
  have hdiff : H - F = Hin - energyTruncation Hin (e 0 + t) := by
    dsimp only [H, F]
    rw [hsum, Fin.sum_univ_two]
    change Hin + Hout + Y - _ - (energyTruncation Hin (e 0 + t) + Hout + Y - _) = _
    abel
  have hFH : F ≤ H := Matrix.le_iff.mpr (by
    rw [hdiff]
    exact Matrix.le_iff.mp ((hA 0).1.isHermitian.energyTruncation_le (e 0 + t)))
  obtain ⟨hX1, -, -, -, -, -, E', z', hz', hFz₀, hE'₀, hE'0, hE'J⟩ := hclip t ht0 {0}
  have hFz' : F *ᵥ z' = (E' : ℂ) • z' := by
    rw [← hmiddle]
    exact hFz₀
  have hE'' : (F - (E' : ℂ) • 1).PosSemidef := by
    rw [← hmiddle]
    exact hE'₀
  have hFpos : F.PosSemidef := by
    rw [← hmiddle]
    exact hX1.add hY
  let hH := hHpos.isHermitian
  let hF := hFpos.isHermitian
  refine ⟨hH, hF, E', z', hFH, hz', hFz', hE'', hE'0, hE'J, ?_⟩
  have hκ : 0 < κ := Nat.cast_pos.mpr hgk
  let s : ℝ := 1 / (2 * κ)
  have hs0 : 0 < s := by positivity
  have hsκ : 2 * κ * s ≤ 1 := by
    rw [mul_one_div_cancel (by positivity)]
  let u : ℝ := η + 3 * b + 1
  have hconj : ‖NormedSpace.exp (s • (A 0 - (e 0 + u) • (1 : Matrix (Config X)
      (Config X) ℂ))) * Y * NormedSpace.exp (-(s • (A 0 - (e 0 + u) •
        (1 : Matrix (Config X) (Config X) ℂ))))‖ ≤ 2 * b := by
    have hgin (v : V) : (Iin.filter fun i ↦ v ∈ T i).card ≤ g :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans (hg v)
    have hc := norm_exp_conjugation_shift_sum_le Φ Iin (crossingTerms T Λ) hpos hle hk hgin
      ((e 0 + u : ℝ) : ℂ) hs0.le hsκ
    simp only [Complex.coe_smul] at hc
    exact hc
  have hgap : 2 * b < u - (E + η) := by simp only [u]; linarith
  have hres (M : Matrix (Config X) (Config X) ℂ) (hM : M.IsHermitian)
      (U : Finset (Fin 2)) (hBM : B t U = M) :
      ‖((toEuclideanCLM (n := Config X) (𝕜 := ℂ)) H -
          (toEuclideanCLM (n := Config X) (𝕜 := ℂ)) F).domRestrict
        (Submodule.spectralSpanLE hM.eigenvectorBasis hM.eigenvalues (E + η))‖ ≤
          4 * κ * (b + 1) * Real.exp (-(t - (η + 3 * b + 1)) / (2 * κ)) := by
    have hEigen (v : Config X) : (toEuclideanCLM (n := Config X) (𝕜 := ℂ)) (B t U)
        (hM.eigenvectorBasis v) = (hM.eigenvalues v : ℂ) • hM.eigenvectorBasis v := by
      rw [hBM]
      exact hM.toEuclideanCLM_eigenvectorBasis v
    have hsingle := Matrix.norm_partially_clipped_truncation_low_le A
      (fun j ↦ (hA j).1.isHermitian)
      (fun i j hij ↦ by
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact commute_of_mem_supportedOperators_of_disjoint (hsA 0) (hsA 1) (hR hij)
        · exact commute_of_mem_supportedOperators_of_disjoint (hsA 1) (hsA 0) (hR hij)
        · exact absurd rfl hij)
      e (fun j ↦ Matrix.le_iff.mpr (he j)) U 0 Y u (E + η) s t (2 * b) hs0
      (by simp only [u]; linarith) ht hM.eigenvectorBasis hM.eigenvalues hEigen hconj hgap
    rw [← map_sub, hdiff]
    exact hsingle.trans (residual_coefficient_le hκ hb0 hEJ)
  constructor
  · rw [← hH.spectralSpanLE_eigenvectorBasis_eq (E + η)]
    exact hres H hH ∅ (hcenter t)
  · rw [← hF.spectralSpanLE_eigenvectorBasis_eq (E + η)]
    exact hres F hF {0} hmiddle

/-- **Hard truncation of a region.** Let the terms of `Φ` be positive contractions, each
supported on at most `k` sites, with every site in the supports of at most `g` terms. For a
region `Λ`, let `H_in`, `H_out` and `Y` be the sums of the terms supported in `Λ`, supported
outside `Λ`, and crossing the cut at `Λ`, and `b` the number of crossing terms. There are the
minimum eigenvalues `e_in, e_out ≥ 0` of `H_in` and `H_out` and one unit vector attaining
both. Put `H = Φ.hamiltonian - (e_in + e_out)`, with ground energy `E ∈ [0, b]`. For `η > 0`
and `t ≥ η + 3 b + 1`, the hard truncation `F = min(H_in, e_in + t) + H_out + Y - (e_in + e_out)`
satisfies `F ≤ H`, has ground energy `E' ∈ [0, b]`, and, with
`ξ = 4 g k (b + 1) exp(-(t - η - 3 b - 1) / (2 g k))`:
the restrictions of `H - F` to the spectral spaces of `H` and of `F` below `E + η` have norm at
most `ξ`; every eigenvalue `λᵢ(F) ≤ E + η`, numbered in decreasing order, satisfies
`λᵢ(F) ≤ λᵢ(H) ≤ λᵢ(F) + ξ`; `E' ≤ E ≤ E' + ξ`; and for every `δ > 0`, with
`η' = η + ξ + 2 ξ √(⌈η / (2ξ)⌉ / δ)`, the spectral space of `F` below `E' + η'` is `δ`-close to
that of `H` below `E + η`, and the spectral space of `H` below `E + η'` is `δ`-close to that of
`F` below `E' + η`.
AKL14, arXiv:1406.3898, `def:Ht`, lines 684–697, and `thm:lowspec`, lines 719–748; ALVV,
arXiv:1602.08828v2, Definition 4.3, Proposition 4.4 and Lemma 4.5, lines 873–968; within the
module's local fix. -/
theorem exists_region_hard_truncation_spectral_comparison (Φ : Interaction X T) {k g : ℕ}
    (hgk : 0 < g * k) (hpos : ∀ i, 0 ≤ Φ.term i) (hle : ∀ i, Φ.term i ≤ 1)
    (hk : ∀ i, (T i).card ≤ k) (hg : ∀ v, (Finset.univ.filter fun i ↦ v ∈ T i).card ≤ g)
    (Λ : Finset V) :
    let Hin := ∑ i ∈ Finset.univ.filter (fun i ↦ T i ⊆ Λ), Φ.term i
    let Hout := ∑ i ∈ Finset.univ.filter (fun i ↦ ¬T i ⊆ Λ ∧ Disjoint (T i) Λ), Φ.term i
    let Y := ∑ i ∈ crossingTerms T Λ, Φ.term i
    let b : ℝ := (crossingTerms T Λ).card
    let κ : ℝ := ((g * k : ℕ) : ℝ)
    ∃ (ein eout : ℝ) (x z : Config X → ℂ) (E : ℝ),
      star x ⬝ᵥ x = 1 ∧ Hin *ᵥ x = (ein : ℂ) • x ∧ Hout *ᵥ x = (eout : ℂ) • x ∧
      (Hin - (ein : ℂ) • 1).PosSemidef ∧ (Hout - (eout : ℂ) • 1).PosSemidef ∧
      0 ≤ ein ∧ 0 ≤ eout ∧
      let H := Φ.hamiltonian - ((ein + eout : ℝ) : ℂ) • 1
      star z ⬝ᵥ z = 1 ∧ H *ᵥ z = (E : ℂ) • z ∧
      (H - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ b ∧
      ∀ η t : ℝ, 0 < η → η + 3 * b + 1 ≤ t →
        let F := energyTruncation Hin (ein + t) + Hout + Y - ((ein + eout : ℝ) : ℂ) • 1
        ∃ (hH : H.IsHermitian) (hF : F.IsHermitian) (E' : ℝ) (z' : Config X → ℂ),
          F ≤ H ∧ star z' ⬝ᵥ z' = 1 ∧ F *ᵥ z' = (E' : ℂ) • z' ∧
          (F - (E' : ℂ) • (1 : Matrix (Config X) (Config X) ℂ)).PosSemidef ∧
          0 ≤ E' ∧ E' ≤ b ∧
          let ξ : ℝ := (4 : ℝ) * κ * (b + (1 : ℝ)) *
            Real.exp (-(t - (η + (3 : ℝ) * b + (1 : ℝ))) / ((2 : ℝ) * κ))
          let bH := (isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
            finrank_euclideanSpace
          let bF := (isSymmetric_toEuclideanLin_iff.mpr hF).eigenvectorBasis
            finrank_euclideanSpace
          ‖((toEuclideanCLM (n := Config X) (𝕜 := ℂ)) H -
              (toEuclideanCLM (n := Config X) (𝕜 := ℂ)) F).domRestrict
            (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η))‖ ≤ ξ ∧
          ‖((toEuclideanCLM (n := Config X) (𝕜 := ℂ)) H -
              (toEuclideanCLM (n := Config X) (𝕜 := ℂ)) F).domRestrict
            (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E + η))‖ ≤ ξ ∧
          (∀ i : Fin (Fintype.card (Config X)), hF.eigenvalues₀ i ≤ E + η →
            hF.eigenvalues₀ i ≤ hH.eigenvalues₀ i ∧
              hH.eigenvalues₀ i ≤ hF.eigenvalues₀ i + ξ) ∧
          E' ≤ E ∧ E ≤ E' + ξ ∧
          ∀ δ : ℝ, 0 < δ →
            let η' : ℝ := η + ξ + 2 * ξ * Real.sqrt ((⌈η / (2 * ξ)⌉₊ : ℝ) / δ)
            Submodule.IsCloseTo δ
              (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E' + η'))
              (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η)) ∧
            Submodule.IsCloseTo δ
              (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η'))
              (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E' + η)) := by
  intro Hin Hout Y b κ
  obtain ⟨ein, eout, x, z, E, hx, hxin, hxout, hein, heout, hein0, heout0,
      hz, hHz, hElow, hE0, hEb, hclip⟩ :=
    exists_region_hard_truncation_residuals Φ hgk hpos hle hk hg Λ
  refine ⟨ein, eout, x, z, E, hx, hxin, hxout, hein, heout, hein0, heout0,
    hz, hHz, hElow, hE0, hEb, ?_⟩
  intro η t hη ht F
  obtain ⟨hH, hF, E', z', hFH, hz', hFz', hE'low, hE'0, hE'b, hresH, hresF⟩ :=
    hclip η t hη ht
  set ξ : ℝ := (4 : ℝ) * κ * (b + (1 : ℝ)) *
    Real.exp (-(t - (η + (3 : ℝ) * b + (1 : ℝ))) / ((2 : ℝ) * κ))
  have hminH : minEigenvalue hH = E := by
    simpa using hH.minEigenvalue_eq_add_of_centered_ground 0 E z hz
      (by simpa using hHz) (by simpa using hElow)
  have hminF : minEigenvalue hF = E' := by
    simpa using hF.minEigenvalue_eq_add_of_centered_ground 0 E' z' hz'
      (by simpa using hFz') (by simpa using hE'low)
  have hlastH := hH.eigenvalues₀_last_eq_minEigenvalue.trans hminH
  have hlastF := hF.eigenvalues₀_last_eq_minEigenvalue.trans hminF
  refine ⟨hH, hF, E', z', hFH, hz', hFz', hE'low, hE'0, hE'b, hresH, hresF,
    fun i hi ↦ ⟨hF.eigenvalues₀_mono hH hFH i,
      hH.eigenvalues₀_le_add_of_norm_domRestrict_low_le hF (E + η) ξ hresF i hi⟩, ?_⟩
  have hξ : 0 < ξ := by
    have hκ : 0 < κ := Nat.cast_pos.mpr hgk
    have hb : 0 ≤ b := Nat.cast_nonneg _
    positivity
  have hresult (δ : ℝ) (hδ : 0 < δ) := by
    have h := hH.groundEnergy_compare_and_isCloseTo_spectralSpanLE_of_norm_domRestrict_le
      hF hFH η ξ δ hη hξ hδ
    dsimp only at h
    rw [hlastH, hlastF] at h
    exact h hresH hresF
  obtain ⟨hgroundLower, hgroundUpper, -, -⟩ := hresult 1 zero_lt_one
  exact ⟨hgroundLower, hgroundUpper, fun δ hδ ↦ ⟨(hresult δ hδ).2.2.1, (hresult δ hδ).2.2.2⟩⟩

end ManyBody.Interaction
