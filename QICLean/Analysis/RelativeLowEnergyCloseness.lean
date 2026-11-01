/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.WeylMonotonicity

/-!
# Closeness of actual spectral subspaces above their own ground energies

For two actual ordered Hermitian matrices, restricted perturbation bounds on
both closed low-energy spaces give ground-energy comparison and closeness in
both directions. The canonical ground energies and eigenbases are derived from
the matrices. No ground energy, eigenbasis, or spectral comparison is supplied.

**Local fix (window count):** The enlargement uses the actual finite window
count from ALVV, arXiv:1602.08828v2, proof of Lemma 4.5 (`lem:hard-trunc`),
`local_alg_arxiv_v2.tex`, lines 955–968, as corrected in
`docs/paper-gaps/alvv16_hard_truncation_windows.tex`. This is a generic
finite-dimensional consequence of actual restricted residual bounds, not a
construction of a physical hard-truncation residual or a uniform small-cutoff
claim. The original and truncated spaces use their own actual ground energies.
-/

open scoped BigOperators ComplexOrder InnerProductSpace MatrixOrder

/-- An explicit enlargement satisfies the finite spectral-window budget,
including a ground-energy displacement at most the residual scale. -/
private theorem relative_low_energy_window_budget (E E' η ξ δ : ℝ)
    (hξ : 0 ≤ ξ) (hδ : 0 < δ) (hE : E ≤ E' + ξ) :
    let N : ℕ := ⌈η / (2 * ξ)⌉₊
    let η' := η + ξ + 2 * ξ * Real.sqrt ((N : ℝ) / δ)
    E + η ≤ E' + η' ∧
      (N : ℝ) * (ξ + ξ) ^ 2 ≤ δ * ((E' + η') - (E + η) + ξ) ^ 2 := by
  intro N η'
  have hratio : 0 ≤ (N : ℝ) / δ := div_nonneg (Nat.cast_nonneg N) hδ.le
  have hw : 0 ≤ 2 * ξ * Real.sqrt ((N : ℝ) / δ) := by positivity
  have hsep : E + η ≤ E' + η' := by dsimp only [η']; linarith
  have hden : 2 * ξ * Real.sqrt ((N : ℝ) / δ) ≤
      (E' + η') - (E + η) + ξ := by dsimp only [η']; linarith
  have hsquare := pow_le_pow_left₀ hw hden 2
  have hid : δ * (2 * ξ * Real.sqrt ((N : ℝ) / δ)) ^ 2 =
      (N : ℝ) * (ξ + ξ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hratio]
    field_simp [hδ.ne']
    ring
  exact ⟨hsep, hid.symm.trans_le (mul_le_mul_of_nonneg_left hsquare hδ.le)⟩

namespace Matrix.IsHermitian

/-- Actual closed low-energy spectral spaces are close in both directions after
an explicit enlargement of the relative energy cutoff. The last canonically
ordered eigenvalues give the actual ground energies internally; all bases are
canonical bases of the given matrices. Repeated eigenvalues are allowed.

Source: ALVV, arXiv:1602.08828v2, `lem:hard-trunc`, lines 955–968; this is the
relative-ground-energy consequence with the corrected finite window count.
The actual physical residual estimates remain separate hypotheses. -/
theorem groundEnergy_compare_and_isCloseTo_spectralSpanLE_of_norm_domRestrict_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {H F : Matrix n n ℂ} (hH : H.IsHermitian) (hF : F.IsHermitian)
    (hFH : F ≤ H) (η ξ δ : ℝ) (hη : 0 < η) (hξ : 0 < ξ) (hδ : 0 < δ) :
    let jmin : Fin (Fintype.card n) :=
      ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide)⟩
    let bH := (isSymmetric_toEuclideanLin_iff.mpr hH).eigenvectorBasis
      finrank_euclideanSpace
    let bF := (isSymmetric_toEuclideanLin_iff.mpr hF).eigenvectorBasis
      finrank_euclideanSpace
    let E := hH.eigenvalues₀ jmin
    let E' := hF.eigenvalues₀ jmin
    let η' := η + ξ + 2 * ξ * Real.sqrt ((⌈η / (2 * ξ)⌉₊ : ℝ) / δ)
    ‖((toEuclideanCLM (n := n) (𝕜 := ℂ)) H -
        (toEuclideanCLM (n := n) (𝕜 := ℂ)) F).domRestrict
      (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η))‖ ≤ ξ →
    ‖((toEuclideanCLM (n := n) (𝕜 := ℂ)) H -
        (toEuclideanCLM (n := n) (𝕜 := ℂ)) F).domRestrict
      (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E + η))‖ ≤ ξ →
    E' ≤ E ∧ E ≤ E' + ξ ∧
      Submodule.IsCloseTo δ
        (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E' + η'))
        (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η)) ∧
      Submodule.IsCloseTo δ
        (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η'))
        (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E' + η)) := by
  intro jmin bH bF E E' η' hresH hresF
  classical
  let D : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
    (toEuclideanCLM (n := n) (𝕜 := ℂ)) H - (toEuclideanCLM (n := n) (𝕜 := ℂ)) F
  have hj (j : Fin (Fintype.card n)) : j ≤ jmin := by
    change j.val ≤ Fintype.card n - 1
    omega
  have hE (j : Fin (Fintype.card n)) : E ≤ hH.eigenvalues₀ j :=
    hH.eigenvalues₀_antitone (hj j)
  have hE' (j : Fin (Fintype.card n)) : E' ≤ hF.eigenvalues₀ j :=
    hF.eigenvalues₀_antitone (hj j)
  have hgroundLower : E' ≤ E := hF.eigenvalues₀_mono hH hFH jmin
  have hgroundUpper : E ≤ E' + ξ :=
    hH.eigenvalues₀_le_add_of_norm_domRestrict_low_le hF (E + η) ξ hresF jmin
      (by change E' ≤ E + η; linarith)
  have hdiagH (j : Fin (Fintype.card n)) :
      toEuclideanLin H (bH j) = (hH.eigenvalues₀ j : ℂ) • bH j :=
    (isSymmetric_toEuclideanLin_iff.mpr hH).apply_eigenvectorBasis
      finrank_euclideanSpace j
  have hdiagF (j : Fin (Fintype.card n)) :
      toEuclideanLin F (bF j) = (hF.eigenvalues₀ j : ℂ) • bF j :=
    (isSymmetric_toEuclideanLin_iff.mpr hF).apply_eigenvectorBasis
      finrank_euclideanSpace j
  have hpertH (v : EuclideanSpace ℂ n)
      (hv : v ∈ Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η)) :
      ‖toEuclideanLin H v - toEuclideanLin F v‖ ≤ ξ * ‖v‖ := by
    have h := (D.domRestrict
      (Submodule.spectralSpanLE bH hH.eigenvalues₀ (E + η))).le_opNorm ⟨v, hv⟩
    exact h.trans (mul_le_mul_of_nonneg_right hresH (norm_nonneg v))
  have hpertF (v : EuclideanSpace ℂ n)
      (hv : v ∈ Submodule.spectralSpanLE bF hF.eigenvalues₀ (E' + η)) :
      ‖toEuclideanLin F v - toEuclideanLin H v‖ ≤ ξ * ‖v‖ := by
    have hsubset : Submodule.spectralSpanLE bF hF.eigenvalues₀ (E' + η) ≤
        Submodule.spectralSpanLE bF hF.eigenvalues₀ (E + η) := by
      apply Submodule.span_mono
      rintro _ ⟨j, hj', rfl⟩
      exact ⟨j, le_trans (show hF.eigenvalues₀ j ≤ E' + η from hj')
        (by linarith : E' + η ≤ E + η), rfl⟩
    have h := (D.domRestrict
      (Submodule.spectralSpanLE bF hF.eigenvalues₀ (E + η))).le_opNorm
        ⟨v, hsubset hv⟩
    rw [norm_sub_rev]
    exact h.trans (mul_le_mul_of_nonneg_right hresF (norm_nonneg v))
  obtain ⟨hsep, hbudget⟩ := relative_low_energy_window_budget E E' η ξ δ hξ.le hδ hgroundUpper
  obtain ⟨hsep', hbudget'⟩ := relative_low_energy_window_budget E' E η ξ δ hξ.le hδ
    (hgroundLower.trans (le_add_of_nonneg_right hξ.le))
  have hcount : (E + η - E) / (2 * ξ) = η / (2 * ξ) := by ring
  have hcount' : (E' + η - E') / (2 * ξ) = η / (2 * ξ) := by ring
  refine ⟨hgroundLower, hgroundUpper, ?_, ?_⟩
  · exact Submodule.isCloseTo_spectralSpanLE_of_perturbation
      bH bF hH.eigenvalues₀ hF.eigenvalues₀ hdiagH hdiagF hpertH hξ
      (fun j _ ↦ hE j) (by linarith) hsep (by simpa only [hcount] using hbudget)
  · exact Submodule.isCloseTo_spectralSpanLE_of_perturbation
      bF bH hF.eigenvalues₀ hH.eigenvalues₀ hdiagF hdiagH hpertF hξ
      (fun j _ ↦ hE' j) (by linarith) hsep' (by simpa only [hcount'] using hbudget')

end Matrix.IsHermitian
