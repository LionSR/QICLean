/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralFilter.MatrixFilter
import QICLean.Analysis.GlobalGap
import QICLean.Analysis.RootChannel

/-!
# Positive replacement of a gapped Hamiltonian

Let `H = ∑ᵢ hᵢ` be a Hermitian matrix with a unit eigenvector `Ω`, `H Ω = E₀ Ω`, and the
full-system gap `H - E₀ I ≥ Δ (I - |Ω⟩⟨Ω|)` with `Δ > 0`. Filter each term with the
spectral filter of width `δ ≤ Δ` and remove its ground expectation:
`Mᵢ = ∫ f(t) e^{itH} hᵢ e^{-itH} dt - ⟨Ω, hᵢ Ω⟩ I`. Then `Mᵢ` is Hermitian, `Mᵢ Ω = 0`,
`∑ᵢ Mᵢ = H - E₀ I` and `‖Mᵢ‖ ≤ ‖hᵢ‖ (‖f‖₁ + 1)`. With
`c_* = max {1, J (‖f‖₁ + 1)}` and `kᵢ = |Mᵢ| / c_*`, one obtains positive contractions
annihilating `Ω` whose sum dominates `c_*⁻¹ (H - E₀ I) ≥ (Δ / c_*) (I - |Ω⟩⟨Ω|)`.

This is the spectral part of Proposition 4.3; the graph-locality estimates of that
proposition depend on the lattice and belong to the consumer library.

## Main definitions

* `SpectralFilter.filterL1`: the integral `‖f‖₁` of the filter kernel.
* `SpectralFilter.centeredFilter`: the centered filtered term `Mᵢ`.
* `SpectralFilter.positiveConstraint`: `kᵢ = c⁻¹ |Mᵢ|`.

## Main results

* `SpectralFilter.filterIntegral_mulVec_of_posSemidef_gap`: filtering below the gap maps
  `Ω` to `⟨Ω, A Ω⟩ Ω`.
* `SpectralFilter.centeredFilter_mulVec_eq_zero`, `SpectralFilter.sum_centeredFilter`,
  `SpectralFilter.norm_centeredFilter_le`, `SpectralFilter.isHermitian_centeredFilter`.
* `SpectralFilter.positiveConstraint_nonneg`, `SpectralFilter.positiveConstraint_le_one`,
  `SpectralFilter.positiveConstraint_mulVec_eq_zero`,
  `SpectralFilter.smul_le_positiveConstraint`.
* `SpectralFilter.positive_replacement`: the assembled spectral statement of
  Proposition 4.3, `eq:quasilocal-positive`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 4.3 (`prop:positive`), section file `03-quasilocal.tex`, lines 220–284.
  The proofs here are written from the paper; the construction follows Kitaev,
  *Anyons in an exactly solved model and beyond*, Appendix D.1.2, Proposition D.1, as
  cited there. Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open MeasureTheory Complex
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder InnerProductSpace

namespace SpectralFilter

variable {n : Type*} [Fintype n] [DecidableEq n]

open Matrix

/-- The `L¹` norm `‖f‖₁ = ∫ |f(t)| dt` of the filter kernel (`03-quasilocal.tex`,
line 262). -/
noncomputable def filterL1 (p : ℕ) (δ : ℝ) : ℝ :=
  ∫ t, |spectralKernel p δ t|

theorem filterL1_nonneg (p : ℕ) (δ : ℝ) : 0 ≤ filterL1 p δ :=
  integral_nonneg fun _ => abs_nonneg _

omit [DecidableEq n] in
/-- A unit vector satisfies `Ω⋆ Ω = 1`. -/
theorem star_dotProduct_self_of_norm_eq_one {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1) :
    star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp Ω = 1 := by
  have h : ⟪Ω, Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]; simp
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  exact h

/-- `|⟨Ω, A Ω⟩| ≤ ‖A‖` for a unit vector `Ω`. -/
theorem norm_star_dotProduct_mulVec_le {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (A : Matrix n n ℂ) :
    ‖star (WithLp.ofLp Ω) ⬝ᵥ (A *ᵥ WithLp.ofLp Ω)‖ ≤ ‖A‖ := by
  have h : star (WithLp.ofLp Ω) ⬝ᵥ (A *ᵥ WithLp.ofLp Ω) =
      ⟪Ω, (EuclideanSpace.equiv n ℂ).symm (A *ᵥ WithLp.ofLp Ω)⟫_ℂ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; rfl
  rw [h]
  calc _ ≤ ‖Ω‖ * ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ WithLp.ofLp Ω)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖Ω‖ * (‖A‖ * ‖Ω‖) := by gcongr; exact A.l2_opNorm_mulVec Ω
    _ = ‖A‖ := by rw [hΩ]; ring

/-- `‖c • 1‖ ≤ ‖c‖` for the operator norm. -/
theorem norm_smul_one_le (c : ℂ) : ‖c • (1 : Matrix n n ℂ)‖ ≤ ‖c‖ := by
  rw [norm_smul]
  have h1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial (Matrix n n ℂ) with h | h
    · simp [Subsingleton.elim (1 : Matrix n n ℂ) 0]
    · rw [CStarRing.norm_one]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

/-! ### Filtering below a global gap -/

/-- **Filtering below the gap** (`03-quasilocal.tex`, lines 252–257): under the global gap
`H - E₀ I ≥ Δ (I - |Ω⟩⟨Ω|)` with `H Ω = E₀ Ω`, `‖Ω‖ = 1` and `0 < δ ≤ Δ`, the filtered
operator maps `Ω` to `⟨Ω, A Ω⟩ Ω`: excited components carry the multiplier
`χ(E - E₀) = 0`, and the ground component the multiplier `χ(0) = 1`. -/
theorem filterIntegral_mulVec_of_posSemidef_gap {p : ℕ} (hp : 1 ≤ p) {δ Δ E₀ : ℝ}
    (hδ : 0 < δ) (hδΔ : δ ≤ Δ) {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : H *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω)
    (hgap : (H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (A : Matrix n n ℂ) :
    filterIntegral p δ H A *ᵥ WithLp.ofLp Ω =
      (star (WithLp.ofLp Ω) ⬝ᵥ (A *ᵥ WithLp.ofLp Ω)) • WithLp.ofLp Ω := by
  set ω := WithLp.ofLp Ω with hω
  set c := star ω ⬝ᵥ (A *ᵥ ω) with hc
  set b := hH.eigenvectorBasis
  have hωω : star ω ⬝ᵥ ω = 1 := star_dotProduct_self_of_norm_eq_one hΩ
  have hΔ : 0 < Δ := hδ.trans_le hδΔ
  -- It suffices to test against every eigenbasis vector.
  suffices hk : ∀ k, star (WithLp.ofLp (b k)) ⬝ᵥ
      (filterIntegral p δ H A *ᵥ ω - c • ω) = 0 by
    have hv : (EuclideanSpace.equiv n ℂ).symm (filterIntegral p δ H A *ᵥ ω - c • ω) = 0 := by
      rw [← b.sum_repr' ((EuclideanSpace.equiv n ℂ).symm _)]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      change (star (WithLp.ofLp (b k)) ⬝ᵥ (filterIntegral p δ H A *ᵥ ω - c • ω)) • b k = 0
      rw [hk k, zero_smul]
    have := congrArg WithLp.ofLp hv
    simpa [sub_eq_zero] using this
  intro k
  set u := WithLp.ofLp (b k) with hu
  set lam := hH.eigenvalues k
  have hHu : H *ᵥ u = (lam : ℂ) • u := mulVec_eigenvectorBasis_complex hH k
  have hbk : ‖b k‖ = 1 := b.orthonormal.1 k
  -- The quadratic-form gap at the eigenvector `b k`.
  have hgk := hgap.gap_le (b k)
  have hHlin : ⟪b k, toEuclideanLin H (b k)⟫_ℂ = lam := by
    have : toEuclideanLin H (b k) = (lam : ℂ) • b k := by
      change WithLp.toLp 2 (H *ᵥ u) = _
      rw [hHu]; rfl
    rw [this, inner_smul_right, inner_self_eq_norm_sq_to_K, hbk]; simp
  rw [hHlin, hbk] at hgk
  simp only [Complex.ofReal_re, one_pow, mul_one] at hgk
  -- `⟨Ω, b k⟩` and `u⋆ Ω` are conjugate.
  have hinner : ⟪Ω, b k⟫_ℂ = star (star u ⬝ᵥ ω) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.star_dotProduct, star_star,
      dotProduct_comm]
  rw [dotProduct_sub, dotProduct_smul,
    dotProduct_filterIntegral_mulVec hp hδ hH A hHu hHΩ, smul_eq_mul]
  by_cases hlam : lam = E₀
  · -- Ground eigenvector: `b k = ⟨Ω, b k⟩ Ω`.
    rw [hlam, sub_self, spectralCutoff_zero p hδ, Complex.ofReal_one, one_mul]
    set a := ⟪Ω, b k⟫_ℂ with ha
    have ha1 : 1 ≤ ‖a‖ ^ 2 := by
      have : Δ * (1 - ‖a‖ ^ 2) ≤ 0 := by linarith
      by_contra hlt
      push Not at hlt
      have : 0 < Δ * (1 - ‖a‖ ^ 2) := mul_pos hΔ (by linarith)
      linarith
    have hsq : ‖b k - a • Ω‖ ^ 2 = 1 - ‖a‖ ^ 2 := by
      rw [@norm_sub_sq ℂ, hbk, inner_smul_right, norm_smul, hΩ, mul_one]
      have : ⟪b k, Ω⟫_ℂ = star a := (inner_conj_symm _ _).symm
      rw [this, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [RCLike.re_to_complex, Complex.ofReal_re]
      ring
    have hzero : b k = a • Ω := by
      have : ‖b k - a • Ω‖ ^ 2 ≤ 0 := by rw [hsq]; linarith
      have h0 : ‖b k - a • Ω‖ = 0 := by
        nlinarith [norm_nonneg (b k - a • Ω)]
      exact sub_eq_zero.mp (norm_eq_zero.mp h0)
    have hu' : u = a • ω := by rw [hu, hzero]; rfl
    rw [hu', star_smul, smul_dotProduct, smul_dotProduct, hωω, ← hc]
    simp only [smul_eq_mul, mul_one]
    ring
  · -- Excited eigenvector: orthogonal to `Ω` and at energy at least `E₀ + Δ`.
    have horth : star u ⬝ᵥ ω = 0 := by
      have h1 : star (H *ᵥ u) ⬝ᵥ ω = star u ⬝ᵥ (H *ᵥ ω) := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH.eq]
      rw [hHu, hHΩ, star_smul, smul_dotProduct, dotProduct_smul] at h1
      have hlc : star (lam : ℂ) = lam := Complex.conj_ofReal lam
      rw [hlc, smul_eq_mul, smul_eq_mul] at h1
      have : ((lam : ℂ) - E₀) * (star u ⬝ᵥ ω) = 0 := by rw [sub_mul, h1, sub_self]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by exact_mod_cast sub_eq_zero.mp h) hlam
      · exact h
    have hgap' : Δ ≤ lam - E₀ := by
      rw [hinner, horth, star_zero, norm_zero] at hgk
      linarith
    have hcut : spectralCutoff p δ (lam - E₀) = 0 :=
      spectralCutoff_eq_zero_of_le_abs p (by
        rw [abs_of_nonneg (by linarith)]; linarith)
    rw [hcut, horth]; simp

/-! ### The centered filtered terms -/

/-- **The centered filtered term** `M = ∫ f(t) e^{itH} h e^{-itH} dt - ⟨Ω, h Ω⟩ I`
(`03-quasilocal.tex`, `eq:quasilocal-centered-filter`, lines 247–250). -/
noncomputable def centeredFilter (p : ℕ) (δ : ℝ) (H : Matrix n n ℂ) (Ω : EuclideanSpace ℂ n)
    (h : Matrix n n ℂ) : Matrix n n ℂ :=
  filterIntegral p δ H h - (star (WithLp.ofLp Ω) ⬝ᵥ (h *ᵥ WithLp.ofLp Ω)) • 1

/-- `M` is Hermitian (`03-quasilocal.tex`, line 252). -/
theorem isHermitian_centeredFilter (p : ℕ) (δ : ℝ) {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (Ω : EuclideanSpace ℂ n) {h : Matrix n n ℂ} (hh : h.IsHermitian) :
    (centeredFilter p δ H Ω h).IsHermitian := by
  refine (isHermitian_filterIntegral p δ hH hh).sub ?_
  have hreal : star (star (WithLp.ofLp Ω) ⬝ᵥ (h *ᵥ WithLp.ofLp Ω)) =
      star (WithLp.ofLp Ω) ⬝ᵥ (h *ᵥ WithLp.ofLp Ω) := by
    rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, hh.eq, dotProduct_comm,
      Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [IsHermitian, conjTranspose_smul, conjTranspose_one, hreal]

/-- **`M Ω = 0`** (`03-quasilocal.tex`, lines 252–257). -/
theorem centeredFilter_mulVec_eq_zero {p : ℕ} (hp : 1 ≤ p) {δ Δ E₀ : ℝ}
    (hδ : 0 < δ) (hδΔ : δ ≤ Δ) {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : H *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω)
    (hgap : (H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (h : Matrix n n ℂ) :
    centeredFilter p δ H Ω h *ᵥ WithLp.ofLp Ω = 0 := by
  rw [centeredFilter, Matrix.sub_mulVec,
    filterIntegral_mulVec_of_posSemidef_gap hp hδ hδΔ hH hΩ hHΩ hgap h, Matrix.smul_mulVec,
    Matrix.one_mulVec, sub_self]

/-- **`∑ᵢ Mᵢ = H - E₀ I`** (`03-quasilocal.tex`, `eq:quasilocal-filter-sum`,
lines 258–261), because filtering fixes `H` and `⟨Ω, H Ω⟩ = E₀`. -/
theorem sum_centeredFilter {p : ℕ} (hp : 1 ≤ p) {δ E₀ : ℝ} (hδ : 0 < δ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : H *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω)
    {ι : Type*} (s : Finset ι) (h : ι → Matrix n n ℂ) (hsum : ∑ i ∈ s, h i = H) :
    ∑ i ∈ s, centeredFilter p δ H Ω (h i) = H - (E₀ : ℂ) • 1 := by
  simp only [centeredFilter, Finset.sum_sub_distrib]
  rw [← filterIntegral_finset_sum hp hδ hH, hsum, filterIntegral_self hp hδ, ← Finset.sum_smul]
  congr 2
  rw [← dotProduct_sum, ← Matrix.sum_mulVec, hsum, hHΩ, dotProduct_smul,
    star_dotProduct_self_of_norm_eq_one hΩ, smul_eq_mul, mul_one]

/-- **`‖M‖ ≤ ‖h‖ (‖f‖₁ + 1)`** (`03-quasilocal.tex`, `eq:quasilocal-filter-sum`). -/
theorem norm_centeredFilter_le {p : ℕ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1) (h : Matrix n n ℂ) :
    ‖centeredFilter p δ H Ω h‖ ≤ ‖h‖ * (filterL1 p δ + 1) := by
  calc ‖centeredFilter p δ H Ω h‖
      ≤ ‖filterIntegral p δ H h‖ +
          ‖(star (WithLp.ofLp Ω) ⬝ᵥ (h *ᵥ WithLp.ofLp Ω)) • (1 : Matrix n n ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ filterL1 p δ * ‖h‖ + ‖h‖ :=
        add_le_add (norm_filterIntegral_le hp hδ hH h)
          ((norm_smul_one_le _).trans (norm_star_dotProduct_mulVec_le hΩ h))
    _ = ‖h‖ * (filterL1 p δ + 1) := by ring

/-! ### The positive constraints -/

/-- **The positive constraint** `k = |M| / c` (`03-quasilocal.tex`, line 263). -/
noncomputable def positiveConstraint (c : ℝ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  c⁻¹ • CFC.abs M

theorem positiveConstraint_nonneg {c : ℝ} (hc : 0 ≤ c) (M : Matrix n n ℂ) :
    0 ≤ positiveConstraint c M :=
  smul_nonneg (inv_nonneg.mpr hc) (CFC.abs_nonneg M)

/-- `‖k‖ = c⁻¹ ‖M‖`. -/
theorem norm_positiveConstraint {c : ℝ} (hc : 0 ≤ c) (M : Matrix n n ℂ) :
    ‖positiveConstraint c M‖ = c⁻¹ * ‖M‖ := by
  rw [positiveConstraint, norm_smul, CFC.norm_abs, Real.norm_of_nonneg (inv_nonneg.mpr hc)]

/-- `k ≤ 1` when `‖M‖ ≤ c` (`03-quasilocal.tex`, lines 263–266). -/
theorem positiveConstraint_le_one {c : ℝ} (hc : 0 < c) {M : Matrix n n ℂ} (hM : ‖M‖ ≤ c) :
    positiveConstraint c M ≤ 1 := by
  rw [← CStarAlgebra.norm_le_one_iff_of_nonneg _ (positiveConstraint_nonneg hc.le M),
    norm_positiveConstraint hc.le, inv_mul_le_iff₀ hc, mul_one]
  exact hM

/-- `ker |M| ⊇ ker M` for Hermitian `M` (`03-quasilocal.tex`, lines 264–265). -/
theorem positiveConstraint_mulVec_eq_zero (c : ℝ) {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {v : n → ℂ} (hv : M *ᵥ v = 0) : positiveConstraint c M *ᵥ v = 0 := by
  have habs : CFC.abs M = CFC.sqrt (M * M) := by
    rw [CFC.abs]; congr 1; rw [star_eq_conjTranspose, hM.eq]
  have hMM : 0 ≤ M * M := CFC.mul_self_nonneg_of_isSelfAdjoint hM
  rw [positiveConstraint, Matrix.smul_mulVec, habs,
    sqrt_mulVec_eq_zero hMM (by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]),
    smul_zero]

/-- `c⁻¹ M ≤ k` for Hermitian `M` (`03-quasilocal.tex`, line 264). -/
theorem smul_le_positiveConstraint {c : ℝ} (hc : 0 ≤ c) {M : Matrix n n ℂ}
    (hM : M.IsHermitian) : c⁻¹ • M ≤ positiveConstraint c M :=
  smul_le_smul_of_nonneg_left (CFC.le_abs_of_isSelfAdjoint hM) (inv_nonneg.mpr hc)

/-! ### The assembled spectral statement -/

/-- The normalization `c_* = max {1, J (‖f‖₁ + 1)}` (`03-quasilocal.tex`, line 263). -/
noncomputable def positiveNormalization (p : ℕ) (δ J : ℝ) : ℝ :=
  max 1 (J * (filterL1 p δ + 1))

theorem one_le_positiveNormalization (p : ℕ) (δ J : ℝ) : 1 ≤ positiveNormalization p δ J :=
  le_max_left _ _

theorem positiveNormalization_pos (p : ℕ) (δ J : ℝ) : 0 < positiveNormalization p δ J :=
  zero_lt_one.trans_le (one_le_positiveNormalization p δ J)

/-- **Positive replacement, spectral part** (Proposition 4.3, `prop:positive`,
`eq:quasilocal-positive`, `03-quasilocal.tex`, lines 220–284, with `δ = Δ / 2`). Let
`H = ∑ᵢ hᵢ` with Hermitian terms of norm at most `J`, a unit vector `Ω` with
`H Ω = E₀ Ω`, and `H - E₀ I ≥ Δ (I - |Ω⟩⟨Ω|)` with `Δ > 0`. Put
`kᵢ = |Mᵢ| / c_*` for the centered filtered terms `Mᵢ` with `δ = Δ / 2`. Then
`0 ≤ kᵢ ≤ 1`, `kᵢ Ω = 0`, and
`∑ᵢ kᵢ ≥ c_*⁻¹ (H - E₀ I) ≥ (Δ / c_*) (I - |Ω⟩⟨Ω|)`. -/
theorem positive_replacement {p : ℕ} (hp : 1 ≤ p) {Δ E₀ J : ℝ} (hΔ : 0 < Δ)
    {H : Matrix n n ℂ} {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : H *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω)
    (hgap : (H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    {ι : Type*} [Fintype ι] (h : ι → Matrix n n ℂ) (hh : ∀ i, (h i).IsHermitian)
    (hJ : ∀ i, ‖h i‖ ≤ J) (hsum : ∑ i, h i = H) :
    let c := positiveNormalization p (Δ / 2) J
    let k := fun i => positiveConstraint c (centeredFilter p (Δ / 2) H Ω (h i))
    (∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ WithLp.ofLp Ω = 0) ∧
      c⁻¹ • (H - (E₀ : ℂ) • 1) ≤ ∑ i, k i ∧
      ((Δ / c : ℝ) : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
        c⁻¹ • (H - (E₀ : ℂ) • 1) := by
  intro c k
  have hH : H.IsHermitian := by
    rw [← hsum, IsHermitian, conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => hh i
  have hδ : 0 < Δ / 2 := half_pos hΔ
  have hδΔ : Δ / 2 ≤ Δ := half_le_self hΔ.le
  have hc : 0 < c := positiveNormalization_pos p (Δ / 2) J
  have hMh : ∀ i, (centeredFilter p (Δ / 2) H Ω (h i)).IsHermitian := fun i =>
    isHermitian_centeredFilter p _ hH Ω (hh i)
  have hMn : ∀ i, ‖centeredFilter p (Δ / 2) H Ω (h i)‖ ≤ c := by
    intro i
    refine (norm_centeredFilter_le hp hδ hH hΩ (h i)).trans ?_
    refine (mul_le_mul_of_nonneg_right (hJ i)
      (add_nonneg (filterL1_nonneg _ _) zero_le_one)).trans ?_
    exact le_max_right _ _
  refine ⟨fun i => ⟨positiveConstraint_nonneg hc.le _, positiveConstraint_le_one hc (hMn i),
    positiveConstraint_mulVec_eq_zero c (hMh i)
      (centeredFilter_mulVec_eq_zero hp hδ hδΔ hH hΩ hHΩ hgap (h i))⟩, ?_, ?_⟩
  · rw [← sum_centeredFilter hp hδ hH hΩ hHΩ Finset.univ h hsum, Finset.smul_sum]
    exact Finset.sum_le_sum fun i _ => smul_le_positiveConstraint hc.le (hMh i)
  · have hgap' : (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
        H - (E₀ : ℂ) • 1 := by
      rw [Matrix.le_iff]; exact hgap
    have := smul_le_smul_of_nonneg_left hgap' (inv_nonneg.mpr hc.le)
    convert this using 1
    rw [← Complex.coe_smul, smul_smul, ← Complex.ofReal_mul, inv_mul_eq_div]

end SpectralFilter
