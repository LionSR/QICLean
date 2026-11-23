/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Eigenvalue.GlobalGap
import QICLean.Channel.Schmidt.ProductOverlapBootstrap

/-!
# Normalized approximations of a unit target

A vector with a nonzero component along a unit target can be normalized and phase corrected,
with squared error at most twice the ratio of orthogonal mass to target mass. An operator
fixing the target and shrinking its orthogonal complement improves a nearby unit vector after
normalization and a phase correction; the phase is explicit because normalization alone
preserves the phase of the target component. A unit seed with overlap at least `μ` with the
target gives a normalized filtered approximant with squared error at most `2 δ / μ²` and
Schmidt rank at most `D` times the seed rank.

These are the normalization, changing-target and rank steps of Arad, Kitaev, Landau and
Vazirani (AKLV), arXiv:1301.1162v1, Lemma 6.3 (`l:5`, lines 1021–1052) and Lemma 7.1, for a supplied
approximate projector; its construction is separate.

## Main results

* `inner_sub_inner_smul_unit_eq_zero`, `exists_phase_normalized_of_decomposition`: the
  normalization of a vector with a nonzero target component.
* `Matrix.schmidtRank_phase_normalized_eq`: normalization and a unit phase preserve Schmidt
  rank.
* `LinearMap.exists_normalized_approximation_step`: the changing-target step.
* `Matrix.exists_filtered_approximation_of_overlap`,
  `Matrix.exists_filtered_approximation_of_seven_eighths`: the filtered approximant.
-/

open scoped InnerProductSpace

noncomputable section

/-- Subtracting the component along a unit vector leaves an orthogonal
vector. This is the decomposition used in AKLV, Lemmas 6.3 and 7.1. -/
theorem inner_sub_inner_smul_unit_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (φ ψ : E) (hφ : ‖φ‖ = 1) : ⟪φ, ψ - ⟪φ, ψ⟫_ℂ • φ⟫_ℂ = 0 := by
  rw [inner_sub_right, inner_smul_right, inner_self_eq_one_of_norm_eq_one hφ,
    mul_one, sub_self]

/-- Normalization and a unit phase convert an orthogonal decomposition into
a squared-distance bound. Auxiliary to AKLV, Lemma 6.3. -/
theorem exists_phase_normalized_of_decomposition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (φ χ v : E) (a : ℂ) (hφ : ‖φ‖ = 1) (ha : a ≠ 0)
    (horth : ⟪φ, v⟫_ℂ = 0) (hχ : χ = a • φ + v) :
    χ ≠ 0 ∧ ∃ θ : ℝ,
      let ψ := Complex.exp (θ * Complex.I) • ((‖χ‖ : ℂ)⁻¹ • χ)
      ‖ψ‖ = 1 ∧ ‖φ - ψ‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 / ‖a‖ ^ 2 := by
  have hself : ⟪φ, φ⟫_ℂ = 1 := inner_self_eq_one_of_norm_eq_one hφ
  have hinnerχ : ⟪φ, χ⟫_ℂ = a := by
    simp only [hχ, inner_add_right, inner_smul_right, hself, mul_one, horth, add_zero]
  have hnormχ : ‖χ‖ ^ 2 = ‖a‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [hχ]
    simpa only [norm_smul, hφ, mul_one, pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
        (a • φ) v (by simp only [inner_smul_left, horth, mul_zero])
  have hχne : χ ≠ 0 := by
    intro hz
    apply ha
    simpa only [hz, inner_zero_right] using hinnerχ.symm
  have hn : 0 < ‖χ‖ := norm_pos_iff.mpr hχne
  let u := (‖χ‖ : ℂ)⁻¹ • χ
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  have hinner : ‖⟪φ, u⟫_ℂ‖ ^ 2 = ‖a‖ ^ 2 / ‖χ‖ ^ 2 := by
    simp only [u, inner_smul_right, hinnerχ, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hn, mul_pow, inv_pow, div_eq_inv_mul]
  have hdef : 1 - ‖⟪φ, u⟫_ℂ‖ ^ 2 = ‖v‖ ^ 2 / ‖χ‖ ^ 2 := by
    rw [hinner]
    apply (eq_div_iff (pow_ne_zero _ hn.ne')).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (pow_ne_zero _ hn.ne'), hnormχ]
    ring
  have hbound : 1 - ‖⟪φ, u⟫_ℂ‖ ^ 2 ≤ ‖v‖ ^ 2 / ‖a‖ ^ 2 := by
    rw [hdef]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr ha))
    nlinarith [sq_nonneg ‖v‖]
  obtain ⟨θ, -, hθ⟩ := exists_isMinOn_sq_norm_sub_exp_smul_le_of_gap
    (by norm_num : (0 : ℝ) < 1) hφ hu
    (by simpa only [one_mul, norm_inner_symm] using hbound)
  refine ⟨hχne, θ, ?_, ?_⟩
  · change ‖Complex.exp (θ * Complex.I) • u‖ = 1
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, hu, mul_one]
  · change ‖φ - Complex.exp (θ * Complex.I) • u‖ ^ 2 ≤ _
    convert hθ using 1
    ring

namespace Matrix

/-- Nonzero normalization and unit phase preserve Schmidt rank. This is the
rank invariance used at every normalized step of AKLV, Lemma 6.3. -/
theorem schmidtRank_phase_normalized_eq
    {m n : Type*} [Fintype m] [Fintype n]
    (χ : EuclideanSpace ℂ (m × n)) (hne : χ ≠ 0) (θ : ℝ) :
    Matrix.schmidtRank (WithLp.ofLp (Complex.exp (θ * Complex.I) •
      ((‖χ‖ : ℂ)⁻¹ • χ))) = Matrix.schmidtRank (WithLp.ofLp χ) := by
  rw [WithLp.ofLp_smul, Matrix.schmidtRank_smul_eq_of_ne_zero _
    (Complex.exp_ne_zero _) _, WithLp.ofLp_smul,
    Matrix.schmidtRank_smul_eq_of_ne_zero _
      (inv_ne_zero (by exact_mod_cast (norm_pos_iff.mpr hne).ne')) _]

end Matrix

namespace LinearMap

/-- A normalized approximate-projector step reduces squared distance by at
most four times its squared shrinking factor, allowing a unit complex phase.
AKLV, Lemma 6.3. This auxiliary assumes the operator estimates explicitly;
it does not assert their existence for a Hamiltonian. -/
theorem exists_normalized_approximation_step
    {ι : Type*} [Fintype ι]
    (K : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (φ ψ : EuclideanSpace ℂ ι) (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (hfix : K φ = φ) (δ r : ℝ) (hδ : 0 ≤ δ)
    (hperp : ∀ v : EuclideanSpace ℂ ι, ‖v‖ = 1 → ⟪φ, v⟫_ℂ = 0 →
      ⟪φ, K v⟫_ℂ = 0 ∧ ‖K v‖ ^ 2 ≤ δ)
    (hr : r ≤ 1 / 2) (hclose : ‖φ - ψ‖ ^ 2 ≤ r) :
    K ψ ≠ 0 ∧ ∃ θ : ℝ,
      let χ := Complex.exp (θ * Complex.I) • ((‖K ψ‖ : ℂ)⁻¹ • K ψ)
      ‖χ‖ = 1 ∧ ‖φ - χ‖ ^ 2 ≤ 4 * δ * r := by
  let a : ℂ := ⟪φ, ψ⟫_ℂ
  let v := ψ - a • φ
  have hv : ⟪φ, v⟫_ℂ = 0 := inner_sub_inner_smul_unit_eq_zero φ ψ hφ
  have hdec : ψ = a • φ + v := by dsimp only [v]; abel
  have ha1 : ‖a‖ ≤ 1 := by
    simpa only [a, hφ, hψ, one_mul] using norm_inner_le_norm (𝕜 := ℂ) φ ψ
  have ham : 2 - 2 * ‖a‖ ≤ r := by
    have h := norm_sq_add_norm_sq_sub_le_norm_sub_exp_smul_sq φ ψ 0
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul,
      hφ, hψ, one_pow] at h
    simpa only [a, ← one_add_one_eq_two] using h.trans hclose
  have ha2 : 1 / 2 ≤ ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hvnorm : ‖a‖ ^ 2 + ‖v‖ ^ 2 = 1 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
      (a • φ) v (by simp only [inner_smul_left, hv, mul_zero])
    simpa only [← hdec, norm_smul, hφ, hψ, mul_one, one_pow, pow_two] using h.symm
  have hvr : ‖v‖ ^ 2 ≤ r := by nlinarith [sq_nonneg (1 - ‖a‖)]
  have hr0 : 0 ≤ r := (sq_nonneg _).trans hclose
  obtain ⟨hKvorth, hKvnorm⟩ :=
    Matrix.perpendicular_shrinking_homogeneous K φ δ hperp v hv
  have hKdec : K ψ = a • φ + K v := by rw [hdec, map_add, map_smul, hfix]
  have ha : a ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at ha2
    norm_num at ha2
  obtain ⟨hne, θ, hunit, herror⟩ := exists_phase_normalized_of_decomposition
    φ (K ψ) (K v) a hφ ha hKvorth hKdec
  refine ⟨hne, θ, hunit, herror.trans ?_⟩
  apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr ha))).mpr
  have hb : ‖K v‖ ^ 2 ≤ δ * r :=
    hKvnorm.trans (mul_le_mul_of_nonneg_left hvr hδ)
  have hm := mul_le_mul_of_nonneg_left ha2 (mul_nonneg hδ hr0)
  nlinarith only [hb, hm]

end LinearMap

namespace Matrix

/-- An actual normalized filtered seed, with explicit squared error and
Schmidt-rank bounds. The seed overlap is a lower bound and the output
normalization is proved nonzero. AKLV, Lemmas 6.3 and 7.1. -/
theorem exists_filtered_approximation_of_overlap
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (K : Matrix (m × n) (m × n) ℂ) (φ ξ : EuclideanSpace ℂ (m × n))
    (hφ : ‖φ‖ = 1) (hξ : ‖ξ‖ = 1) (hfix : Matrix.toEuclideanLin K φ = φ)
    (μ δ : ℝ) (hμ : 0 < μ) (hδ : 0 ≤ δ) (hoverlap : μ ≤ ‖⟪φ, ξ⟫_ℂ‖)
    (hperp : ∀ v : EuclideanSpace ℂ (m × n), ‖v‖ = 1 → ⟪φ, v⟫_ℂ = 0 →
      ⟪φ, Matrix.toEuclideanLin K v⟫_ℂ = 0 ∧ ‖Matrix.toEuclideanLin K v‖ ^ 2 ≤ δ)
    (D R : ℕ) (hD : Matrix.operatorSchmidtRank K ≤ D)
    (hR : Matrix.schmidtRank (WithLp.ofLp ξ) ≤ R) :
    Matrix.toEuclideanLin K ξ ≠ 0 ∧ ∃ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 ∧ ‖φ - ψ‖ ^ 2 ≤ 2 * δ / μ ^ 2 ∧
      Matrix.schmidtRank (WithLp.ofLp ψ) ≤ D * R ∧
      ∃ θ : ℝ, ψ = Complex.exp (θ * Complex.I) •
        ((‖Matrix.toEuclideanLin K ξ‖ : ℂ)⁻¹ • Matrix.toEuclideanLin K ξ) := by
  let a := ⟪φ, ξ⟫_ℂ
  let v := ξ - a • φ
  have hv : ⟪φ, v⟫_ℂ = 0 := inner_sub_inner_smul_unit_eq_zero φ ξ hφ
  have hdec : ξ = a • φ + v := by dsimp only [v]; abel
  have ha : a ≠ 0 := by
    intro hz
    have h := hμ.trans_le hoverlap
    change 0 < ‖a‖ at h
    rw [hz, norm_zero] at h
    exact (lt_irrefl 0) h
  have hvnorm : ‖v‖ ^ 2 ≤ 1 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
      (a • φ) v (by simp only [inner_smul_left, hv, mul_zero])
    rw [← hdec, hξ] at h
    nlinarith [sq_nonneg ‖a • φ‖]
  obtain ⟨hKvorth, hKvnorm⟩ := Matrix.perpendicular_shrinking_homogeneous
    (Matrix.toEuclideanLin K) φ δ hperp v hv
  have hKdec : Matrix.toEuclideanLin K ξ = a • φ + Matrix.toEuclideanLin K v := by
    rw [hdec, map_add, map_smul, hfix]
  obtain ⟨hne, θ, hunit, herror⟩ := exists_phase_normalized_of_decomposition
    φ (Matrix.toEuclideanLin K ξ) (Matrix.toEuclideanLin K v) a hφ ha hKvorth hKdec
  let ψ := Complex.exp (θ * Complex.I) •
    ((‖Matrix.toEuclideanLin K ξ‖ : ℂ)⁻¹ • Matrix.toEuclideanLin K ξ)
  refine ⟨hne, ψ, hunit, herror.trans ?_, ?_, θ, rfl⟩
  · calc
      _ ≤ 2 * δ / ‖a‖ ^ 2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hKvnorm.trans (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hvnorm hδ)) (by norm_num))
        (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hμ)
        (pow_le_pow_left₀ hμ.le hoverlap 2)
  · rw [schmidtRank_phase_normalized_eq _ hne θ]
    exact (Matrix.schmidtRank_mulVec_le K (WithLp.ofLp ξ)).trans (Nat.mul_le_mul hD hR)

/-- A seed of overlap at least seven eighths gives norm error `exp(-x)`
when the squared shrinking factor has the corresponding explicit budget.
The rank is the actual filtered rank, at most the product of the two
supplied bounds. AKLV, Lemma 7.1, the accuracy-dependent filtering step. -/
theorem exists_filtered_approximation_of_seven_eighths
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (K : Matrix (m × n) (m × n) ℂ) (φ ξ : EuclideanSpace ℂ (m × n))
    (hφ : ‖φ‖ = 1) (hξ : ‖ξ‖ = 1) (hfix : Matrix.toEuclideanLin K φ = φ)
    (δ x : ℝ) (hδ : 0 ≤ δ) (hoverlap : (7 / 8 : ℝ) ≤ ‖⟪φ, ξ⟫_ℂ‖)
    (hbudget : δ ≤ (49 / 128) * Real.exp (-2 * x))
    (hperp : ∀ v : EuclideanSpace ℂ (m × n), ‖v‖ = 1 → ⟪φ, v⟫_ℂ = 0 →
      ⟪φ, Matrix.toEuclideanLin K v⟫_ℂ = 0 ∧ ‖Matrix.toEuclideanLin K v‖ ^ 2 ≤ δ)
    (D R : ℕ) (hD : Matrix.operatorSchmidtRank K ≤ D)
    (hR : Matrix.schmidtRank (WithLp.ofLp ξ) ≤ R) :
    Matrix.toEuclideanLin K ξ ≠ 0 ∧ ∃ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 ∧ ‖φ - ψ‖ ≤ Real.exp (-x) ∧
      Matrix.schmidtRank (WithLp.ofLp ψ) ≤ D * R ∧
      ∃ θ : ℝ, ψ = Complex.exp (θ * Complex.I) •
        ((‖Matrix.toEuclideanLin K ξ‖ : ℂ)⁻¹ • Matrix.toEuclideanLin K ξ) := by
  obtain ⟨hne, ψ, hunit, herror, hrank, hphase⟩ :=
    exists_filtered_approximation_of_overlap K φ ξ hφ hξ hfix (7 / 8) δ
      (by norm_num) hδ hoverlap hperp D R hD hR
  refine ⟨hne, ψ, hunit, ?_, hrank, hphase⟩
  have hexp : Real.exp (-2 * x) = Real.exp (-x) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hbudget
  norm_num at herror
  nlinarith [Real.exp_pos (-x), norm_nonneg (φ - ψ)]

end Matrix

end
