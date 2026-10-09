/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralFilter.PositiveReplacement

/-!
# Locality of filtered operators and of their absolute values

Let `L` be a linear map on matrices, to be thought of as a conditional expectation onto the
operators supported in a ball of radius `l`. Suppose that the Heisenberg evolution of `A`
is localized by `L` up to `‖A‖ min {2, C e^{v |t| - c l}}`. Splitting the time integral at
`|t| = c l / (2 v)` shows that the filtered operator `∫ f(t) e^{itH} A e^{-itH} dt` is
localized up to a stretched exponential `e^{-c' l^α}`, `α = p / (p + 1)`; the constants
depend only on `p, δ, C, v, c`. For a contraction `L` fixing `|L M|`, the square-root
estimate transfers the localization of a Hermitian `M` to its absolute value.

## Main results

* `SpectralFilter.abs_spectralKernel_le_tail`: `|f(t)| ≤ K₀ (1 + |t|)^{-2} e^{-(c/2) T^α}`
  for `|t| ≥ T`.
* `SpectralFilter.norm_filterIntegral_sub_map_le`: the explicit two-term localization bound.
* `SpectralFilter.exists_norm_filterIntegral_sub_map_le`: the stretched-exponential form.
* `SpectralFilter.norm_abs_sub_map_abs_le`: localization of `|M|`.
* `SpectralFilter.exists_norm_positiveConstraint_sub_map_le`: the tail estimate
  `eq:quasilocal-positive-tail` of Proposition 4.3 for an abstract localizing map.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 4.3 (`prop:positive`), section file `03-quasilocal.tex`,
  lines 285–334 (`eq:quasilocal-filter-locality` and the absolute-value step).
  The proofs here are written from the paper.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open MeasureTheory Complex
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace SpectralFilter

/-! ### A tail bound for the kernel -/

/-- The kernel exponent `α = p / (p + 1)`. -/
noncomputable def kernelExponent (p : ℕ) : ℝ := (p : ℝ) / (p + 1)

theorem kernelExponent_pos {p : ℕ} (hp : 1 ≤ p) : 0 < kernelExponent p := by
  have : (0 : ℝ) < p := by exact_mod_cast hp
  unfold kernelExponent; positivity

theorem kernelExponent_le_one (p : ℕ) : kernelExponent p ≤ 1 := by
  unfold kernelExponent
  rw [div_le_one (by positivity)]; linarith

/-- **Kernel tail**: there is `K₀ > 0` with
`|f(t)| ≤ K₀ (1 + |t|)^{-2} e^{-(c/2) T^α}` whenever `0 ≤ T ≤ |t|`, where `c` is the
decay rate of Lemma 4.2. The factor `(1 + |t|)^{-2}` makes the bound integrable. -/
theorem abs_spectralKernel_le_tail {p : ℕ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ t T : ℝ, 0 ≤ T → T ≤ |t| →
      |spectralKernel p δ t| ≤
        K₀ / (1 + |t|) ^ 2 * Real.exp (-(kernelDecayRate p δ / 2 * T ^ kernelExponent p)) := by
  obtain ⟨A₄, hA₄⟩ := one_add_abs_pow_mul_abs_spectralKernel_le hp hδ 4
  set K := kernelDecayConst δ
  set c := kernelDecayRate p δ
  have hK : 0 < K := kernelDecayConst_pos hδ
  have hc : 0 < c := kernelDecayRate_pos hp hδ
  set A := max A₄ 1
  refine ⟨Real.sqrt (A * K), Real.sqrt_pos.mpr (by positivity), fun t T hT hTt => ?_⟩
  set R := 1 + |t| with hR
  have hR0 : 0 < R := by positivity
  set α := kernelExponent p
  have hα : 0 < α := kernelExponent_pos hp
  have hf0 := abs_nonneg (spectralKernel p δ t)
  have h1 : |spectralKernel p δ t| ≤ A / R ^ 4 := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact (hA₄ t).trans (le_max_left _ _)
  have h2 : |spectralKernel p δ t| ≤ K * Real.exp (-(c * |t| ^ α)) :=
    abs_spectralKernel_le_exp hp hδ t
  have hTα : T ^ α ≤ |t| ^ α := Real.rpow_le_rpow hT hTt hα.le
  -- `|f|² ≤ (A / R⁴) (K e^{-c |t|^α})`.
  have hsq : |spectralKernel p δ t| ^ 2 ≤ A / R ^ 4 * (K * Real.exp (-(c * |t| ^ α))) := by
    rw [sq]; exact mul_le_mul h1 h2 hf0 (by positivity)
  have hexp : Real.exp (-(c * |t| ^ α)) =
      Real.exp (-(c / 2 * |t| ^ α)) * Real.exp (-(c / 2 * |t| ^ α)) := by
    rw [← Real.exp_add]; ring_nf
  set X := Real.sqrt (A * K) / R ^ 2 * Real.exp (-(c / 2 * |t| ^ α))
  have hX : X ^ 2 = A / R ^ 4 * (K * Real.exp (-(c * |t| ^ α))) := by
    simp only [X, div_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ A * K), hexp]
    ring
  have hfX : |spectralKernel p δ t| ≤ X := by
    rw [← hX] at hsq
    exact (sq_le_sq₀ hf0 (by positivity)).mp hsq
  refine hfX.trans ?_
  simp only [X]
  gcongr

/-- `∫ (1 + |t|)^{-2} dt < ∞`. -/
theorem integrable_inv_one_add_abs_sq :
    Integrable fun t : ℝ => 1 / (1 + |t|) ^ 2 := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (0 : ℝ) < 1 + |t| := by positivity
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg h1.le, Real.rpow_two, one_div]

/-- `-c l / 2 ≤ c / 2 - (c / 2) l^α` for `0 ≤ l`, `0 ≤ c` and `0 < α ≤ 1`. -/
theorem neg_mul_le_sub_mul_rpow {c l α : ℝ} (hc : 0 ≤ c) (hl : 0 ≤ l) (hα : 0 < α)
    (hα1 : α ≤ 1) : -(c * l / 2) ≤ c / 2 - c / 2 * l ^ α := by
  have : l ^ α ≤ 1 + l := by
    rcases le_total l 1 with h | h
    · have := Real.rpow_le_one hl h hα.le; linarith
    · have := Real.rpow_le_rpow_of_exponent_le h hα1; rw [Real.rpow_one] at this; linarith
  nlinarith

/-! ### Localization of the filtered operator -/

section Matrix

open Matrix

/-- **Localization of the filtered operator**, explicit form (`03-quasilocal.tex`,
`eq:quasilocal-filter-locality`, lines 285–297). There is `K₁ ≥ 0`, depending only on `p`
and `δ`, such that for every linear map `L` on matrices, every Hermitian `H`, and every `A`:
if `‖τ_t(A) - L τ_t(A)‖ ≤ ‖A‖ min {2, C e^{v |t| - c l}}` for all `t`, with `v, c > 0`,
`C, l ≥ 0`, then
`‖F(A) - L F(A)‖ ≤ ‖A‖ (C e^{-c l / 2} ‖f‖₁ + K₁ e^{-(c_f/2) (c l / (2 v))^α})`, where
`F(A) = ∫ f(t) e^{itH} A e^{-itH} dt` and `c_f` is the kernel decay rate. -/
theorem exists_norm_filterIntegral_sub_map_le' {p : ℕ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ},
      H.IsHermitian → ∀ (A : Matrix n n ℂ) (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
      {C v c l : ℝ}, 0 ≤ C → 0 < v → 0 < c → 0 ≤ l →
      (∀ t : ℝ, ‖hermitianUnitaryPath H t * A * hermitianUnitaryPath H (-t) -
          L (hermitianUnitaryPath H t * A * hermitianUnitaryPath H (-t))‖ ≤
        ‖A‖ * min 2 (C * Real.exp (v * |t| - c * l))) →
      ‖filterIntegral p δ H A - L (filterIntegral p δ H A)‖ ≤
        ‖A‖ * (C * Real.exp (-(c * l / 2)) * filterL1 p δ +
          K₁ * Real.exp (-(kernelDecayRate p δ / 2 * (c * l / (2 * v)) ^ kernelExponent p))) := by
  obtain ⟨K₀, hK₀, htail⟩ := abs_spectralKernel_le_tail hp hδ
  set I := ∫ t : ℝ, 1 / (1 + |t|) ^ 2
  have hI : 0 ≤ I := integral_nonneg fun t => by positivity
  refine ⟨2 * K₀ * I, by positivity, ?_⟩
  intro n _ _ H hH A L C v c l hC hv hc hl hτ
  set T := c * l / (2 * v) with hTdef
  have hT : 0 ≤ T := by positivity
  set ε := Real.exp (-(kernelDecayRate p δ / 2 * T ^ kernelExponent p))
  set τ : ℝ → Matrix n n ℂ := fun t => hermitianUnitaryPath H t * A * hermitianUnitaryPath H (-t)
  set Lc := LinearMap.toContinuousLinearMap L
  have hLc : ∀ X, Lc X = L X := fun X => rfl
  have hint := integrable_filterIntegrand hp hδ hH A
  have hrepr : filterIntegral p δ H A - L (filterIntegral p δ H A) =
      ∫ t, (spectralKernel p δ t : ℂ) • (τ t - L (τ t)) := by
    rw [filterIntegral, ← hLc, ← Lc.integral_comp_comm hint,
      ← integral_sub hint (Lc.integrable_comp hint)]
    congr 1; funext t
    rw [hLc, map_smul, smul_sub]
  rw [hrepr]
  -- The pointwise bound.
  set g : ℝ → ℝ := fun t => ‖A‖ * (C * Real.exp (-(c * l / 2)) * |spectralKernel p δ t| +
    2 * K₀ * ε * (1 / (1 + |t|) ^ 2))
  have hpt : ∀ t, ‖(spectralKernel p δ t : ℂ) • (τ t - L (τ t))‖ ≤ g t := by
    intro t
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hf0 := abs_nonneg (spectralKernel p δ t)
    have hb := hτ t
    have hA0 := norm_nonneg A
    rcases le_or_gt |t| T with ht | ht
    · have hmin : min 2 (C * Real.exp (v * |t| - c * l)) ≤ C * Real.exp (-(c * l / 2)) := by
        refine (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC)
        have : v * |t| ≤ v * T := mul_le_mul_of_nonneg_left ht hv.le
        have hvT : v * T = c * l / 2 := by rw [hTdef]; field_simp
        linarith
      calc |spectralKernel p δ t| * ‖τ t - L (τ t)‖
          ≤ |spectralKernel p δ t| * (‖A‖ * (C * Real.exp (-(c * l / 2)))) :=
            mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hmin hA0)) hf0
        _ ≤ g t := by
            simp only [g]
            have : 0 ≤ ‖A‖ * (2 * K₀ * ε * (1 / (1 + |t|) ^ 2)) := by positivity
            nlinarith
    · have hft := htail t T hT ht.le
      calc |spectralKernel p δ t| * ‖τ t - L (τ t)‖
          ≤ (K₀ / (1 + |t|) ^ 2 * ε) * (‖A‖ * 2) :=
            mul_le_mul hft (hb.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hA0))
              (norm_nonneg _) (by positivity)
        _ ≤ g t := by
            simp only [g]
            have : 0 ≤ ‖A‖ * (C * Real.exp (-(c * l / 2)) * |spectralKernel p δ t|) := by
              positivity
            have he : K₀ / (1 + |t|) ^ 2 * ε * (‖A‖ * 2) =
                ‖A‖ * (2 * K₀ * ε * (1 / (1 + |t|) ^ 2)) := by ring
            nlinarith
  have hgint : Integrable g :=
    (((integrable_spectralKernel hp hδ).abs.const_mul _).add
      (integrable_inv_one_add_abs_sq.const_mul _)).const_mul _
  refine (norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)).trans_eq ?_
  simp only [g]
  rw [integral_const_mul, integral_add ((integrable_spectralKernel hp hδ).abs.const_mul _)
    (integrable_inv_one_add_abs_sq.const_mul _), integral_const_mul, integral_const_mul]
  simp only [filterL1, I, ε]
  ring

/-- **Localization of the filtered operator** (`03-quasilocal.tex`,
`eq:quasilocal-filter-locality`, lines 285–297): with `α = p / (p + 1)`, there are
`C' ≥ 0` and `c' > 0`, depending only on `p, δ, C, v, c`, such that the localization
hypothesis of `exists_norm_filterIntegral_sub_map_le'` gives
`‖F(A) - L F(A)‖ ≤ C' e^{-c' l^α} ‖A‖`. -/
theorem exists_norm_filterIntegral_sub_map_le {p : ℕ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    {C v c : ℝ} (hC : 0 ≤ C) (hv : 0 < v) (hc : 0 < c) :
    ∃ C' c' : ℝ, 0 ≤ C' ∧ 0 < c' ∧ ∀ {n : Type*} [Fintype n] [DecidableEq n]
      {H : Matrix n n ℂ}, H.IsHermitian → ∀ (A : Matrix n n ℂ)
      (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) {l : ℝ}, 0 ≤ l →
      (∀ t : ℝ, ‖hermitianUnitaryPath H t * A * hermitianUnitaryPath H (-t) -
          L (hermitianUnitaryPath H t * A * hermitianUnitaryPath H (-t))‖ ≤
        ‖A‖ * min 2 (C * Real.exp (v * |t| - c * l))) →
      ‖filterIntegral p δ H A - L (filterIntegral p δ H A)‖ ≤
        C' * Real.exp (-(c' * l ^ kernelExponent p)) * ‖A‖ := by
  obtain ⟨K₁, hK₁, hloc⟩ := exists_norm_filterIntegral_sub_map_le' hp hδ
  set α := kernelExponent p
  have hα := kernelExponent_pos hp
  have hα1 := kernelExponent_le_one p
  set cf := kernelDecayRate p δ
  have hcf : 0 < cf := kernelDecayRate_pos hp hδ
  set c₂ := min (c / 2) (cf / 2 * (c / (2 * v)) ^ α)
  have hc₂ : 0 < c₂ := lt_min (by positivity) (by positivity)
  refine ⟨C * Real.exp (c / 2) * filterL1 p δ + K₁, c₂,
    add_nonneg (by have := filterL1_nonneg p δ; positivity) hK₁, hc₂, ?_⟩
  intro n _ _ H hH A L l hl hτ
  refine (hloc hH A L hC hv hc hl hτ).trans ?_
  have hl' : 0 ≤ l ^ α := Real.rpow_nonneg hl _
  have e1 : Real.exp (-(c * l / 2)) ≤ Real.exp (c / 2) * Real.exp (-(c₂ * l ^ α)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ((neg_mul_le_sub_mul_rpow hc.le hl hα hα1).trans ?_)
    have : c₂ * l ^ α ≤ c / 2 * l ^ α := mul_le_mul_of_nonneg_right (min_le_left _ _) hl'
    linarith
  have e2 : Real.exp (-(cf / 2 * (c * l / (2 * v)) ^ α)) ≤ Real.exp (-(c₂ * l ^ α)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    rw [show c * l / (2 * v) = c / (2 * v) * l by ring,
      Real.mul_rpow (by positivity) hl, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) hl'
  have hA0 := norm_nonneg A
  have hf1 := filterL1_nonneg p δ
  calc ‖A‖ * (C * Real.exp (-(c * l / 2)) * filterL1 p δ +
          K₁ * Real.exp (-(cf / 2 * (c * l / (2 * v)) ^ α)))
      ≤ ‖A‖ * (C * (Real.exp (c / 2) * Real.exp (-(c₂ * l ^ α))) * filterL1 p δ +
          K₁ * Real.exp (-(c₂ * l ^ α))) := by gcongr
    _ = (C * Real.exp (c / 2) * filterL1 p δ + K₁) * Real.exp (-(c₂ * l ^ α)) * ‖A‖ := by
        ring

/-- **Localization of the absolute value** (`03-quasilocal.tex`, lines 318–334): if `L` is
a contraction, `M` and `L M` are Hermitian, and `L` fixes `|L M|`, then
`‖|M| - L |M|‖ ≤ 2 √(2 ‖M‖ ‖M - L M‖)`. -/
theorem norm_abs_sub_map_abs_le {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hcontr : ∀ X, ‖L X‖ ≤ ‖X‖) (hLM : (L M).IsHermitian)
    (hfix : L (CFC.abs (L M)) = CFC.abs (L M)) :
    ‖CFC.abs M - L (CFC.abs M)‖ ≤ 2 * Real.sqrt (2 * ‖M‖ * ‖M - L M‖) := by
  have hdecomp : CFC.abs M - L (CFC.abs M) =
      (CFC.abs M - CFC.abs (L M)) + L (CFC.abs (L M) - CFC.abs M) := by
    rw [map_sub, hfix]; abel
  have hroot : ‖CFC.abs M - CFC.abs (L M)‖ ≤ Real.sqrt (2 * ‖M‖ * ‖M - L M‖) := by
    refine (CFC.norm_abs_sub_abs_le hM hLM).trans (Real.sqrt_le_sqrt ?_)
    have := hcontr M
    have h0 := norm_nonneg (M - L M)
    nlinarith
  rw [hdecomp]
  calc ‖(CFC.abs M - CFC.abs (L M)) + L (CFC.abs (L M) - CFC.abs M)‖
      ≤ ‖CFC.abs M - CFC.abs (L M)‖ + ‖CFC.abs (L M) - CFC.abs M‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (hcontr _))
    _ = 2 * ‖CFC.abs M - CFC.abs (L M)‖ := by rw [norm_sub_rev]; ring
    _ ≤ 2 * Real.sqrt (2 * ‖M‖ * ‖M - L M‖) := by gcongr

/-- **Tail of the positive constraints** (Proposition 4.3, `eq:quasilocal-positive-tail`,
`03-quasilocal.tex`, lines 240–243 and 285–334), for an abstract localizing map. Fix
`p ≥ 1`, `Δ > 0`, `J ≥ 0` and the localization constants `C ≥ 0`, `v, c > 0`. There are
`C₃ ≥ 0`, `c₃ > 0` with the following property. Let `H` be Hermitian, `‖Ω‖ = 1`, `h`
Hermitian with `‖h‖ ≤ J`, `M = ∫ f(t) τ_t(h) dt - ⟨Ω, h Ω⟩ I` (with `δ = Δ / 2`) and
`k = |M| / c_*`. Let `L` be a unital linear contraction preserving Hermitian matrices and
fixing `|L M|`, with `‖τ_t(h) - L τ_t(h)‖ ≤ ‖h‖ min {2, C e^{v |t| - c l}}`. Then
`‖k - L k‖ ≤ C₃ e^{-c₃ l^α}`. -/
theorem exists_norm_positiveConstraint_sub_map_le {p : ℕ} (hp : 1 ≤ p) {Δ J C v c : ℝ}
    (hΔ : 0 < Δ) (hJ : 0 ≤ J) (hC : 0 ≤ C) (hv : 0 < v) (hc : 0 < c) :
    ∃ C₃ c₃ : ℝ, 0 ≤ C₃ ∧ 0 < c₃ ∧ ∀ {n : Type*} [Fintype n] [DecidableEq n]
      {H : Matrix n n ℂ} {Ω : EuclideanSpace ℂ n} {h : Matrix n n ℂ},
      H.IsHermitian → ‖Ω‖ = 1 → h.IsHermitian → ‖h‖ ≤ J →
      ∀ (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ), (∀ X, ‖L X‖ ≤ ‖X‖) → L 1 = 1 →
      (∀ X, X.IsHermitian → (L X).IsHermitian) →
      L (CFC.abs (L (centeredFilter p (Δ / 2) H Ω h))) =
        CFC.abs (L (centeredFilter p (Δ / 2) H Ω h)) →
      ∀ {l : ℝ}, 0 ≤ l →
      (∀ t : ℝ, ‖hermitianUnitaryPath H t * h * hermitianUnitaryPath H (-t) -
          L (hermitianUnitaryPath H t * h * hermitianUnitaryPath H (-t))‖ ≤
        ‖h‖ * min 2 (C * Real.exp (v * |t| - c * l))) →
      ‖positiveConstraint (positiveNormalization p (Δ / 2) J) (centeredFilter p (Δ / 2) H Ω h) -
          L (positiveConstraint (positiveNormalization p (Δ / 2) J)
            (centeredFilter p (Δ / 2) H Ω h))‖ ≤
        C₃ * Real.exp (-(c₃ * l ^ kernelExponent p)) := by
  have hδ : 0 < Δ / 2 := half_pos hΔ
  obtain ⟨C', c', hC', hc', hloc⟩ := exists_norm_filterIntegral_sub_map_le hp hδ hC hv hc
  set cs := positiveNormalization p (Δ / 2) J
  have hcs : 0 < cs := positiveNormalization_pos p (Δ / 2) J
  refine ⟨cs⁻¹ * 2 * Real.sqrt (2 * cs * C' * J), c' / 2, by positivity, by positivity, ?_⟩
  intro n _ _ H Ω h hH hΩ hh hhJ L hcontr hunit hherm hfix l hl hτ
  set M := centeredFilter p (Δ / 2) H Ω h
  have hM : M.IsHermitian := isHermitian_centeredFilter p _ hH Ω hh
  have hMn : ‖M‖ ≤ cs := by
    refine (norm_centeredFilter_le hp hδ hH hΩ h).trans ?_
    refine (mul_le_mul_of_nonneg_right hhJ
      (add_nonneg (filterL1_nonneg _ _) zero_le_one)).trans (le_max_right _ _)
  -- `M - L M` is the localization error of the filtered term.
  have hML : M - L M = filterIntegral p (Δ / 2) H h - L (filterIntegral p (Δ / 2) H h) := by
    simp only [M, centeredFilter, map_sub, map_smul, hunit]; abel
  have hMLn : ‖M - L M‖ ≤ C' * Real.exp (-(c' * l ^ kernelExponent p)) * J := by
    rw [hML]
    refine (hloc hH h L hl hτ).trans ?_
    gcongr
  have habs := norm_abs_sub_map_abs_le hM L hcontr (hherm M hM) hfix
  have hk : positiveConstraint cs M - L (positiveConstraint cs M) =
      cs⁻¹ • (CFC.abs M - L (CFC.abs M)) := by
    simp only [positiveConstraint, LinearMap.map_smul_of_tower, smul_sub]
  rw [hk, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hcs.le)]
  set e := Real.exp (-(c' * l ^ kernelExponent p))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hsqrt : Real.sqrt (2 * ‖M‖ * ‖M - L M‖) ≤
      Real.sqrt (2 * cs * C' * J) * Real.exp (-(c' / 2 * l ^ kernelExponent p)) := by
    have hee : Real.exp (-(c' / 2 * l ^ kernelExponent p)) = Real.sqrt e := by
      rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq he (Real.exp_pos _).le, ← Real.exp_add]
      ring_nf; rfl
    rw [hee, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    calc 2 * ‖M‖ * ‖M - L M‖ ≤ 2 * cs * (C' * e * J) := by
          gcongr
      _ = 2 * cs * C' * J * e := by ring
  calc cs⁻¹ * ‖CFC.abs M - L (CFC.abs M)‖
      ≤ cs⁻¹ * (2 * (Real.sqrt (2 * cs * C' * J) *
          Real.exp (-(c' / 2 * l ^ kernelExponent p)))) := by
        gcongr; exact habs.trans (by gcongr)
    _ = cs⁻¹ * 2 * Real.sqrt (2 * cs * C' * J) *
          Real.exp (-(c' / 2 * l ^ kernelExponent p)) := by ring

end Matrix

end SpectralFilter
