/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GlobalGap
import QICLean.Analysis.PureStateTraceDistance
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Stability of a global gap under a small perturbation

Let `A` satisfy the global gap `A ≥ g (I - |Ω⟩⟨Ω|)` with `⟨Ω, A Ω⟩ = 0`, and let `B ≥ 0` be
self-adjoint with `‖B - A‖ ≤ ε ≤ g / 4`. Then `B` has a unit ground vector `Ω₀` with
energy `e₀ ∈ [0, ε]`, the gap inequality `B - e₀ I ≥ (g / 2) (I - |Ω₀⟩⟨Ω₀|)` holds (so
`Ω₀` is unique and the gap is at least `g / 2`), and
`g (1 - |⟨Ω, Ω₀⟩|²) ≤ 2 ε`.

The minimizing vector of the quadratic form on the unit sphere is an eigenvector. For a
vector `ψ ⊥ Ω₀`, a combination of `ψ` and `Ω₀` orthogonal to `Ω` has energy at least
`(g - ε)` times its squared norm by the gap of `A`. Since the `Ω₀` component carries energy
`e₀ ≤ g - ε`, this forces `⟨ψ, B ψ⟩ ≥ (g - ε) ‖ψ‖²`: this is the min–max step of the source.

## Main results

* `exists_unit_eigenvector_re_inner_le`: a unit eigenvector minimizing the quadratic form.
* `exists_gap_of_norm_sub_le`: the perturbation statement for operators.
* `Matrix.exists_posSemidef_gap_of_norm_sub_le`: the same for matrices, with the gaps in
  operator form and the phase-minimized distance `min_θ ‖Ω₀ - e^{iθ} Ω‖² ≤ 4 ε / g`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 4.5 (`prop:truncation`), section file `03-quasilocal.tex`,
  lines 487–505. The proof here is written from the paper.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Complex
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- A self-adjoint operator on a nontrivial finite-dimensional space has a unit eigenvector
`Ω₀` whose energy `⟨Ω₀, T Ω₀⟩` is the minimum of the quadratic form on unit vectors. -/
theorem exists_unit_eigenvector_re_inner_le [Nontrivial E] {T : E →L[ℂ] E}
    (hT : (T : E →ₗ[ℂ] E).IsSymmetric) :
    ∃ Ω₀ : E, ‖Ω₀‖ = 1 ∧ T Ω₀ = ((re ⟪Ω₀, T Ω₀⟫_ℂ : ℝ) : ℂ) • Ω₀ ∧
      ∀ ψ : E, re ⟪Ω₀, T Ω₀⟫_ℂ * ‖ψ‖ ^ 2 ≤ re ⟪ψ, T ψ⟫_ℂ := by
  have := FiniteDimensional.proper_rclike ℂ E
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hT' : IsSelfAdjoint T := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
  have H₁ : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere _ _
  have H₂ : (Metric.sphere (0 : E) 1).Nonempty :=
    ⟨(‖x‖⁻¹ : ℂ) • x, by simp [norm_smul, hx]⟩
  obtain ⟨x₀, hx₀, hmin⟩ := H₁.exists_isMinOn H₂ T.reApplyInnerSelf_continuous.continuousOn
  have hx₀n : ‖x₀‖ = 1 := by simpa using hx₀
  have hre : ∀ y : E, T.reApplyInnerSelf y = re ⟪y, T y⟫_ℂ := fun y => by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_conj_symm, RCLike.conj_re]; rfl
  have hmin' : IsMinOn T.reApplyInnerSelf (Metric.sphere 0 ‖x₀‖) x₀ := by
    rwa [hx₀n]
  refine ⟨x₀, hx₀n, ?_, ?_⟩
  · have h := hT'.eq_smul_self_of_isLocalExtrOn (Or.inl hmin'.isLocalMinOn)
    rw [ContinuousLinearMap.rayleighQuotient, hx₀n, one_pow, div_one, hre] at h
    exact h
  · intro ψ
    rcases eq_or_ne ψ 0 with rfl | hψ
    · simp
    have hn : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
    set y : E := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ with hy
    have hyn : y ∈ Metric.sphere (0 : E) 1 := by
      simp [hy, norm_smul, hn.ne']
    have h := hmin hyn
    simp only [Set.mem_ofPred_eq, hre] at h
    have hyq : re ⟪y, T y⟫_ℂ = (‖ψ‖⁻¹) ^ 2 * re ⟪ψ, T ψ⟫_ℂ := by
      rw [hy, map_smul, inner_smul_left, inner_smul_right, conj_ofReal, ← mul_assoc,
        ← ofReal_mul, re_ofReal_mul, sq]
    rw [hyq] at h
    have h2 : 0 < ‖ψ‖ ^ 2 := by positivity
    calc re ⟪x₀, T x₀⟫_ℂ * ‖ψ‖ ^ 2 ≤ ((‖ψ‖⁻¹) ^ 2 * re ⟪ψ, T ψ⟫_ℂ) * ‖ψ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h h2.le
      _ = re ⟪ψ, T ψ⟫_ℂ := by field_simp

omit [FiniteDimensional ℂ E] in
/-- The quadratic form splits along an eigenvector: if `B Ω₀ = E Ω₀`, `‖Ω₀‖ = 1` and
`⟨Ω₀, w⟩ = 0`, then `Re ⟨x Ω₀ + w, B (x Ω₀ + w)⟩ = |x|² E + Re ⟨w, B w⟩`. -/
theorem re_inner_smul_add_eigenvector {B : E →L[ℂ] E} (hB : (B : E →ₗ[ℂ] E).IsSymmetric)
    {Ω₀ w : E} {e : ℝ} (hΩ₀ : ‖Ω₀‖ = 1) (heig : B Ω₀ = (e : ℂ) • Ω₀) (hw : ⟪Ω₀, w⟫_ℂ = 0)
    (x : ℂ) :
    re ⟪x • Ω₀ + w, B (x • Ω₀ + w)⟫_ℂ = ‖x‖ ^ 2 * e + re ⟪w, B w⟫_ℂ := by
  have hw' : ⟪w, Ω₀⟫_ℂ = 0 := by rw [← inner_conj_symm, hw, map_zero]
  have hBw : ⟪Ω₀, B w⟫_ℂ = 0 := by
    have := hB Ω₀ w
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [← this, heig, inner_smul_left, hw, mul_zero]
  have hΩΩ : ⟪Ω₀, Ω₀⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ₀]; simp
  simp only [map_add, map_smul, heig, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, hw', hBw, hΩΩ, mul_zero, zero_add, add_zero, mul_one]
  rw [add_re]
  congr 1
  have : x * (e * (starRingEnd ℂ) x) = ((‖x‖ ^ 2 * e : ℝ) : ℂ) := by
    rw [mul_left_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [this, ofReal_re]

/-- **Stability of a global gap** (`03-quasilocal.tex`, lines 487–499). Let
`g (‖ψ‖² - |⟨Ω, ψ⟩|²) ≤ Re ⟨ψ, A ψ⟩` for all `ψ`, `‖Ω‖ = 1`, `Re ⟨Ω, A Ω⟩ = 0`, and let `B` be
symmetric and positive with `‖B - A‖ ≤ ε ≤ g / 4`, `g > 0`. Then there are `e₀ ∈ [0, ε]` and
a unit `Ω₀` with `B Ω₀ = e₀ Ω₀`,
`(g / 2) (‖ψ‖² - |⟨Ω₀, ψ⟩|²) ≤ Re ⟨ψ, B ψ⟩ - e₀ ‖ψ‖²` for all `ψ`, and
`g (1 - |⟨Ω, Ω₀⟩|²) ≤ 2 ε`. -/
theorem exists_gap_of_norm_sub_le {A B : E →L[ℂ] E} (hB : (B : E →ₗ[ℂ] E).IsSymmetric)
    {Ω : E} (hΩ : ‖Ω‖ = 1) {g ε : ℝ} (hg : 0 < g) (hε : ε ≤ g / 4)
    (hA : ∀ ψ, g * (‖ψ‖ ^ 2 - ‖⟪Ω, ψ⟫_ℂ‖ ^ 2) ≤ re ⟪ψ, A ψ⟫_ℂ)
    (hAΩ : re ⟪Ω, A Ω⟫_ℂ = 0) (hBnn : ∀ ψ, 0 ≤ re ⟪ψ, B ψ⟫_ℂ) (hAB : ‖B - A‖ ≤ ε) :
    ∃ (e : ℝ) (Ω₀ : E), ‖Ω₀‖ = 1 ∧ B Ω₀ = (e : ℂ) • Ω₀ ∧ 0 ≤ e ∧ e ≤ ε ∧
      (∀ ψ, g / 2 * (‖ψ‖ ^ 2 - ‖⟪Ω₀, ψ⟫_ℂ‖ ^ 2) ≤ re ⟪ψ, B ψ⟫_ℂ - e * ‖ψ‖ ^ 2) ∧
      g * (1 - ‖⟪Ω, Ω₀⟫_ℂ‖ ^ 2) ≤ 2 * ε := by
  have : Nontrivial E := ⟨⟨Ω, 0, fun h => by simp [h] at hΩ⟩⟩
  obtain ⟨Ω₀, hΩ₀, heig, hmin⟩ := exists_unit_eigenvector_re_inner_le hB
  set e := re ⟪Ω₀, B Ω₀⟫_ℂ with he
  -- The two quadratic forms differ by at most `ε ‖ψ‖²`.
  have hdiff : ∀ ψ, |re ⟪ψ, B ψ⟫_ℂ - re ⟪ψ, A ψ⟫_ℂ| ≤ ε * ‖ψ‖ ^ 2 := by
    intro ψ
    have h1 : re ⟪ψ, B ψ⟫_ℂ - re ⟪ψ, A ψ⟫_ℂ = re ⟪ψ, (B - A) ψ⟫_ℂ := by
      rw [sub_apply, inner_sub_right, sub_re]
    rw [h1]
    calc |re ⟪ψ, (B - A) ψ⟫_ℂ| ≤ ‖⟪ψ, (B - A) ψ⟫_ℂ‖ := abs_re_le_norm _
      _ ≤ ‖ψ‖ * ‖(B - A) ψ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ψ‖ * (‖B - A‖ * ‖ψ‖) := by gcongr; exact (B - A).le_opNorm ψ
      _ ≤ ‖ψ‖ * (ε * ‖ψ‖) := by gcongr
      _ = ε * ‖ψ‖ ^ 2 := by ring
  have hup : ∀ ψ, re ⟪ψ, B ψ⟫_ℂ ≤ re ⟪ψ, A ψ⟫_ℂ + ε * ‖ψ‖ ^ 2 := fun ψ => by
    linarith [le_abs_self (re ⟪ψ, B ψ⟫_ℂ - re ⟪ψ, A ψ⟫_ℂ), hdiff ψ]
  have hlow : ∀ ψ, re ⟪ψ, A ψ⟫_ℂ - ε * ‖ψ‖ ^ 2 ≤ re ⟪ψ, B ψ⟫_ℂ := fun ψ => by
    linarith [neg_abs_le (re ⟪ψ, B ψ⟫_ℂ - re ⟪ψ, A ψ⟫_ℂ), hdiff ψ]
  have he0 : 0 ≤ e := hBnn Ω₀
  have heε : e ≤ ε := by
    have := (hmin Ω).trans (hup Ω)
    rw [hΩ, hAΩ] at this
    linarith
  have hε0 : 0 ≤ ε := he0.trans heε
  have hover : g * (1 - ‖⟪Ω, Ω₀⟫_ℂ‖ ^ 2) ≤ 2 * ε := by
    have h1 := hA Ω₀
    have h2 := hlow Ω₀
    rw [hΩ₀] at h1 h2
    linarith
  -- The energy of every vector orthogonal to `Ω₀` is at least `(g - ε) ‖ψ‖²`.
  have horth : ∀ ψ, ⟪Ω₀, ψ⟫_ℂ = 0 → (g - ε) * ‖ψ‖ ^ 2 ≤ re ⟪ψ, B ψ⟫_ℂ := by
    intro ψ hψ
    set α := ⟪Ω, ψ⟫_ℂ
    set β := ⟪Ω, Ω₀⟫_ℂ
    have hβ : 1 / 2 ≤ ‖β‖ ^ 2 := by
      have : g * (1 - ‖β‖ ^ 2) ≤ g / 2 := hover.trans (by linarith)
      by_contra hlt
      push Not at hlt
      nlinarith
    set φ := (-α) • Ω₀ + β • ψ with hφ
    have hw : ⟪Ω₀, β • ψ⟫_ℂ = 0 := by rw [inner_smul_right, hψ, mul_zero]
    have hφΩ : ⟪Ω, φ⟫_ℂ = 0 := by
      rw [hφ, inner_add_right, inner_smul_right, inner_smul_right]; ring
    have hφn : ‖φ‖ ^ 2 = ‖α‖ ^ 2 + ‖β‖ ^ 2 * ‖ψ‖ ^ 2 := by
      have hi : ⟪(-α) • Ω₀, β • ψ⟫_ℂ = 0 := by
        rw [inner_smul_left, hw, mul_zero]
      rw [hφ, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi, norm_smul,
        norm_smul,
        hΩ₀, norm_neg]
      ring
    have hφB : re ⟪φ, B φ⟫_ℂ = ‖α‖ ^ 2 * e + ‖β‖ ^ 2 * re ⟪ψ, B ψ⟫_ℂ := by
      rw [hφ, re_inner_smul_add_eigenvector hB hΩ₀ heig hw, norm_neg, map_smul,
        inner_smul_left, inner_smul_right, ← mul_assoc, mul_comm _ β, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      push_cast
      rw [← ofReal_pow, re_ofReal_mul]
    have h1 := hA φ
    rw [hφΩ, norm_zero] at h1
    have h2 := hlow φ
    have hαe : ‖α‖ ^ 2 * e ≤ ‖α‖ ^ 2 * (g - ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hkey : ‖β‖ ^ 2 * ((g - ε) * ‖ψ‖ ^ 2) ≤ ‖β‖ ^ 2 * re ⟪ψ, B ψ⟫_ℂ := by
      nlinarith
    exact le_of_mul_le_mul_left hkey (by linarith)
  refine ⟨e, Ω₀, hΩ₀, heig, he0, heε, fun ψ => ?_, hover⟩
  -- Split `ψ` along `Ω₀`.
  set a := ⟪Ω₀, ψ⟫_ℂ
  set w := ψ - a • Ω₀ with hwdef
  have hΩΩ : ⟪Ω₀, Ω₀⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hΩ₀]; simp
  have hw : ⟪Ω₀, w⟫_ℂ = 0 := by
    rw [hwdef, inner_sub_right, inner_smul_right, hΩΩ, mul_one, sub_self]
  have hψ : ψ = a • Ω₀ + w := by rw [hwdef]; abel
  have hq : re ⟪ψ, B ψ⟫_ℂ = ‖a‖ ^ 2 * e + re ⟪w, B w⟫_ℂ := by
    conv_lhs => rw [hψ]
    exact re_inner_smul_add_eigenvector hB hΩ₀ heig hw a
  have hn : ‖ψ‖ ^ 2 = ‖a‖ ^ 2 + ‖w‖ ^ 2 := by
    have hi : ⟪a • Ω₀, w⟫_ℂ = 0 := by rw [inner_smul_left, hw, mul_zero]
    conv_lhs => rw [hψ]
    rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi, norm_smul, hΩ₀]
    ring
  have hwB := horth w hw
  rw [hq, hn]
  nlinarith [sq_nonneg ‖w‖]

end Core

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Truncation perturbation, spectral part** (Proposition 4.5, `prop:truncation`,
`03-quasilocal.tex`, lines 487–505). Let `H_F ≥ g (I - |Ω⟩⟨Ω|)` with `H_F Ω = 0`,
`‖Ω‖ = 1`, `g > 0`, and let `H' ≥ 0` with `‖H' - H_F‖ ≤ ε ≤ g / 4`. Then `H'` has a unit
ground vector `Ω₀` with ground energy `e₀ ∈ [0, ε]` and the gap inequality
`H' - e₀ I ≥ (g / 2) (I - |Ω₀⟩⟨Ω₀|)` (so `Ω₀` is unique and the gap is at least `g / 2`);
after a choice of phase `‖Ω₀ - e^{iθ} Ω‖ ≤ 2 √(ε / g)`, and the trace distance of the two
pure states is at most `√(2 ε / g)` (`eq:quasilocal-ground-distance`). -/
theorem exists_posSemidef_gap_of_norm_sub_le {HF Ht : Matrix n n ℂ}
    {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1) {g ε : ℝ} (hg : 0 < g) (hε : ε ≤ g / 4)
    (hgap : (HF - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hHFΩ : HF *ᵥ WithLp.ofLp Ω = 0) (hHt : Ht.PosSemidef) (hdiff : ‖Ht - HF‖ ≤ ε) :
    ∃ (e : ℝ) (Ω₀ : EuclideanSpace ℂ n), ‖Ω₀‖ = 1 ∧
      Ht *ᵥ WithLp.ofLp Ω₀ = (e : ℂ) • WithLp.ofLp Ω₀ ∧ 0 ≤ e ∧ e ≤ ε ∧
      (Ht - (e : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)))).PosSemidef ∧
      (∃ θ : ℝ, ‖Ω₀ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
      traceDistance (vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)))
          (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ Real.sqrt (2 * ε / g) := by
  set A := toEuclideanCLM (𝕜 := ℂ) (n := n) HF
  set B := toEuclideanCLM (𝕜 := ℂ) (n := n) Ht
  have hAapp : ∀ ψ, A ψ = toEuclideanLin HF ψ := fun ψ => rfl
  have hBapp : ∀ ψ, B ψ = toEuclideanLin Ht ψ := fun ψ => rfl
  have hBsym : (B : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr hHt.isHermitian
  have hgap' : (HF - ((0 : ℝ) : ℂ) • 1 - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
    simpa using hgap
  have hA : ∀ ψ, g * (‖ψ‖ ^ 2 - ‖⟪Ω, ψ⟫_ℂ‖ ^ 2) ≤ re ⟪ψ, A ψ⟫_ℂ := by
    intro ψ; simpa [hAapp] using hgap'.gap_le ψ
  have hAΩ : re ⟪Ω, A Ω⟫_ℂ = 0 := by
    have : A Ω = 0 := by
      rw [hAapp]
      change WithLp.toLp 2 (HF *ᵥ WithLp.ofLp Ω) = 0
      rw [hHFΩ]; rfl
    rw [this, inner_zero_right, zero_re]
  have hBnn : ∀ ψ, 0 ≤ re ⟪ψ, B ψ⟫_ℂ := by
    intro ψ
    have h := (isPositive_toEuclideanLin_iff.mpr hHt).re_inner_nonneg_right ψ
    rw [RCLike.re_to_complex] at h
    rwa [hBapp]
  have hAB : ‖B - A‖ ≤ ε := by
    have : B - A = toEuclideanCLM (𝕜 := ℂ) (n := n) (Ht - HF) := by
      rw [map_sub]
    rw [this]
    exact hdiff
  obtain ⟨e, Ω₀, hΩ₀, heig, he0, heε, hgapB, hover⟩ :=
    exists_gap_of_norm_sub_le hBsym hΩ hg hε hA hAΩ hBnn hAB
  have hε0 : 0 ≤ ε := he0.trans heε
  refine ⟨e, Ω₀, hΩ₀, ?_, he0, heε, ?_, ?_, ?_⟩
  · have := congrArg WithLp.ofLp heig
    simpa [hBapp] using this
  · refine (hHt.isHermitian.posSemidef_gap_iff e (g / 2) Ω₀).mpr fun ψ => ?_
    simpa [hBapp] using hgapB ψ
  · obtain ⟨θ, -, hθ⟩ := exists_isMinOn_sq_norm_sub_exp_smul_le_of_gap hg hΩ₀ hΩ
      (ε := 2 * ε) hover
    refine ⟨θ, ?_⟩
    have h4 : 2 * (2 * ε) / g = (2 * Real.sqrt (ε / g)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hε0 hg.le)]; ring
    rw [h4] at hθ
    exact abs_le_of_sq_le_sq' hθ (by positivity) |>.2 |>.trans_eq' (by simp)
  · rw [traceDistance_vecMulVec_eq hΩ₀ hΩ]
    refine Real.sqrt_le_sqrt ?_
    rw [norm_inner_symm, le_div_iff₀ hg]
    linarith

end Matrix
