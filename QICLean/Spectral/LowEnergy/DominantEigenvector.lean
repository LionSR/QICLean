/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Eigenvalue.GlobalGap
import QICLean.Spectral.Eigenvalue.KyFanNorm
import QICLean.Spectral.Eigenvalue.DominantEigenvectorUniqueness
import QICLean.Analysis.Projection.DetectabilityLemma

/-!
# A dominant low-energy eigenvector of a low-energy density matrix

Let `H` have a unique ground vector `Ω` with energy `E₀` and gap `Δ > 0`, in the operator form
`H - E₀ ≥ Δ (1 - |Ω⟩⟨Ω|)`, and let `σ` be a density matrix with energy `tr(σ H) ≤ E₀ + e`.
If `4e < Δ`, then `σ` has an eigenvalue larger than `1/2` whose unit eigenvector `v` has
energy at most `E₀ + 2e` and overlap `|⟨Ω, v⟩| ≥ 1 - 2e/Δ`.

Write `σ = ∑ₖ λₖ |vₖ⟩⟨vₖ|`. The eigenvectors of energy above `E₀ + 2e` carry weight less than
`1/2` (Markov's inequality); each eigenvector of energy at most `E₀ + 2e` has squared overlap
with `Ω` larger than `1/2`, so there is at most one of them, and its eigenvalue exceeds `1/2`.
This is the eigenvector argument in the proof of Lemma `l:leading` of Landau, Vazirani and
Vidick.

## Main results

* `Matrix.IsHermitian.re_trace_mul_eq_sum_eigenvalues_mul`: `Re tr(σ H)` is the sum of the
  eigenvalues of `σ` times the energies of its eigenvectors.
* `Matrix.PosSemidef.exists_eigenvector_of_re_trace_mul_le`: the dominant eigenvector.
* `Matrix.PosSemidef.one_sub_energyExcess_div_gap_le_maxEigenvalue`,
  `Matrix.PosSemidef.twentyThree_div_twentyFour_le_maxEigenvalue`: the largest eigenvalue is at
  least `1 - e/Δ`, and at least `23 / 24` at energy excess `Δ / 24`.
* `Matrix.PosSemidef.norm_orthogonal_component_le_leading_residual`,
  `Matrix.PosSemidef.exists_nearby_unit_eigenvector_of_residual_le`: residual certificates for
  the leading eigenvector.

The largest-eigenvalue and residual statements are moved from TNLean,
`TNLean/MPS/AreaLaw/GroundStateAlgorithm/BoundaryState/ViableLeadingBounds.lean` and
`TNLean/MPS/AreaLaw/GroundStateAlgorithm/BoundaryState/LeadingResidual.lean` at commit
`6a5afb57c2`, with no change to the statements.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of
  1D gapped local Hamiltonians*, arXiv:1307.5143v1, `algo53.tex`, proof of Lemma `l:leading`,
  lines 497–502.
-/

open scoped Matrix ComplexOrder InnerProductSpace

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real energy `Re tr(σ H)` of a Hermitian `σ` is `∑ₖ λₖ Re ⟨vₖ, H vₖ⟩` over its
eigenvalues `λₖ` and orthonormal eigenvectors `vₖ`. -/
theorem IsHermitian.re_trace_mul_eq_sum_eigenvalues_mul {σ : Matrix n n ℂ}
    (hσ : σ.IsHermitian) (H : Matrix n n ℂ) :
    (σ * H).trace.re = ∑ k, hσ.eigenvalues k *
      (⟪hσ.eigenvectorBasis k, toEuclideanLin H (hσ.eigenvectorBasis k)⟫_ℂ).re := by
  rw [trace_mul_comm, hσ.trace_mul_re_eq_sum_eigenbasis]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_comm]
  congr 2
  simp only [EuclideanSpace.inner_eq_star_dotProduct, mul_apply, star_apply,
    IsHermitian.eigenvectorUnitary_apply, toLpLin_apply, mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
    simp only [Pi.star_apply]; ring

variable {σ H : Matrix n n ℂ} {E₀ Δ e : ℝ} {Ω : EuclideanSpace ℂ n}

/-- **A dominant low-energy eigenvector.** Let `H - E₀ ≥ Δ (1 - |Ω⟩⟨Ω|)` with `Δ > 0` and
`‖Ω‖ = 1`, and let `σ` be positive semidefinite with `tr σ = 1` and `Re tr(σ H) ≤ E₀ + e`,
where `4e < Δ`. Then `σ` has a unit eigenvector `v` with eigenvalue larger than `1/2`, energy
`Re ⟨v, H v⟩ ≤ E₀ + 2e` and overlap `|⟨Ω, v⟩| ≥ 1 - 2e/Δ`.

This is the eigenvector argument of the proof of Lemma `l:leading` of arXiv:1307.5143v1,
`algo53.tex`, lines 497–502, where the threshold is twice the energy excess of the glued
state. -/
theorem PosSemidef.exists_eigenvector_of_re_trace_mul_le (hσ : σ.PosSemidef)
    (htr : σ.trace = 1)
    (hgap : (H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΩ : ‖Ω‖ = 1) (hΔ : 0 < Δ) (he : (σ * H).trace.re ≤ E₀ + e) (h4 : 4 * e < Δ) :
    ∃ (v : EuclideanSpace ℂ n) (μ : ℝ), ‖v‖ = 1 ∧ toEuclideanLin σ v = (μ : ℂ) • v ∧
      1 / 2 < μ ∧ (⟪v, toEuclideanLin H v⟫_ℂ).re ≤ E₀ + 2 * e ∧
      1 - 2 * e / Δ ≤ ‖⟪Ω, v⟫_ℂ‖ := by
  classical
  set hS := hσ.isHermitian
  set v := hS.eigenvectorBasis
  set lam := hS.eigenvalues
  set E : n → ℝ := fun k ↦ (⟪v k, toEuclideanLin H (v k)⟫_ℂ).re with hE
  have hv1 (k : n) : ‖v k‖ = 1 := v.orthonormal.1 k
  have hlam0 (k : n) : 0 ≤ lam k := hσ.eigenvalues_nonneg k
  have hlam1 : ∑ k, lam k = 1 := by
    have h := congrArg Complex.re hS.trace_eq_sum_eigenvalues
    rw [htr, Complex.re_sum] at h
    simpa [lam] using h.symm
  -- The gap at each eigenvector.
  have hgapk (k : n) : Δ * (1 - ‖⟪Ω, v k⟫_ℂ‖ ^ 2) ≤ E k - E₀ := by
    have h := hgap.gap_le (v k)
    rw [hv1, one_pow, mul_one] at h
    exact h
  have hov1 (k : n) : ‖⟪Ω, v k⟫_ℂ‖ ≤ 1 :=
    (norm_inner_le_norm _ _).trans (by rw [hΩ, hv1, one_mul])
  have hEk (k : n) : E₀ ≤ E k := by
    have h1 : 0 ≤ 1 - ‖⟪Ω, v k⟫_ℂ‖ ^ 2 := by nlinarith [norm_nonneg ⟪Ω, v k⟫_ℂ, hov1 k]
    linarith [hgapk k, mul_nonneg hΔ.le h1]
  have hsum : ∑ k, lam k * (E k - E₀) ≤ e := by
    have h : (σ * H).trace.re = ∑ k, lam k * E k := hS.re_trace_mul_eq_sum_eigenvalues_mul H
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hlam1, one_mul]
    linarith
  have he0 : 0 ≤ e := hsum.trans' (Finset.sum_nonneg fun k _ ↦
    mul_nonneg (hlam0 k) (sub_nonneg.mpr (hEk k)))
  -- The low-energy eigenvectors.
  set J := Finset.univ.filter fun k ↦ E k ≤ E₀ + 2 * e
  have hJov (k : n) (hk : k ∈ J) : 1 / 2 < ‖⟪Ω, v k⟫_ℂ‖ ^ 2 := by
    have hk' : E k ≤ E₀ + 2 * e := (Finset.mem_filter.mp hk).2
    have := hgapk k
    have : Δ * (1 - ‖⟪Ω, v k⟫_ℂ‖ ^ 2) ≤ 2 * e := by linarith
    nlinarith
  -- Markov: the weight outside `J` is less than `1/2`.
  have hout : ∑ k ∈ Finset.univ.filter (fun k ↦ ¬ E k ≤ E₀ + 2 * e), lam k < 1 / 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    set O := Finset.univ.filter fun k ↦ ¬ E k ≤ E₀ + 2 * e
    have hpos : 0 < ∑ k ∈ O, lam k := by linarith
    obtain ⟨k₀, hk₀, hlk₀⟩ : ∃ k ∈ O, 0 < lam k := by
      by_contra hno
      push Not at hno
      exact (Finset.sum_nonpos hno).not_gt hpos
    have hstrict : 2 * e * ∑ k ∈ O, lam k < ∑ k ∈ O, lam k * (E k - E₀) := by
      rw [Finset.mul_sum]
      refine Finset.sum_lt_sum (fun k hk ↦ ?_) ⟨k₀, hk₀, ?_⟩
      · have : E₀ + 2 * e < E k := not_le.mp (Finset.mem_filter.mp hk).2
        nlinarith [hlam0 k]
      · have : E₀ + 2 * e < E k₀ := not_le.mp (Finset.mem_filter.mp hk₀).2
        nlinarith
    have hsub : ∑ k ∈ O, lam k * (E k - E₀) ≤ ∑ k, lam k * (E k - E₀) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ ↦
        mul_nonneg (hlam0 k) (sub_nonneg.mpr (hEk k))
    nlinarith
  have hin : 1 / 2 < ∑ k ∈ J, lam k := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k ↦ E k ≤ E₀ + 2 * e) lam
    rw [hlam1] at h
    change ∑ k ∈ J, lam k + ∑ k ∈ Finset.univ.filter (fun k ↦ ¬ E k ≤ E₀ + 2 * e), lam k = 1
      at h
    linarith
  -- At most one low-energy eigenvector: their squared overlaps with `Ω` sum to at most `1`.
  obtain ⟨k₀, hk₀⟩ : J.Nonempty :=
    Finset.nonempty_of_sum_ne_zero (lt_trans (by norm_num) hin).ne'
  have hJ : J = {k₀} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hk₀, fun k hk ↦ ?_⟩
    by_contra hne
    have hpar := v.sum_sq_norm_inner_right Ω
    rw [hΩ, one_pow] at hpar
    have hpair : ‖⟪v k, Ω⟫_ℂ‖ ^ 2 + ‖⟪v k₀, Ω⟫_ℂ‖ ^ 2 ≤ ∑ j, ‖⟪v j, Ω⟫_ℂ‖ ^ 2 := by
      rw [← Finset.sum_pair (f := fun j ↦ ‖⟪v j, Ω⟫_ℂ‖ ^ 2) hne]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ ↦ sq_nonneg _
    rw [norm_inner_symm (v k), norm_inner_symm (v k₀)] at hpair
    linarith [hJov k hk, hJov k₀ hk₀]
  have hk₀E : E k₀ ≤ E₀ + 2 * e := (Finset.mem_filter.mp hk₀).2
  refine ⟨v k₀, lam k₀, hv1 k₀, ?_, ?_, hk₀E, ?_⟩
  · rw [← (WithLp.ofLp_injective 2).eq_iff]
    simp only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul]
    rw [hS.mulVec_eigenvectorBasis k₀, ← Complex.coe_smul]
  · rwa [hJ, Finset.sum_singleton] at hin
  · have hg := hgapk k₀
    have hov := hov1 k₀
    have hsq : 1 - 2 * e / Δ ≤ ‖⟪Ω, v k₀⟫_ℂ‖ ^ 2 := by
      have h2 : 1 - ‖⟪Ω, v k₀⟫_ℂ‖ ^ 2 ≤ 2 * e / Δ := by
        rw [le_div_iff₀ hΔ]; nlinarith
      linarith
    nlinarith [norm_nonneg ⟪Ω, v k₀⟫_ℂ]

/-! ### The largest eigenvalue and residual certificates

The largest eigenvalue of a low-energy density matrix is at least its ground-state population,
and at the LVV energy scale it is at least `23 / 24`. A unit eigenvector `u` with eigenvalue
`μ > 1/2` is then certified by the residual of any unit vector `z`: the orthogonal component of
`z` is at most `‖σ z - μ z‖ / (2μ - 1)`, and `z` is close to a phase of `u`. Landau, Vazirani
and Vidick, arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`, lines 493–505. -/

/-- The largest eigenvalue of a low-energy density matrix is at least its ground-state
population.  Under a gap `Δ`, an energy excess `e` therefore gives the quantitative
bound `1 - e / Δ ≤ μ`.  This is the spectral separation estimate implicit in the
leading-vector step of LVV13, `algo53.tex`, lines 497--502. -/
theorem PosSemidef.one_sub_energyExcess_div_gap_le_maxEigenvalue
    {σ H : Matrix n n ℂ} {E₀ Δ e μ : ℝ} {Ω : EuclideanSpace ℂ n}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (hgap : (H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΩ : ‖Ω‖ = 1) (hΔ : 0 < Δ) (henergy : (σ * H).trace.re ≤ E₀ + e)
    (hmax : ∀ (ν : ℝ) (z : EuclideanSpace ℂ n), z ≠ 0 →
      σ *ᵥ WithLp.ofLp z = (ν : ℂ) • WithLp.ofLp z → ν ≤ μ) :
    1 - e / Δ ≤ μ := by
  classical
  let hS := hσ.isHermitian
  let b := hS.eigenvectorBasis
  let lam := hS.eigenvalues
  let E : n → ℝ := fun i ↦ (⟪b i, toEuclideanLin H (b i)⟫_ℂ).re
  have hb1 (i : n) : ‖b i‖ = 1 := b.orthonormal.1 i
  have hlam0 (i : n) : 0 ≤ lam i := hσ.eigenvalues_nonneg i
  have hlam1 : ∑ i, lam i = 1 := by
    have hh := congrArg Complex.re hS.trace_eq_sum_eigenvalues
    rw [htr, Complex.re_sum] at hh
    simpa [lam] using hh.symm
  have hgap_i (i : n) :
      Δ * (1 - ‖⟪Ω, b i⟫_ℂ‖ ^ 2) ≤ E i - E₀ := by
    have hh := hgap.gap_le (b i)
    rw [hb1, one_pow, mul_one] at hh
    exact hh
  have hsum : ∑ i, lam i * (E i - E₀) ≤ e := by
    have hh : (σ * H).trace.re = ∑ i, lam i * E i :=
      hS.re_trace_mul_eq_sum_eigenvalues_mul H
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hlam1, one_mul]
    linarith
  have hweighted :
      Δ * ∑ i, lam i * (1 - ‖⟪Ω, b i⟫_ℂ‖ ^ 2) ≤ e := by
    calc
      _ = ∑ i, lam i * (Δ * (1 - ‖⟪Ω, b i⟫_ℂ‖ ^ 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, lam i * (E i - E₀) := Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_left (hgap_i i) (hlam0 i)
      _ ≤ e := hsum
  have hpopulation : 1 - e / Δ ≤ ∑ i, lam i * ‖⟪Ω, b i⟫_ℂ‖ ^ 2 := by
    have hid : ∑ i, lam i * (1 - ‖⟪Ω, b i⟫_ℂ‖ ^ 2) =
        1 - ∑ i, lam i * ‖⟪Ω, b i⟫_ℂ‖ ^ 2 := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hlam1]
    rw [hid] at hweighted
    field_simp [ne_of_gt hΔ]
    nlinarith only [hweighted]
  have hlamμ (i : n) : lam i ≤ μ := by
    apply hmax (lam i) (b i) (by
      intro hz
      have hi := hb1 i
      rw [hz, norm_zero] at hi
      norm_num at hi)
    exact hS.mulVec_eigenvectorBasis i
  have hparseval : ∑ i, ‖⟪Ω, b i⟫_ℂ‖ ^ 2 = 1 := by
    have hh := b.sum_sq_norm_inner_right Ω
    rw [hΩ, one_pow] at hh
    simpa only [norm_inner_symm] using hh
  calc
    1 - e / Δ ≤ ∑ i, lam i * ‖⟪Ω, b i⟫_ℂ‖ ^ 2 := hpopulation
    _ ≤ ∑ i, μ * ‖⟪Ω, b i⟫_ℂ‖ ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hlamμ i) (sq_nonneg _)
    _ = μ := by rw [← Finset.mul_sum, hparseval, mul_one]

/-- At the LVV leading-vector energy scale, the maximal density eigenvalue is uniformly
bounded away from one half: energy excess at most `Δ / 24` gives `23 / 24 ≤ μ`.
This is the quantitative conditioning needed for a numerical leading-eigenvector solve. -/
theorem PosSemidef.twentyThree_div_twentyFour_le_maxEigenvalue
    {σ H : Matrix n n ℂ} {E₀ Δ μ : ℝ} {Ω : EuclideanSpace ℂ n}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (hgap : (H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΩ : ‖Ω‖ = 1) (hΔ : 0 < Δ) (henergy : (σ * H).trace.re ≤ E₀ + Δ / 24)
    (hmax : ∀ (ν : ℝ) (z : EuclideanSpace ℂ n), z ≠ 0 →
      σ *ᵥ WithLp.ofLp z = (ν : ℂ) • WithLp.ofLp z → ν ≤ μ) :
    23 / 24 ≤ μ := by
  have hh := PosSemidef.one_sub_energyExcess_div_gap_le_maxEigenvalue
    hσ htr hgap hΩ hΔ henergy hmax
  have heq : 1 - (Δ / 24) / Δ = (23 : ℝ) / 24 := by
    field_simp [ne_of_gt hΔ]
    ring
  rwa [heq] at hh

/-- The uniform bound `23 / 24 ≤ μ` leaves a spectral separation of at least
`11 / 12` between `μ` and the interval `[0, 1 - μ]`.  Consequently division by
this separation costs at most the factor `12 / 11`. -/
private theorem leading_residual_div_separation_le
    {r μ : ℝ} (hr : 0 ≤ r) (hμ : 23 / 24 ≤ μ) :
    r / (2 * μ - 1) ≤ (12 / 11) * r := by
  have hsep : (11 : ℝ) / 12 ≤ 2 * μ - 1 := by linarith only [hμ]
  have hpos : 0 < 2 * μ - 1 := lt_of_lt_of_le (by norm_num) hsep
  apply (div_le_iff₀ hpos).2
  nlinarith only [hr, hsep]

/-- The shifted positive operator `μ I - σ` has gap `2μ - 1` above its kernel on the
orthogonal complement of a unit `μ`-eigenvector of the trace-one density matrix `σ`.
Consequently its residual controls the orthogonal component of any vector. -/
theorem PosSemidef.norm_orthogonal_component_le_shifted_residual
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 1 / 2 < μ) (z : EuclideanSpace ℂ n) :
    let K := toEuclideanLin (((μ : ℂ) • (1 : Matrix n n ℂ)) - σ)
    ‖z - ⟪u, z⟫_ℂ • u‖ ≤ ‖K z‖ / (2 * μ - 1) := by
  let K := toEuclideanLin (((μ : ℂ) • (1 : Matrix n n ℂ)) - σ)
  have hone : (((μ : ℂ) • (1 : Matrix n n ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  have hK : K.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr
    (hone.sub hσ.isHermitian)
  have huL : toEuclideanLin σ u = (μ : ℂ) • u := by
    apply WithLp.ofLp_injective 2
    simpa only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using huσ
  have heig : K u = (0 : ℂ) • u := by
    have h1 : toEuclideanLin (1 : Matrix n n ℂ) u = u := by simp [toLpLin_one]
    dsimp only [K]
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, h1, huL,
      sub_self, zero_smul]
  have hsep : (0 : ℝ) < 2 * μ - 1 := by linarith only [hμ]
  have horth : ∀ w : EuclideanSpace ℂ n, ⟪u, w⟫_ℂ = 0 →
      (2 * μ - 1) * ‖w‖ ^ 2 ≤ (⟪w, K w⟫_ℂ).re := by
    intro w hw
    have hh := PosSemidef.re_inner_le_one_sub_eigenvalue_of_orthogonal
      hσ htr hu huσ hμ hw
    have h1 : toEuclideanLin (1 : Matrix n n ℂ) w = w := by simp [toLpLin_one]
    have hscalar : (⟪w, (μ : ℂ) • w⟫_ℂ).re = μ * ‖w‖ ^ 2 := by
      rw [inner_smul_right, Complex.re_ofReal_mul,
        show (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) w]
    dsimp only [K]
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, h1, inner_sub_right,
      Complex.sub_re, hscalar]
    linarith
  let P : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
    1 - InnerProductSpace.rankOne ℂ u u
  have hP : IsStarProjection P :=
    (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hu).one_sub
  have hPapply (x : EuclideanSpace ℂ n) : P x = x - ⟪u, x⟫_ℂ • u := rfl
  have hself : ⟪u, u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    simp
  have hinner (x : EuclideanSpace ℂ n) : ⟪u, K x⟫_ℂ = 0 := by
    have hsym := hK u x
    rw [heig, zero_smul, inner_zero_left] at hsym
    exact hsym.symm
  have hcomm (x : EuclideanSpace ℂ n) : K (P x) = P (K x) := by
    simp only [hPapply, map_sub, map_smul, heig, zero_smul, smul_zero, sub_zero,
      hinner]
  let w := P z
  have hw : ⟪u, w⟫_ℂ = 0 := by
    rw [show w = P z from rfl, hPapply, inner_sub_right, inner_smul_right,
      hself, mul_one, sub_self]
  have hres : K w = P (K z) := by
    rw [show w = P z from rfl, hcomm]
  have hlow : (2 * μ - 1) * ‖w‖ ^ 2 ≤ (⟪w, K w⟫_ℂ).re := horth w hw
  have hupper : (⟪w, K w⟫_ℂ).re ≤ ‖w‖ * ‖K z‖ := by
    calc
      _ ≤ ‖w‖ * ‖K w‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        rw [hres]
        exact ContinuousLinearMap.IsStarProjection.norm_apply_le hP _) (norm_nonneg _)
  change ‖w‖ ≤ _
  by_cases hw0 : ‖w‖ = 0
  · rw [hw0]
    exact div_nonneg (norm_nonneg _) hsep.le
  apply (le_div_iff₀ hsep).mpr
  have hmul : ‖w‖ * ((2 * μ - 1) * ‖w‖) ≤ ‖w‖ * ‖K z‖ := by
    nlinarith
  have hh := le_of_mul_le_mul_left hmul
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0))
  nlinarith

/-- The shifted residual is the usual eigenpair residual, up to a harmless sign. -/
theorem PosSemidef.norm_orthogonal_component_le_leading_residual
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 1 / 2 < μ) (z : EuclideanSpace ℂ n) :
    ‖z - ⟪u, z⟫_ℂ • u‖ ≤
      ‖toEuclideanLin σ z - (μ : ℂ) • z‖ / (2 * μ - 1) := by
  have hh := PosSemidef.norm_orthogonal_component_le_shifted_residual
    hσ htr hu huσ hμ z
  change ‖z - ⟪u, z⟫_ℂ • u‖ ≤
    ‖toEuclideanLin (((μ : ℂ) • (1 : Matrix n n ℂ)) - σ) z‖ / (2 * μ - 1) at hh
  have h1 : toEuclideanLin (1 : Matrix n n ℂ) z = z := by simp [toLpLin_one]
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, h1,
    show (μ : ℂ) • z - toEuclideanLin σ z =
      -(toEuclideanLin σ z - (μ : ℂ) • z) by abel, norm_neg] at hh
  exact hh

/-- For a unit numerical vector, the eigenpair residual gives a phase-aligned squared
distance to the exact leading vector. -/
theorem PosSemidef.exists_phase_sq_distance_le_leading_residual
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u z : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 1 / 2 < μ) :
    ∃ θ : ℝ, ‖z - Complex.exp (θ * Complex.I) • u‖ ^ 2 ≤
      2 * (‖toEuclideanLin σ z - (μ : ℂ) • z‖ / (2 * μ - 1)) ^ 2 := by
  let P : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
    1 - InnerProductSpace.rankOne ℂ u u
  have hP : IsStarProjection P :=
    (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hu).one_sub
  have hPapply (x : EuclideanSpace ℂ n) : P x = x - ⟪u, x⟫_ℂ • u := rfl
  have hnorm : ‖P z‖ ≤
      ‖toEuclideanLin σ z - (μ : ℂ) • z‖ / (2 * μ - 1) := by
    rw [hPapply]
    exact PosSemidef.norm_orthogonal_component_le_leading_residual
      hσ htr hu huσ hμ z
  have hdeficit : 1 - ‖⟪u, z⟫_ℂ‖ ^ 2 = ‖P z‖ ^ 2 := by
    have hh := ContinuousLinearMap.IsStarProjection.norm_sq_eq
      (InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hu) z
    simp only [hz, one_pow, InnerProductSpace.rankOne_apply, norm_smul, hu, mul_one] at hh
    change 1 = ‖⟪u, z⟫_ℂ‖ ^ 2 + ‖P z‖ ^ 2 at hh
    linarith
  have hbound : 1 * (1 - ‖⟪u, z⟫_ℂ‖ ^ 2) ≤
      (‖toEuclideanLin σ z - (μ : ℂ) • z‖ / (2 * μ - 1)) ^ 2 := by
    rw [one_mul, hdeficit]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  obtain ⟨θ, _, hθ⟩ := exists_isMinOn_sq_norm_sub_exp_smul_le_of_gap
    (by norm_num : (0 : ℝ) < 1) hz hu hbound
  exact ⟨θ, by simpa only [div_one] using hθ⟩

/-- At the LVV scale `μ ≥ 23 / 24`, the residual-to-distance estimate has the
uniform conditioning factor `12 / 11`. -/
theorem PosSemidef.exists_phase_sq_distance_le_twelve_div_eleven_residual
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u z : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) :
    ∃ θ : ℝ, ‖z - Complex.exp (θ * Complex.I) • u‖ ^ 2 ≤
      2 * ((12 / 11) * ‖toEuclideanLin σ z - (μ : ℂ) • z‖) ^ 2 := by
  have hhalf : 1 / 2 < μ := by linarith only [hμ]
  obtain ⟨θ, hθ⟩ := PosSemidef.exists_phase_sq_distance_le_leading_residual
    hσ htr hu hz huσ hhalf
  refine ⟨θ, hθ.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (by linarith only [hhalf]))
  exact leading_residual_div_separation_le (norm_nonneg _) hμ

/-- A residual at most `11 / 24` times a target vector tolerance suffices for that
phase-aligned tolerance.  The factor is a convenient rational consequence of the
uniform `12 / 11` conditioning and the squared-distance estimate. -/
theorem PosSemidef.exists_phase_distance_le_of_residual_le
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u z : EuclideanSpace ℂ n} {μ ζ : ℝ} (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) (hζ : 0 ≤ ζ)
    (hres : ‖toEuclideanLin σ z - (μ : ℂ) • z‖ ≤ (11 / 24) * ζ) :
    ∃ θ : ℝ, ‖z - Complex.exp (θ * Complex.I) • u‖ ≤ ζ := by
  obtain ⟨θ, hθ⟩ :=
    PosSemidef.exists_phase_sq_distance_le_twelve_div_eleven_residual
      hσ htr hu hz huσ hμ
  refine ⟨θ, ?_⟩
  have hscaled : (12 / 11) * ‖toEuclideanLin σ z - (μ : ℂ) • z‖ ≤ ζ / 2 := by
    nlinarith only [hres]
  have hsq : ‖z - Complex.exp (θ * Complex.I) • u‖ ^ 2 ≤ ζ ^ 2 := by
    calc
      _ ≤ 2 * ((12 / 11) * ‖toEuclideanLin σ z - (μ : ℂ) • z‖) ^ 2 := hθ
      _ ≤ 2 * (ζ / 2) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (by norm_num) (norm_nonneg _)) hscaled 2) (by norm_num)
      _ ≤ ζ ^ 2 := by nlinarith only [sq_nonneg ζ]
  nlinarith only [hsq, hζ, norm_nonneg (z - Complex.exp (θ * Complex.I) • u),
    sq_nonneg (‖z - Complex.exp (θ * Complex.I) • u‖ - ζ)]

/-- A sufficiently accurate residual certificate produces an exact unit leading
eigenvector within the prescribed tolerance.  The exact vector differs from the
chosen leading eigenvector only by a complex phase. -/
theorem PosSemidef.exists_nearby_unit_eigenvector_of_residual_le
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u z : EuclideanSpace ℂ n} {μ ζ : ℝ} (hu : ‖u‖ = 1) (hz : ‖z‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 23 / 24 ≤ μ) (hζ : 0 ≤ ζ)
    (hres : ‖toEuclideanLin σ z - (μ : ℂ) • z‖ ≤ (11 / 24) * ζ) :
    ∃ v : EuclideanSpace ℂ n,
      ‖v‖ = 1 ∧
      σ *ᵥ WithLp.ofLp v = (μ : ℂ) • WithLp.ofLp v ∧
      ‖z - v‖ ≤ ζ ∧
      ∃ θ : ℝ, v = Complex.exp (θ * Complex.I) • u := by
  obtain ⟨θ, hθ⟩ := PosSemidef.exists_phase_distance_le_of_residual_le
    hσ htr hu hz huσ hμ hζ hres
  refine ⟨Complex.exp (θ * Complex.I) • u, ?_, ?_, hθ, θ, rfl⟩
  · rw [norm_smul, Complex.norm_exp, hu]
    norm_num
  · rw [WithLp.ofLp_smul, mulVec_smul, huσ]
    simp only [smul_smul, mul_comm]

end Matrix
