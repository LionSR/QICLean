/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GlobalGap
import QICLean.Analysis.KyFanNorm

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
`algo53.tex`, lines 497–502, there with `e = 7√c_ε` and threshold `E₀ + 14√c_ε`. -/
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

end Matrix
