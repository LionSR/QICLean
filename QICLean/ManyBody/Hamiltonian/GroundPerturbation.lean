/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Perturbation.GapPerturbation
import QICLean.Analysis.Order.GlobalGap
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# Ground vectors of a perturbed gapped Hamiltonian

Let `H` be Hermitian with every eigenvalue equal to `E₀` or at least `E₀ + Δ`, and let a
Hermitian `M` satisfy `‖H - M‖ ≤ ε`. A unit vector `φ` minimizing the Rayleigh quotient of `M`
is an eigenvector of `M`, and its excess energy under `H` is at most `2ε`. The gap of `H` then
controls the projection of `φ` onto the ground space of `H`: the defect
`1 - ‖P φ‖²` is at most `2ε/Δ`, so `P φ ≠ 0` once `2ε < Δ`. For a unique unit ground vector `Ω`,
`1 - |⟨Ω, φ⟩|² ≤ 2ε/Δ` and the squared distance from `φ` to the best phase multiple of `Ω` is at
most `4ε/Δ`. If `ε = B e^{-βℓ}`, an explicit logarithmic radius `ℓ` makes the defect at most any
`η > 0`. Neither `M` nor `ε` is restricted: no positivity of `M` and no smallness of `ε` against
`Δ` is assumed.

`exists_gap_of_norm_sub_le` of `Analysis/GapPerturbation` assumes `M ≥ 0`, `ε ≤ Δ/4` and a
ground energy `0`, and concludes, in addition, a gap `Δ/2` above the ground vector of `M`; the
statements here keep only the overlap and need none of those hypotheses.

## Main results

* `ManyBody.groundSpace_gap_le_of_eigenvalues` — the quadratic form of the gap.
* `ManyBody.exists_groundVector_energy_le_of_norm_sub_le` — a ground vector of `M` of energy at
  most `E₀ + 2ε` under `H`.
* `ManyBody.exists_groundVector_projected_mass_of_norm_sub_le`,
  `ManyBody.exists_groundVector_overlap_of_norm_sub_le` — its projection onto the ground space.
* `ManyBody.exists_groundVector_projection_of_exp_norm_bound`,
  `ManyBody.exists_groundVector_overlap_of_exp_norm_bound` — at a logarithmic radius.

## References

Hastings, *Solving Gapped Hamiltonians Locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 359–367.

Moved from TNLean, `TNLean/Lattice/GaussianGroundStateOverlap.lean` at commit `e113e005`, with
no change to the statements.
-/

open Matrix Complex
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem unit_energy_error_le {H M : Matrix n n ℂ} {ε : ℝ}
    (hHM : ‖H - M‖ ≤ ε) {v : EuclideanSpace ℂ n} (hv : ‖v‖ = 1) :
    |(⟪v, toEuclideanLin H v⟫_ℂ).re - (⟪v, toEuclideanLin M v⟫_ℂ).re| ≤ ε := by
  have hq := ((toEuclideanCLM (𝕜 := ℂ) (n := n) (H - M)).rayleighQuotient_le_norm v).trans hHM
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    hv, one_pow, div_one] at hq
  change |(⟪toEuclideanLin (H - M) v, v⟫_ℂ).re| ≤ ε at hq
  rw [← inner_conj_symm (toEuclideanLin (H - M) v) v, Complex.conj_re] at hq
  simpa only [map_sub, LinearMap.sub_apply, inner_sub_right, Complex.sub_re] using hq

/-- The eigenvalue gap is the quadratic-form gap above the canonical ground eigenspace.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem groundSpace_gap_le_of_eigenvalues {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {E₀ Δ : ℝ} (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k)
    (ψ : EuclideanSpace ℂ n) :
    Δ * (‖ψ‖ ^ 2 - ‖(groundSpace H E₀).starProjection ψ‖ ^ 2) ≤
      (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2 := by
  let K := groundSpace H E₀
  let b := hH.eigenvectorBasis
  let y := ψ - K.starProjection ψ
  have hb (k : n) : H *ᵥ WithLp.ofLp (b k) = (hH.eigenvalues k : ℂ) • WithLp.ofLp (b k) :=
    (by rw [hH.mulVec_eigenvectorBasis, Complex.coe_smul])
  have hcoef (k : n) : ⟪b k, toEuclideanLin H ψ⟫_ℂ =
      (hH.eigenvalues k : ℂ) * ⟪b k, ψ⟫_ℂ := by
    have hs := isSymmetric_toEuclideanLin_iff.mpr hH
    have heig : toEuclideanLin H (b k) = (hH.eigenvalues k : ℂ) • b k := by
      exact (WithLp.ofLp_injective 2) (hb k)
    rw [← hs, heig, inner_smul_left, Complex.conj_ofReal]
  have henergy : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re =
      ∑ k, hH.eigenvalues k * ‖⟪b k, ψ⟫_ℂ‖ ^ 2 := by
    rw [← b.sum_inner_mul_inner ψ (toEuclideanLin H ψ)]
    change Complex.reAddGroupHom (∑ k, ⟪ψ, b k⟫_ℂ * ⟪b k, toEuclideanLin H ψ⟫_ℂ) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hcoef, ← inner_conj_symm ψ (b k)]
    have heq : (starRingEnd ℂ) ⟪b k, ψ⟫_ℂ *
        ((hH.eigenvalues k : ℂ) * ⟪b k, ψ⟫_ℂ) =
        ((hH.eigenvalues k * ‖⟪b k, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      calc _ = (hH.eigenvalues k : ℂ) *
          ((starRingEnd ℂ) ⟪b k, ψ⟫_ℂ * ⟪b k, ψ⟫_ℂ) := by ring
        _ = _ := by rw [Complex.conj_mul']; push_cast; rfl
    rw [heq]
    rfl
  have henergySub : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2 =
      ∑ k, (hH.eigenvalues k - E₀) * ‖⟪b k, ψ⟫_ℂ‖ ^ 2 := by
    rw [henergy, ← b.sum_sq_norm_inner_right ψ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hres : ‖ψ‖ ^ 2 - ‖K.starProjection ψ‖ ^ 2 = ‖y‖ ^ 2 := by
    have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection ψ K
    rw [K.starProjection_orthogonal_val ψ] at hp
    dsimp [y]
    linarith
  change Δ * (‖ψ‖ ^ 2 - ‖K.starProjection ψ‖ ^ 2) ≤ _
  rw [hres, ← b.sum_sq_norm_inner_right y, Finset.mul_sum, henergySub]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : hH.eigenvalues k = E₀
  · have hmem : b k ∈ K := eigenvectorBasis_mem_groundSpace hH hk
    have hzero : ⟪b k, y⟫_ℂ = 0 := by
      rw [inner_eq_zero_symm]
      exact K.starProjection_inner_eq_zero ψ (b k) hmem
    simp [hzero, hk]
  · have hzero : ⟪b k, K.starProjection ψ⟫_ℂ = 0 :=
      inner_eq_zero_of_mem_groundSpace hH hk (hb k) (K.starProjection_apply_mem ψ)
    have hge := (hgap k).resolve_left hk
    simp only [y, inner_sub_right, hzero, sub_zero]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- A unit eigenvector of a Hermitian approximation minimizes its quadratic form
and has excess original energy at most twice the operator-norm error.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_energy_le_of_norm_sub_le {H M : Matrix n n ℂ}
    {E₀ ε : ℝ} {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω = (E₀ : ℂ) • Ω)
    (hM : M.IsHermitian) (hHM : ‖H - M‖ ≤ ε) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      (⟪φ, toEuclideanLin H φ⟫_ℂ).re - E₀ ≤ 2 * ε := by
  have : Nontrivial (EuclideanSpace ℂ n) :=
    ⟨⟨Ω, 0, fun h ↦ by simp [h] at hΩ⟩⟩
  have hMsym : (toEuclideanCLM (𝕜 := ℂ) (n := n) M :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr hM
  obtain ⟨φ, hφ, heig, hmin⟩ := exists_unit_eigenvector_re_inner_le hMsym
  have hE₀ : (⟪Ω, toEuclideanLin H Ω⟫_ℂ).re = E₀ := by
    change (⟪Ω, toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω⟫_ℂ).re = E₀
    rw [hHΩ, inner_smul_right, inner_self_eq_norm_sq_to_K, hΩ]
    simp
  have hminΩ := hmin Ω
  have hdiffΩ := unit_energy_error_le hHM hΩ
  have hdiffφ := unit_energy_error_le hHM hφ
  have henergy : (⟪φ, toEuclideanLin H φ⟫_ℂ).re - E₀ ≤ 2 * ε := by
    rw [hΩ, one_pow, mul_one] at hminΩ
    change (⟪φ, toEuclideanLin M φ⟫_ℂ).re ≤
      (⟪Ω, toEuclideanLin M Ω⟫_ℂ).re at hminΩ
    linarith [(abs_le.mp hdiffΩ).1, (abs_le.mp hdiffφ).2]
  exact ⟨_, φ, hφ, heig, hmin, henergy⟩

/-- An actual ground vector of a Hermitian approximation has large overlap with the
unit vector spanning the ground space of a gapped Hermitian Hamiltonian.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_overlap_of_norm_sub_le {H M : Matrix n n ℂ}
    {E₀ Δ ε : ℝ} {Ω : EuclideanSpace ℂ n} (hH : H.IsHermitian) (hΩ : ‖Ω‖ = 1)
    (hgs : IsGapped H E₀ Δ) (hspan : groundSpace H E₀ = Submodule.span ℂ {Ω}) (hΔ : 0 < Δ)
    (hM : M.IsHermitian) (hHM : ‖H - M‖ ≤ ε) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      Δ * (1 - ‖⟪Ω, φ⟫_ℂ‖ ^ 2) ≤ 2 * ε ∧
      ∃ θ : ℝ, IsMinOn
        (fun α : ℝ ↦ ‖φ - Complex.exp (α * Complex.I) • Ω‖) Set.univ θ ∧
        ‖φ - Complex.exp (θ * Complex.I) • Ω‖ ^ 2 ≤ 4 * ε / Δ := by
  have hHΩ : toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω = (E₀ : ℂ) • Ω :=
    mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Ω)
  obtain ⟨e, φ, hφ, heig, hmin, henergy⟩ :=
    exists_groundVector_energy_le_of_norm_sub_le hΩ hHΩ hM hHM
  have hgap : Δ * (1 - ‖⟪Ω, φ⟫_ℂ‖ ^ 2) ≤ 2 * ε := by
    have hg := (hgs.posSemidef_sub_smul_one hH hΩ hspan).gap_le φ
    rw [hφ, one_pow, mul_one] at hg
    exact hg.trans henergy
  obtain ⟨θ, hminθ, hθ⟩ := exists_isMinOn_sq_norm_sub_exp_smul_le_of_gap hΔ hφ hΩ hgap
  refine ⟨_, φ, hφ, heig, hmin, hgap, θ, hminθ, ?_⟩
  simpa only [show (2 : ℝ) * (2 * ε) = 4 * ε by ring] using hθ

/-- The same energy comparison controls mass outside the canonical ground eigenspace,
without a simplicity assumption on the original ground energy.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_projected_mass_of_norm_sub_le {H M : Matrix n n ℂ}
    {E₀ Δ ε : ℝ} {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω = (E₀ : ℂ) • Ω)
    (hgap : ∀ ψ : EuclideanSpace ℂ n,
      Δ * (‖ψ‖ ^ 2 - ‖(groundSpace H E₀).starProjection ψ‖ ^ 2) ≤
        (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2)
    (hM : M.IsHermitian) (hHM : ‖H - M‖ ≤ ε) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      Δ * (1 - ‖(groundSpace H E₀).starProjection φ‖ ^ 2) ≤ 2 * ε ∧
      (2 * ε < Δ → (groundSpace H E₀).starProjection φ ≠ 0) := by
  obtain ⟨e, φ, hφ, heig, hmin, henergy⟩ :=
    exists_groundVector_energy_le_of_norm_sub_le hΩ hHΩ hM hHM
  have hmass : Δ * (1 - ‖(groundSpace H E₀).starProjection φ‖ ^ 2) ≤ 2 * ε := by
    have hg := hgap φ
    rw [hφ, one_pow, mul_one] at hg
    exact hg.trans henergy
  refine ⟨e, φ, hφ, heig, hmin, hmass, ?_⟩
  intro hsmall hz
  rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, mul_one] at hmass
  linarith

/-- A logarithmic radius makes an exponential approximation error smaller than
one quarter of the gap times a prescribed accuracy.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
private theorem exp_error_le_of_log_radius {B β Δ τ ℓ : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ)
    (hτ : 0 < τ) (hℓ : Real.log (4 * max B 1 / (Δ * τ)) / β ≤ ℓ) :
    B * Real.exp (-(β * ℓ)) ≤ Δ * τ / 4 := by
  let Q := max B 1
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hr : 0 < 4 * Q / (Δ * τ) := by positivity
  have hlog : Real.log (4 * Q / (Δ * τ)) ≤ ℓ * β := (div_le_iff₀ hβ).mp hℓ
  have he : Real.exp (-(β * ℓ)) ≤ Δ * τ / (4 * Q) := by
    calc Real.exp (-(β * ℓ)) ≤ Real.exp (-Real.log (4 * Q / (Δ * τ))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log hr, inv_div]
  calc B * Real.exp (-(β * ℓ)) ≤ Q * Real.exp (-(β * ℓ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ Q * (Δ * τ / (4 * Q)) := mul_le_mul_of_nonneg_left he hQ.le
    _ = _ := by field_simp

/-- An exponential norm approximation gives a ground vector of nonzero overlap
and arbitrary phase-minimized accuracy at an explicit logarithmic radius.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_overlap_of_exp_norm_bound {H M : Matrix n n ℂ}
    {E₀ Δ B β ℓ η : ℝ} {Ω : EuclideanSpace ℂ n} (hH : H.IsHermitian) (hΩ : ‖Ω‖ = 1)
    (hgs : IsGapped H E₀ Δ) (hspan : groundSpace H E₀ = Submodule.span ℂ {Ω}) (hΔ : 0 < Δ)
    (hM : M.IsHermitian) (hβ : 0 < β) (hη : 0 < η)
    (hHM : ‖H - M‖ ≤ B * Real.exp (-(β * ℓ)))
    (hℓ : Real.log (4 * max B 1 / (Δ * min η 1)) / β ≤ ℓ) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      ⟪Ω, φ⟫_ℂ ≠ 0 ∧
      ∃ θ : ℝ, IsMinOn
        (fun α : ℝ ↦ ‖φ - Complex.exp (α * Complex.I) • Ω‖) Set.univ θ ∧
        ‖φ - Complex.exp (θ * Complex.I) • Ω‖ ^ 2 ≤ η := by
  have herr := exp_error_le_of_log_radius hβ hΔ (lt_min hη zero_lt_one) hℓ
  obtain ⟨e, φ, hφ, heig, hmin, hgap, θ, hminθ, hphase⟩ :=
    exists_groundVector_overlap_of_norm_sub_le hH hΩ hgs hspan hΔ hM hHM
  have hsmall : 2 * (B * Real.exp (-(β * ℓ))) ≤ Δ / 2 := by
    nlinarith [min_le_right η 1]
  have hnonzero : ⟪Ω, φ⟫_ℂ ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, mul_one] at hgap
    linarith
  refine ⟨e, φ, hφ, heig, hmin, hnonzero, θ, hminθ, hphase.trans ?_⟩
  apply le_trans _ (min_le_left η 1)
  apply (div_le_iff₀ hΔ).mpr
  nlinarith


/-- An exponential approximation gives a ground vector with nonzero projection onto
the full original ground eigenspace at a logarithmic radius.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_projection_of_exp_norm_bound {H M : Matrix n n ℂ}
    {E₀ Δ B β ℓ η : ℝ} {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω = (E₀ : ℂ) • Ω)
    (hgap : ∀ ψ : EuclideanSpace ℂ n,
      Δ * (‖ψ‖ ^ 2 - ‖(groundSpace H E₀).starProjection ψ‖ ^ 2) ≤
        (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2)
    (hΔ : 0 < Δ) (hM : M.IsHermitian) (hβ : 0 < β) (hη : 0 < η)
    (hHM : ‖H - M‖ ≤ B * Real.exp (-(β * ℓ)))
    (hℓ : Real.log (4 * max B 1 / (Δ * min η 1)) / β ≤ ℓ) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      (groundSpace H E₀).starProjection φ ≠ 0 ∧
      1 - ‖(groundSpace H E₀).starProjection φ‖ ^ 2 ≤ η := by
  have herr := exp_error_le_of_log_radius hβ hΔ (lt_min hη zero_lt_one) hℓ
  obtain ⟨e, φ, hφ, heig, hmin, hmass, hnonzero⟩ :=
    exists_groundVector_projected_mass_of_norm_sub_le hΩ hHΩ hgap hM hHM
  have hsmall : 2 * (B * Real.exp (-(β * ℓ))) < Δ := by
    nlinarith [min_le_right η 1]
  refine ⟨e, φ, hφ, heig, hmin, hnonzero hsmall, ?_⟩
  apply (mul_le_mul_iff_right₀ hΔ).mp
  nlinarith [min_le_left η 1]

end ManyBody
