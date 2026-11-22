/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Gap.PositiveGapTransfer
import QICLean.Spectral.Eigenvalue.EuclideanEigenvectorBasis
import QICLean.Analysis.Order.LowEnergyPerturbation

/-!
# The gap above the kernel in eigenvalue, quadratic and norm form

Let `H` be an operator on a finite-dimensional complex inner product space and `Δ` a real
number. Three statements say that `H` has gap `Δ` above its kernel:

* every eigenvalue of `H` other than `0` is at least `Δ`;
* `Δ ‖v‖² ≤ Re ⟨v, H v⟩` for every `v` orthogonal to the kernel;
* `Δ ‖v‖ ≤ ‖H v‖` for every `v` orthogonal to the kernel.

The first two are equivalent for a symmetric operator, and all three for a positive one. No
sign of `Δ` and no nonzero kernel is assumed: for a zero kernel each statement says that `H` is
bounded below by `Δ`.

## Main results

* `LinearMap.IsSymmetric.mul_norm_sq_le_re_inner_of_forall_hasEigenvalue`,
  `LinearMap.IsSymmetric.forall_hasEigenvalue_of_re_inner` — the eigenvalue form and the
  quadratic form of the gap imply each other for a symmetric operator.
* `LinearMap.IsPositive.forall_hasEigenvalue_iff_re_inner`,
  `LinearMap.IsPositive.forall_hasEigenvalue_iff_norm` — for a positive operator, the
  eigenvalue form of the gap is its quadratic form and its norm form.
* `LinearMap.IsPositive.quadraticForm_sq_ge_of_forall_hasEigenvalue` — a positive operator with
  gap `γ ≥ 0` above its kernel satisfies `H² ≥ γ H` as a quadratic form on the whole space.
* `Matrix.IsHermitian.mul_norm_sq_le_re_inner_of_spectral_gap` — for a Hermitian matrix, a lower
  bound for every nonzero real point of the spectrum bounds the quadratic form on the orthogonal
  complement of the kernel. This is the spectral step used with detectability in ALVV,
  arXiv:1602.08828v2, `lem:dl` and `thm:FF-tH`, lines 1508–1519 and 1562–1568.

The quadratic-form inequality `H² ≥ γ H` is moved from TNLean,
`TNLean/MPS/ParentHamiltonian/Martingale/QuadraticFormGap.lean` at commit `414a18fb88`, with the
norm-form hypothesis replaced by the eigenvalue form.
-/

open scoped BigOperators InnerProductSpace ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

namespace LinearMap.IsSymmetric

/-- An eigenvector of a symmetric operator with a nonzero eigenvalue is orthogonal to the
kernel. -/
theorem mem_orthogonal_ker_of_apply_eq_smul {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric) {μ : ℂ}
    (hμ : μ ≠ 0) {ψ : E} (hψ : H ψ = μ • ψ) : ψ ∈ (LinearMap.ker H)ᗮ := by
  intro w hw
  have h := hH w ψ
  rw [LinearMap.mem_ker.mp hw, inner_zero_left, hψ, inner_smul_right] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hμ

/-- **The quadratic form above the kernel from the eigenvalues.** If every eigenvalue of a
symmetric operator `H` on a finite-dimensional space other than `0` is at least `Δ`, then
`Δ ‖v‖² ≤ Re ⟨v, H v⟩` for every `v` orthogonal to the kernel. -/
theorem mul_norm_sq_le_re_inner_of_forall_hasEigenvalue [FiniteDimensional ℂ E]
    {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric) {Δ : ℝ}
    (h : ∀ μ : ℂ, Module.End.HasEigenvalue H μ → μ = 0 ∨ (Δ : ℂ) ≤ μ)
    {v : E} (hv : v ∈ (LinearMap.ker H)ᗮ) :
    Δ * ‖v‖ ^ 2 ≤ (⟪v, H v⟫_ℂ).re := by
  classical
  let b := hH.eigenvectorBasis rfl
  let μ := hH.eigenvalues rfl
  have hμGap : ∀ i, μ i = 0 ∨ Δ ≤ μ i := fun i ↦
    (h _ (hH.hasEigenvalue_eigenvalues rfl i)).imp Complex.ofReal_eq_zero.mp
      Complex.real_le_real.mp
  have hv_sq : ‖v‖ ^ 2 = ∑ i, ‖(b.repr v) i‖ ^ 2 := by
    rw [← b.repr.norm_map v, EuclideanSpace.norm_sq_eq]
  rw [hv_sq, b.re_inner_apply_eq_sum_of_eigen μ H (hH.apply_eigenvectorBasis rfl) v,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rcases hμGap i with hzero | hbound
  · have hcoeff : (b.repr v) i = 0 := by
      rw [b.repr_apply_apply]
      refine Submodule.inner_right_of_mem_orthogonal ?_ hv
      rw [LinearMap.mem_ker, hH.apply_eigenvectorBasis rfl]
      change (μ i : ℂ) • b i = 0
      simp [hzero]
    simp [hcoeff]
  · exact mul_le_mul_of_nonneg_right hbound (sq_nonneg _)

/-- **The eigenvalues from the quadratic form above the kernel.** If a symmetric operator `H`
satisfies `Δ ‖v‖² ≤ Re ⟨v, H v⟩` for every `v` orthogonal to its kernel, then every eigenvalue
of `H` other than `0` is at least `Δ`. -/
theorem forall_hasEigenvalue_of_re_inner {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric) {Δ : ℝ}
    (hq : ∀ v ∈ (LinearMap.ker H)ᗮ, Δ * ‖v‖ ^ 2 ≤ (⟪v, H v⟫_ℂ).re) :
    ∀ μ : ℂ, Module.End.HasEigenvalue H μ → μ = 0 ∨ (Δ : ℂ) ≤ μ := by
  intro μ hμ
  rcases eq_or_ne μ 0 with hμ0 | hμ0
  · exact Or.inl hμ0
  right
  obtain ⟨ψ, hψ⟩ := hμ.exists_hasEigenvector
  have hreal : μ.im = 0 := Complex.conj_eq_iff_im.mp (hH.conj_eigenvalue_eq_self hμ)
  have hre : (⟪ψ, H ψ⟫_ℂ).re = μ.re * ‖ψ‖ ^ 2 := by
    rw [hψ.apply_eq_smul, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hg := hq ψ (hH.mem_orthogonal_ker_of_apply_eq_smul hμ0 hψ.apply_eq_smul)
  rw [hre] at hg
  have hpos : 0 < ‖ψ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hψ.2) 2
  rw [Complex.le_def]
  exact ⟨by simpa using le_of_mul_le_mul_right hg hpos, by simp [hreal]⟩

end LinearMap.IsSymmetric

namespace LinearMap.IsPositive

variable [FiniteDimensional ℂ E]

/-- **The gap above the kernel, eigenvalue and quadratic form.** For a positive operator `H` on
a finite-dimensional space, every eigenvalue other than `0` is at least `Δ` exactly when
`Δ ‖v‖² ≤ Re ⟨v, H v⟩` for every `v` orthogonal to the kernel. -/
theorem forall_hasEigenvalue_iff_re_inner {H : E →ₗ[ℂ] E} (hH : H.IsPositive) {Δ : ℝ} :
    (∀ μ : ℂ, Module.End.HasEigenvalue H μ → μ = 0 ∨ (Δ : ℂ) ≤ μ) ↔
      ∀ v ∈ (LinearMap.ker H)ᗮ, Δ * ‖v‖ ^ 2 ≤ (⟪v, H v⟫_ℂ).re :=
  ⟨fun h _ hv ↦ hH.isSymmetric.mul_norm_sq_le_re_inner_of_forall_hasEigenvalue h hv,
    hH.isSymmetric.forall_hasEigenvalue_of_re_inner⟩

/-- **The gap above the kernel, eigenvalue and norm form.** For a positive operator `H` on a
finite-dimensional space, every eigenvalue other than `0` is at least `Δ` exactly when
`Δ ‖v‖ ≤ ‖H v‖` for every `v` orthogonal to the kernel. -/
theorem forall_hasEigenvalue_iff_norm {H : E →ₗ[ℂ] E} (hH : H.IsPositive) {Δ : ℝ} :
    (∀ μ : ℂ, Module.End.HasEigenvalue H μ → μ = 0 ∨ (Δ : ℂ) ≤ μ) ↔
      ∀ v ∈ (LinearMap.ker H)ᗮ, Δ * ‖v‖ ≤ ‖H v‖ := by
  refine hH.forall_hasEigenvalue_iff_re_inner.trans ⟨fun hq v hv ↦ ?_, fun hn v hv ↦ ?_⟩
  · rcases eq_or_ne v 0 with rfl | hv0
    · simp
    refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hv0)
    calc Δ * ‖v‖ * ‖v‖ = Δ * ‖v‖ ^ 2 := by ring
      _ ≤ (⟪v, H v⟫_ℂ).re := hq v hv
      _ ≤ ‖v‖ * ‖H v‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ = ‖H v‖ * ‖v‖ := mul_comm _ _
  rcases lt_or_ge Δ 0 with hΔ | hΔ
  · exact (mul_nonpos_of_nonpos_of_nonneg hΔ.le (sq_nonneg _)).trans
      (hH.re_inner_nonneg_right v)
  · exact (hH.re_inner_ge_of_norm_gap hΔ hn v hv).trans_eq (inner_re_symm (𝕜 := ℂ) _ _)

/-- **The quadratic-form inequality `H² ≥ γ H` from the gap.** If every eigenvalue of a positive
operator `H` on a finite-dimensional space other than `0` is at least `γ ≥ 0`, then
`γ Re ⟨H v, v⟩ ≤ Re ⟨H v, H v⟩` for every `v`. -/
theorem quadraticForm_sq_ge_of_forall_hasEigenvalue {H : E →ₗ[ℂ] E} (hH : H.IsPositive)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue H μ → μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∀ v : E, γ * (⟪H v, v⟫_ℂ).re ≤ (⟪H v, H v⟫_ℂ).re := by
  classical
  have hNorm := hH.forall_hasEigenvalue_iff_norm.mp hGap
  intro v
  let w := v - (LinearMap.ker H).starProjection v
  have hw : w ∈ (LinearMap.ker H)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal v
  have hproj : H ((LinearMap.ker H).starProjection v) = 0 := by
    rw [← LinearMap.mem_ker]
    exact Submodule.starProjection_apply_mem _ _
  have hHw : H w = H v := by
    simp [w, hproj]
  have hcross : ⟪H v, (LinearMap.ker H).starProjection v⟫_ℂ = 0 := by
    rw [hH.isSymmetric v, hproj, inner_zero_right]
  have hinner : ⟪H v, v⟫_ℂ = ⟪H v, w⟫_ℂ := by
    calc
      ⟪H v, v⟫_ℂ = ⟪H v, w + (LinearMap.ker H).starProjection v⟫_ℂ := by
        congr 1
        simp [w]
      _ = ⟪H v, w⟫_ℂ := by rw [inner_add_right, hcross, add_zero]
  calc
    γ * (⟪H v, v⟫_ℂ).re = γ * (⟪H v, w⟫_ℂ).re := by rw [hinner]
    _ ≤ γ * (‖H v‖ * ‖w‖) :=
      mul_le_mul_of_nonneg_left (re_inner_le_norm (𝕜 := ℂ) (H v) w) hγ
    _ = ‖H v‖ * (γ * ‖w‖) := by ring
    _ ≤ ‖H v‖ * ‖H w‖ :=
      mul_le_mul_of_nonneg_left (hNorm w hw) (norm_nonneg _)
    _ = (⟪H v, H v⟫_ℂ).re := by
      rw [hHw, ← pow_two]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (H v)).symm

end LinearMap.IsPositive

namespace Matrix.IsHermitian

/-- The actual spectral gap controls every vector orthogonal to the kernel.
The real bound may have either sign. Auxiliary to ALVV,
arXiv:1602.08828v2, `lem:dl` and `thm:FF-tH`, lines 1508–1519 and 1562–1568. -/
theorem mul_norm_sq_le_re_inner_of_spectral_gap
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {γ : ℝ} (hγgap : ∀ e ∈ spectrum ℝ A, e = 0 ∨ γ ≤ e)
    (x : EuclideanSpace ℂ n)
    (horth : ∀ z : EuclideanSpace ℂ n,
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A z = 0 → ⟪z, x⟫_ℂ = 0) :
    γ * ‖x‖ ^ 2 ≤ (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A x⟫_ℂ).re := by
  have hnorm : ‖x‖ ^ 2 = ∑ j, ‖hA.eigenvectorBasis.repr x j‖ ^ 2 := by
    simpa only [LinearIsometryEquiv.norm_map] using
      EuclideanSpace.norm_sq_eq (hA.eigenvectorBasis.repr x)
  change γ * ‖x‖ ^ 2 ≤
    (⟪x, (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A).toLinearMap x⟫_ℂ).re
  rw [hnorm, Finset.mul_sum,
    hA.eigenvectorBasis.re_inner_apply_eq_sum_of_eigen hA.eigenvalues
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A).toLinearMap
      hA.toEuclideanCLM_eigenvectorBasis x]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rcases hγgap (hA.eigenvalues j) (hA.eigenvalues_mem_spectrum_real j) with hz | hj
  · have hzero : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A
        (hA.eigenvectorBasis j) = 0 := by
      simpa only [hz, map_zero, zero_smul] using
        hA.toEuclideanCLM_eigenvectorBasis j
    have hcoeff : hA.eigenvectorBasis.repr x j = 0 :=
      (hA.eigenvectorBasis.repr_apply_apply x j).trans (horth _ hzero)
    simpa only [hcoeff, norm_zero, zero_pow two_ne_zero, mul_zero] using (le_refl (0 : ℝ))
  · exact mul_le_mul_of_nonneg_right hj (sq_nonneg _)

end Matrix.IsHermitian
