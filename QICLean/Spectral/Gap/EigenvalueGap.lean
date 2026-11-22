/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Gap.PositiveGapTransfer

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

The last statement is moved from TNLean, `TNLean/MPS/ParentHamiltonian/Martingale/
QuadraticFormGap.lean` at commit `414a18fb88`, with the norm-form hypothesis replaced by the
eigenvalue form.
-/

open scoped InnerProductSpace ComplexOrder

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
  have hHv : H v = ∑ i, ((μ i : ℂ) * (b.repr v) i) • b i := by
    nth_rw 1 [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, hH.apply_eigenvectorBasis rfl, smul_smul]
    exact congrArg (· • b i) (mul_comm _ _)
  have hquad : (⟪H v, v⟫_ℂ).re = ∑ i, μ i * ‖(b.repr v) i‖ ^ 2 := by
    rw [hHv, sum_inner, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_smul_left, b.repr_apply_apply, map_mul, Complex.conj_ofReal, mul_assoc,
      ← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
    simp
  rw [← hH v v, hv_sq, hquad, Finset.mul_sum]
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
  refine ⟨fun h v hv ↦ ?_, fun hn μ hμ ↦ ?_⟩
  · rcases eq_or_ne v 0 with rfl | hv0
    · simp
    refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hv0)
    calc Δ * ‖v‖ * ‖v‖ = Δ * ‖v‖ ^ 2 := by ring
      _ ≤ (⟪v, H v⟫_ℂ).re := (hH.forall_hasEigenvalue_iff_re_inner.mp h) v hv
      _ ≤ ‖v‖ * ‖H v‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ = ‖H v‖ * ‖v‖ := mul_comm _ _
  rcases eq_or_ne μ 0 with hμ0 | hμ0
  · exact Or.inl hμ0
  right
  obtain ⟨ψ, hψ⟩ := hμ.exists_hasEigenvector
  have hreal : μ.im = 0 :=
    Complex.conj_eq_iff_im.mp (hH.isSymmetric.conj_eigenvalue_eq_self hμ)
  have hψ0 : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ.2
  have hre : 0 ≤ μ.re := by
    have h := hH.re_inner_nonneg_right ψ
    rw [hψ.apply_eq_smul, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
    have h' : 0 ≤ μ.re * ‖ψ‖ ^ 2 := by simpa [← Complex.ofReal_pow] using h
    exact nonneg_of_mul_nonneg_left h' (pow_pos hψ0 2)
  have hnorm : ‖μ‖ = μ.re := by
    rw [← Complex.re_add_im μ, hreal]
    simp [abs_of_nonneg hre]
  have hg := hn ψ (hH.isSymmetric.mem_orthogonal_ker_of_apply_eq_smul hμ0 hψ.apply_eq_smul)
  rw [hψ.apply_eq_smul, norm_smul, hnorm] at hg
  rw [Complex.le_def]
  exact ⟨by simpa using le_of_mul_le_mul_right hg hψ0, by simp [hreal]⟩

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
