/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Eigenvalue.EuclideanEigenvectorBasis
import QICLean.Analysis.Order.LowEnergyPerturbation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Group.Basic
import QICLean.Analysis.Topology.CompactUniformBounds
import QICLean.Spectral.Perturbation.KernelGapPerturbation
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum

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
* `LinearMap.IsPositive.smul_orthogonal_ker_projection_le_of_forall_hasEigenvalue`,
  `LinearMap.forall_hasEigenvalue_of_smul_orthogonal_ker_projection_le` — for a positive operator,
  the gap `γ` above the kernel is the operator inequality `γ P ≤ H`, with `P` the orthogonal
  projection onto the orthogonal complement of the kernel; and `γ P ≤ H ≤ C P` for some
  `0 < γ` and `C` (`exists_pos_smul_orthogonal_ker_projection_le`,
  `exists_pos_le_smul_orthogonal_ker_projection`).
* `LinearMap.IsPositive.smul_starProjection_orthogonal_le_iff` — for a positive operator that
  annihilates a subspace `U`, the operator inequality `γ P ≤ H`, with `P` the orthogonal
  projection onto `Uᗮ`, is the quadratic-form bound `γ ‖v‖² ≤ Re ⟨H v, v⟩` on `Uᗮ`.
* `Matrix.IsHermitian.mul_norm_sq_le_re_inner_of_spectral_gap` — for a Hermitian matrix, a lower
  bound for every nonzero real point of the spectrum bounds the quadratic form on the orthogonal
  complement of the kernel. This is the spectral step used with detectability in ALVV,
  arXiv:1602.08828v2, `lem:dl` and `thm:FF-tH`, lines 1508–1519 and 1562–1568.

The quadratic-form inequality `H² ≥ γ H` is moved from TNLean,
`TNLean/MPS/ParentHamiltonian/Martingale/QuadraticFormGap.lean` at commit `414a18fb88`, with the
norm-form hypothesis replaced by the eigenvalue form. The operator form of the gap is moved from
TNLean, `TNLean/MPS/ParentHamiltonian/ParentInteraction/FiniteIntervalGapComparison.lean` and
`TNLean/MPS/ParentHamiltonian/Gap/Comparison/IntervalGapTransport.lean` at commit `600676ccac`;
its eigenvalue-form direction is proved through the quadratic form. Its version for a subspace
annihilated by `H` is moved from TNLean,
`TNLean/MPS/ParentHamiltonian/Gap/Filtration/SparseGroupedOpenGap.lean` at commit `6a5afb57c2`,
with the converse added.
* `LinearEquiv.ker_adjoint_congruence`,
  `LinearMap.IsPositive.norm_gap_adjoint_congruence_of_inverse_bound`: spectral gaps under bounded
  invertible congruences.
* `IsCompact.exists_uniform_norm_lower_bound_on_tail`,
  `ContinuousLinearMap.exists_uniform_norm_gap_of_compact`: uniform norm gaps on compact parameter
  sets.
* `LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker`, `Nat.exists_pos_forall_of_eventually`:
  norm gaps on the orthogonal complement of a kernel.
* `LinearMap.IsPositive.re_inner_ge_of_norm_gap`, `LinearMap.IsPositive.norm_gap_of_le_of_ker_eq`:
  transfer of gaps through positive-operator comparison.
-/

section OrthogonalKernelGap

/-!
## Norm gaps on the orthogonal complement of a kernel

A linear map \(f\) on a finite-dimensional inner product space is injective on
\((\ker f)^\perp\), hence bounded below there: there is \(\delta>0\) with
\(\delta\|v\|\le\|fv\|\) for every \(v\in(\ker f)^\perp\).

For a sequence of such maps, a lower bound that holds with one constant from
some index on extends to every index: the finitely many earlier indices each
have their own positive constant, and one takes the minimum.

Moved from TNLean, `TNLean/Algebra/OrthogonalKernelGap.lean` at
commit `414a18fb88`, with no change to the statements.

### Main declarations

* `LinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker`: the positive lower
  bound on the orthogonal complement of the kernel.
* `Nat.exists_pos_forall_of_eventually`: an eventual positive constant for a
  downward-closed property, combined with a positive constant at each index,
  gives one positive constant at every index.
-/

namespace LinearMap

/-- A linear map on a finite-dimensional inner product space is bounded below on
the orthogonal complement of its kernel: there is \(\delta>0\) with
\(\delta\|v\|\le\|fv\|\) for all \(v\in(\ker f)^\perp\). -/
theorem exists_pos_mul_norm_le_of_mem_orthogonal_ker {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E →ₗ[𝕜] F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ (LinearMap.ker f)ᗮ, δ * ‖v‖ ≤ ‖f v‖ := by
  have hi : Function.Injective (f.domRestrict (LinearMap.ker f)ᗮ) :=
    LinearMap.injective_domRestrict_iff.mpr (Submodule.orthogonal_disjoint _).symm
  obtain ⟨K, hK, hbound⟩ := (f.domRestrict (LinearMap.ker f)ᗮ).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hi)
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr (by exact_mod_cast hK), fun v hv ↦ ?_⟩
  exact (inv_mul_le_iff₀ (show 0 < (K : ℝ) by exact_mod_cast hK)).mpr
    (ZeroHomClass.bound_of_antilipschitz _ hbound ⟨v, hv⟩)

end LinearMap

/-- Let \(P(N,\gamma)\) be a property of an index \(N\) and a constant \(\gamma\)
that is closed under decreasing \(\gamma\). If \(P(N,\delta)\) holds for all
\(N\ge M\) with one \(\delta>0\), and each index has some positive constant, then
one positive constant works at every index. -/
theorem Nat.exists_pos_forall_of_eventually {P : ℕ → ℝ → Prop}
    (hmono : ∀ N {γ δ : ℝ}, γ ≤ δ → P N δ → P N γ)
    (hfix : ∀ N, ∃ η : ℝ, 0 < η ∧ P N η) {M : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hev : ∀ N, M ≤ N → P N δ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N, P N γ := by
  induction M generalizing δ with
  | zero => exact ⟨δ, hδ, fun N ↦ hev N (Nat.zero_le N)⟩
  | succ M ih =>
    obtain ⟨η, hη, hM⟩ := hfix M
    refine ih (lt_min hδ hη) fun N hN ↦ ?_
    rcases eq_or_lt_of_le hN with rfl | hN
    · exact hmono _ (min_le_right δ η) hM
    · exact hmono _ (min_le_left δ η) (hev N hN)

end OrthogonalKernelGap

section PositiveGapTransfer

/-!
## Transfer of gaps through positive-operator comparison

A finite-dimensional spectral argument transfers a known gap from a positive
operator to a larger positive operator with the same kernel.

### Main results

* `LinearMap.IsPositive.re_inner_ge_of_norm_gap` converts a norm gap on the
  orthogonal complement of the kernel into a quadratic-form lower bound.
* `LinearMap.IsPositive.norm_gap_of_le_of_ker_eq` transfers a norm gap through
  Loewner domination when the kernels agree.
-/

open scoped InnerProductSpace

namespace LinearMap.IsPositive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- For a positive operator, a norm lower bound on the orthogonal complement
of its kernel implies the same quadratic-form lower bound. -/
theorem re_inner_ge_of_norm_gap {P : E →ₗ[ℂ] E} (hP : P.IsPositive)
    {γ : ℝ} (_hγ : 0 ≤ γ)
    (hGap : ∀ v ∈ (LinearMap.ker P)ᗮ, γ * ‖v‖ ≤ ‖P v‖)
    (v : E) (hv : v ∈ (LinearMap.ker P)ᗮ) :
    γ * ‖v‖ ^ 2 ≤ (⟪P v, v⟫_ℂ).re := by
  classical
  let n := Module.finrank ℂ E
  let b := hP.isSymmetric.eigenvectorBasis rfl
  let μ := hP.isSymmetric.eigenvalues rfl
  have hμ : ∀ i, 0 ≤ μ i := hP.nonneg_eigenvalues rfl
  have hμGap : ∀ i, μ i = 0 ∨ γ ≤ μ i := by
    intro i
    by_cases hi : μ i = 0
    · exact Or.inl hi
    · right
      have hbi : b i ∈ (LinearMap.ker P)ᗮ := by
        intro w hw
        rw [LinearMap.mem_ker] at hw
        have horth := hP.isSymmetric w (b i)
        rw [hw, inner_zero_left, hP.isSymmetric.apply_eigenvectorBasis rfl,
          inner_smul_right] at horth
        exact (mul_eq_zero.mp horth.symm).resolve_left (Complex.ofReal_ne_zero.mpr hi)
      have h := hGap (b i) hbi
      rw [hP.isSymmetric.apply_eigenvectorBasis rfl, norm_smul,
        OrthonormalBasis.norm_eq_one] at h
      have h' : γ ≤ |μ i| := by
        simpa only [RCLike.norm_ofReal, mul_one] using h
      rwa [abs_of_nonneg (hμ i)] at h'
  have hv_sq : ‖v‖ ^ 2 = ∑ i, ‖(b.repr v) i‖ ^ 2 := by
    rw [← b.repr.norm_map v, EuclideanSpace.norm_sq_eq]
  have hPv : P v = ∑ i, ((μ i : ℂ) * (b.repr v) i) • b i := by
    nth_rw 1 [← b.sum_repr v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, hP.isSymmetric.apply_eigenvectorBasis rfl, smul_smul]
    congr 1
    exact mul_comm _ _
  have hquad : (⟪P v, v⟫_ℂ).re =
      ∑ i, μ i * ‖(b.repr v) i‖ ^ 2 := by
    rw [hPv, sum_inner, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_smul_left, b.repr_apply_apply, map_mul, Complex.conj_ofReal]
    rw [mul_assoc]
    rw [← Complex.normSq_eq_conj_mul_self]
    rw [Complex.sq_norm]
    simp
  rw [hv_sq, hquad, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rcases hμGap i with hzero | hbound
  · have hcoeff : (b.repr v) i = 0 := by
      rw [b.repr_apply_apply]
      exact Submodule.inner_right_of_mem_orthogonal
        (by
          rw [LinearMap.mem_ker, hP.isSymmetric.apply_eigenvectorBasis rfl]
          change (μ i : ℂ) • b i = 0
          simp [hzero]) hv
    simp [hcoeff]
  · exact mul_le_mul_of_nonneg_right hbound (sq_nonneg _)

/-- An operator \(Q\) inherits the norm gap of a positive operator \(P\)
when \(P \leq Q\) in Loewner order and their kernels agree. -/
theorem norm_gap_of_le_of_ker_eq {P Q : E →ₗ[ℂ] E}
    (hP : P.IsPositive) {γ : ℝ} (hγ : 0 ≤ γ)
    (hPQ : P ≤ Q) (hker : LinearMap.ker P = LinearMap.ker Q)
    (hGap : ∀ v ∈ (LinearMap.ker P)ᗮ, γ * ‖v‖ ≤ ‖P v‖) :
    ∀ v ∈ (LinearMap.ker Q)ᗮ, γ * ‖v‖ ≤ ‖Q v‖ := by
  intro v hv
  have hvP : v ∈ (LinearMap.ker P)ᗮ := by simpa [hker] using hv
  have henergyP := hP.re_inner_ge_of_norm_gap hγ hGap v hvP
  have henergyPQ : (⟪P v, v⟫_ℂ).re ≤ (⟪Q v, v⟫_ℂ).re := by
    have hnonneg := hPQ.re_inner_nonneg_left v
    simpa [sub_apply, inner_sub_left] using hnonneg
  have hinnerNorm : (⟪Q v, v⟫_ℂ).re ≤ ‖Q v‖ * ‖v‖ :=
    @re_inner_le_norm ℂ E _ _ _ (Q v) v
  by_cases hv0 : v = 0
  · simp [hv0]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have hmul : γ * ‖v‖ * ‖v‖ ≤ ‖Q v‖ * ‖v‖ := by
      calc
        γ * ‖v‖ * ‖v‖ = γ * ‖v‖ ^ 2 := by ring
        _ ≤ (⟪P v, v⟫_ℂ).re := henergyP
        _ ≤ (⟪Q v, v⟫_ℂ).re := henergyPQ
        _ ≤ ‖Q v‖ * ‖v‖ := hinnerNorm
    exact le_of_mul_le_mul_right hmul hvpos

end LinearMap.IsPositive

end PositiveGapTransfer

section EigenvalueGap

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


/-! ### The gap above the kernel in operator form -/

private theorem inner_eq_inner_orthogonal_ker_projection {H : E →ₗ[ℂ] E} (hH : H.IsPositive)
    (v : E) :
    ⟪H v, v⟫_ℂ =
      ⟪H ((LinearMap.ker H)ᗮ.starProjection v), (LinearMap.ker H)ᗮ.starProjection v⟫_ℂ := by
  have hproj : H ((LinearMap.ker H).starProjection v) = 0 :=
    LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem _ _)
  simp only [Submodule.starProjection_orthogonal_val, map_sub, sub_zero,
    hH.isSymmetric v, hproj]

/-- **The gap on the orthogonal complement of a subspace in operator form.** Let `H` be a
positive operator that annihilates a subspace `U`. Then `γ P ≤ H` for the orthogonal projection
`P` onto `Uᗮ` exactly when `γ ‖v‖² ≤ Re ⟨H v, v⟩` for every `v` orthogonal to `U`. For
`U = ker H` this is the operator form of the gap above the kernel. -/
theorem smul_starProjection_orthogonal_le_iff {H : E →ₗ[ℂ] E} (hH : H.IsPositive)
    {U : Submodule ℂ E} (hU : U ≤ LinearMap.ker H) {γ : ℝ} :
    (γ : ℂ) • Uᗮ.starProjection.toLinearMap ≤ H ↔
      ∀ v ∈ Uᗮ, γ * ‖v‖ ^ 2 ≤ (⟪H v, v⟫_ℂ).re := by
  constructor
  · intro hLower v hv
    have h := hLower.re_inner_nonneg_left v
    have hv2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
    simp only [RCLike.re_eq_complex_re] at hv2
    rw [LinearMap.sub_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      Uᗮ.starProjection_eq_self_iff.mpr hv, inner_sub_left, inner_smul_left,
      Complex.conj_ofReal] at h
    simp only [RCLike.re_eq_complex_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hv2] at h
    linarith
  intro hq
  refine ⟨hH.isSymmetric.sub (Uᗮ.starProjection_isSymmetric.smul (by simp)), ?_⟩
  intro v
  have hproj : H (U.starProjection v) = 0 :=
    LinearMap.mem_ker.mp (hU (Submodule.starProjection_apply_mem _ _))
  have hform : ⟪H v, v⟫_ℂ = ⟪H (Uᗮ.starProjection v), Uᗮ.starProjection v⟫_ℂ := by
    simp only [Submodule.starProjection_orthogonal_val, map_sub, hproj, sub_zero,
      hH.isSymmetric v]
  have hnorm : (⟪Uᗮ.starProjection v, v⟫_ℂ).re = ‖Uᗮ.starProjection v‖ ^ 2 :=
    Uᗮ.re_inner_starProjection_eq_normSq v
  have h := hq (Uᗮ.starProjection v) (Submodule.starProjection_apply_mem _ _)
  change 0 ≤ (⟪H v - (γ : ℂ) • Uᗮ.starProjection v, v⟫_ℂ).re
  simpa only [inner_sub_left, inner_smul_left, Complex.sub_re, Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    hnorm, hform, sub_nonneg] using h

/-- A norm gap `γ ≥ 0` of a positive operator gives the lower order bound `γ P ≤ H` by the
orthogonal projection `P` onto the orthogonal complement of its kernel. -/
theorem smul_orthogonal_ker_projection_le_of_norm_gap {H : E →ₗ[ℂ] E} (hH : H.IsPositive)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hGap : ∀ v ∈ (LinearMap.ker H)ᗮ, γ * ‖v‖ ≤ ‖H v‖) :
    (γ : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap ≤ H :=
  (hH.smul_starProjection_orthogonal_le_iff le_rfl).mpr (hH.re_inner_ge_of_norm_gap hγ hGap)

/-- **The gap above the kernel in operator form.** If every eigenvalue of a positive operator
`H` other than `0` is at least `γ`, then `γ P ≤ H` for the orthogonal projection `P` onto the
orthogonal complement of the kernel. -/
theorem smul_orthogonal_ker_projection_le_of_forall_hasEigenvalue {H : E →ₗ[ℂ] E}
    (hH : H.IsPositive) {γ : ℝ} (_hγ : 0 ≤ γ)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue H μ → μ = 0 ∨ (γ : ℂ) ≤ μ) :
    (γ : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap ≤ H :=
  (hH.smul_starProjection_orthogonal_le_iff le_rfl).mpr fun _ hv ↦
    (hH.isSymmetric.mul_norm_sq_le_re_inner_of_forall_hasEigenvalue hGap hv).trans_eq
      (inner_re_symm (𝕜 := ℂ) _ _)

/-- A positive operator on a finite-dimensional space dominates a positive multiple of the
orthogonal projection onto the orthogonal complement of its kernel. -/
theorem exists_pos_smul_orthogonal_ker_projection_le {H : E →ₗ[ℂ] E} (hH : H.IsPositive) :
    ∃ γ : ℝ, 0 < γ ∧
      (γ : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap ≤ H := by
  obtain ⟨γ, hγ, hGap⟩ := H.exists_pos_mul_norm_le_of_mem_orthogonal_ker
  exact ⟨γ, hγ, hH.smul_orthogonal_ker_projection_le_of_norm_gap hγ.le hGap⟩

/-- A positive operator on a finite-dimensional space is bounded above by a positive multiple of
the orthogonal projection onto the orthogonal complement of its kernel. -/
theorem exists_pos_le_smul_orthogonal_ker_projection {H : E →ₗ[ℂ] E} (hH : H.IsPositive) :
    ∃ C : ℝ, 0 < C ∧
      H ≤ (C : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap := by
  let C : ℝ := ‖H.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by positivity
  refine ⟨C, hC,
    ((LinearMap.ker H)ᗮ.starProjection_isSymmetric.smul (by simp)).sub hH.isSymmetric,
    ?_⟩
  intro v
  let w := (LinearMap.ker H)ᗮ.starProjection v
  have hbound : (⟪H w, w⟫_ℂ).re ≤ C * ‖w‖ ^ 2 := by
    calc
      _ ≤ ‖H w‖ * ‖w‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ (‖H.toContinuousLinearMap‖ * ‖w‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (H.toContinuousLinearMap.le_opNorm w) (norm_nonneg _)
      _ ≤ C * ‖w‖ ^ 2 := by dsimp [C]; nlinarith [sq_nonneg ‖w‖]
  have hnorm : (⟪(LinearMap.ker H)ᗮ.starProjection v, v⟫_ℂ).re =
      ‖(LinearMap.ker H)ᗮ.starProjection v‖ ^ 2 :=
    Submodule.re_inner_starProjection_eq_normSq (𝕜 := ℂ) (LinearMap.ker H)ᗮ v
  change 0 ≤ (⟪(C : ℂ) • (LinearMap.ker H)ᗮ.starProjection v - H v, v⟫_ℂ).re
  simpa only [inner_sub_left, inner_smul_left, Complex.sub_re,
    Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hnorm,
    inner_eq_inner_orthogonal_ker_projection hH v, sub_nonneg] using hbound

end LinearMap.IsPositive

namespace LinearMap

variable [FiniteDimensional ℂ E]

/-- **The eigenvalues from the operator form of the gap.** If `γ P ≤ H` for the orthogonal
projection `P` onto the orthogonal complement of the kernel of `H`, then every eigenvalue of `H`
other than `0` is at least `γ`. -/
theorem forall_hasEigenvalue_of_smul_orthogonal_ker_projection_le (H : E →ₗ[ℂ] E) {γ : ℝ}
    (hLower : (γ : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap ≤ H) :
    ∀ μ : ℂ, Module.End.HasEigenvalue H μ → μ = 0 ∨ (γ : ℂ) ≤ μ := by
  have hH : H.IsSymmetric := by
    simpa only [sub_add_cancel] using hLower.isSymmetric.add
      ((LinearMap.ker H)ᗮ.starProjection_isSymmetric.smul (c := (γ : ℂ)) (by simp))
  refine hH.forall_hasEigenvalue_of_re_inner fun v hv ↦ ?_
  have h := hLower.re_inner_nonneg_left v
  have hv2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  simp only [RCLike.re_eq_complex_re] at hv2
  rw [LinearMap.sub_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    (LinearMap.ker H)ᗮ.starProjection_eq_self_iff.mpr hv, inner_sub_left, inner_smul_left,
    hH v v, Complex.conj_ofReal] at h
  simp only [RCLike.re_eq_complex_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hv2] at h
  linarith

end LinearMap

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

end EigenvalueGap

section BoundedCongruenceGap

/-!
## Spectral gaps under bounded invertible congruences

Let \(P\) be positive with gap \(\delta\) above its kernel, and let
\(e\) be an invertible linear map satisfying
\(\lVert e^{-1}w\rVert \le C\lVert w\rVert\).
Then \(e^*Pe\) is positive, its kernel is \(e^{-1}(\ker P)\), and
its gap is at least \(\delta/C^2\).

The constant depends only on the inverse bound. In particular, a deformation
supported on a bounded number of sites can use this estimate once its inverse
bound has been established independently of the size of the system.

Moved from TNLean, `TNLean/MPS/ParentHamiltonian/Martingale/BoundedCongruenceGap.lean` at
commit `414a18fb88`, with no change to the statements.
-/

open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- Invertible congruence pulls back the kernel, without requiring positivity. -/
theorem LinearEquiv.ker_adjoint_congruence (e : E ≃ₗ[ℂ] F) (P : F →ₗ[ℂ] F) :
    LinearMap.ker (e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap) =
      (LinearMap.ker P).comap e.toLinearMap := by
  ext v
  change e.toLinearMap.adjoint (P (e v)) = 0 ↔ P (e v) = 0
  constructor
  · intro hv
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    calc
      ⟪P (e v), P (e v)⟫_ℂ =
          ⟪e.toLinearMap.adjoint (P (e v)), e.symm (P (e v))⟫_ℂ := by
        rw [LinearMap.adjoint_inner_left]
        simp
      _ = 0 := by rw [hv, inner_zero_left]
  · intro hv
    simp [hv]

namespace LinearMap.IsPositive

/-- A bounded inverse loses at most a factor \(C^2\) in a positive
operator's norm gap under congruence. The kernel in the conclusion is the
actual kernel of \(e^*Pe\). -/
theorem norm_gap_adjoint_congruence_of_inverse_bound
    {P : F →ₗ[ℂ] F} (hP : P.IsPositive) (e : E ≃ₗ[ℂ] F)
    {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 < C)
    (hInverse : ∀ w : F, ‖e.symm w‖ ≤ C * ‖w‖)
    (hGap : ∀ w ∈ (LinearMap.ker P)ᗮ, δ * ‖w‖ ≤ ‖P w‖) :
    ∀ v ∈ (LinearMap.ker (e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap))ᗮ,
      (δ / C ^ 2) * ‖v‖ ≤ ‖(e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap) v‖ := by
  intro v hv
  let Q := e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap
  let w := (LinearMap.ker P)ᗮ.starProjection (e v)
  let u := e.symm ((LinearMap.ker P).starProjection (e v))
  have hproj : P ((LinearMap.ker P).starProjection (e v)) = 0 :=
    LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem _ _)
  have hu : u ∈ LinearMap.ker Q := by
    rw [show LinearMap.ker Q = (LinearMap.ker P).comap e.toLinearMap from
      e.ker_adjoint_congruence P]
    change P (e u) = 0
    simpa only [u, e.apply_symm_apply] using hproj
  have horth : ⟪v, u⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hu hv
  have hdecomp : e.symm w = v - u := by
    simp only [w, u, Submodule.starProjection_orthogonal_val, map_sub,
      e.symm_apply_apply]
  have hnorm : ‖v‖ ≤ C * ‖w‖ := calc
    ‖v‖ ≤ ‖v - u‖ := by
      have hsq : ‖v - u‖ ^ 2 = ‖v‖ ^ 2 + ‖u‖ ^ 2 := by
        simpa only [horth, RCLike.zero_re, mul_zero, sub_zero] using
          norm_sub_sq (𝕜 := ℂ) v u
      nlinarith [norm_nonneg (v - u), norm_nonneg v, sq_nonneg ‖u‖]
    _ = ‖e.symm w‖ := congrArg norm hdecomp.symm
    _ ≤ C * ‖w‖ := hInverse w
  have hnormSq : ‖v‖ ^ 2 ≤ C ^ 2 * ‖w‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg v) hnorm 2
  have henergy : (⟪Q v, v⟫_ℂ).re = (⟪P w, w⟫_ℂ).re := by
    change (⟪e.toLinearMap.adjoint (P (e v)), v⟫_ℂ).re = _
    rw [LinearMap.adjoint_inner_left]
    change (⟪P (e v), e v⟫_ℂ).re = (⟪P w, w⟫_ℂ).re
    simp only [w, Submodule.starProjection_orthogonal_val, map_sub, hproj,
      sub_zero, hP.isSymmetric (e v)]
  have hquadratic : (δ / C ^ 2) * ‖v‖ ^ 2 ≤ ‖Q v‖ * ‖v‖ := calc
    (δ / C ^ 2) * ‖v‖ ^ 2 ≤ (δ / C ^ 2) * (C ^ 2 * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hnormSq (by positivity)
    _ = δ * ‖w‖ ^ 2 := by field_simp [ne_of_gt hC]
    _ ≤ (⟪P w, w⟫_ℂ).re := hP.re_inner_ge_of_norm_gap hδ hGap w
      (Submodule.starProjection_apply_mem _ _)
    _ = (⟪Q v, v⟫_ℂ).re := henergy.symm
    _ ≤ ‖Q v‖ * ‖v‖ := re_inner_le_norm (𝕜 := ℂ) _ _
  by_cases hv0 : v = 0
  · simp [hv0]
  · exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv0)).mp
      (by simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hquadratic)

end LinearMap.IsPositive

end BoundedCongruenceGap

section CompactKernelGap

/-!
## Uniform norm gaps on compact parameter sets

Locally uniform norm lower bounds, valid for every length beyond a threshold, have one positive
constant and one threshold over a compact parameter set. A continuous family of operators on a
finite-dimensional Hilbert space has a uniform positive lower norm bound away from its kernels on
a compact parameter set, provided the orthogonal kernel projections are continuous. Positivity
and self-adjointness are unnecessary for these norm estimates. Both are the compactness step of
the gap argument in arXiv:1010.3732, Appendix A, lines 2575--2578; the matrix form of the second
statement is `IsCompact.exists_uniform_isGapped`.

Moved from TNLean, `TNLean/Algebra/CompactGapBounds.lean` and
`TNLean/Algebra/CompactKernelGap.lean` at commit `414a18fb88`, with no change to the statements.

### Main results

* `IsCompact.exists_uniform_norm_lower_bound_on_tail` — locally uniform norm lower bounds beyond
  a threshold are uniform on a compact set.
* `ContinuousLinearMap.exists_uniform_norm_gap_of_compact` — a uniform norm gap away from the
  kernels on a compact parameter set.
-/

open scoped Topology

namespace IsCompact

/-- Locally uniform norm lower bounds on a tail have one positive constant
and one threshold over a compact parameter set. This specializes the compactness
step of arXiv:1010.3732, Appendix A; linearity is unnecessary. -/
theorem exists_uniform_norm_lower_bound_on_tail
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {E F : ℕ → Type*} [∀ N, SeminormedAddCommGroup (E N)]
    [∀ N, SeminormedAddCommGroup (F N)]
    (H : X → ∀ N : ℕ, E N → F N) (V : X → ∀ N : ℕ, Set (E N))
    (hlocal : ∀ x ∈ S, ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ,
      ∀ᶠ y in 𝓝 x, ∀ N : ℕ, N₀ ≤ N → ∀ v ∈ V y N, δ * ‖v‖ ≤ ‖H y N v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ x ∈ S, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ V x N, δ * ‖v‖ ≤ ‖H x N v‖ := by
  apply hS.exists_uniform_pos_nat_bounds
    (fun δ N₀ x => ∀ N : ℕ, N₀ ≤ N → ∀ v ∈ V x N, δ * ‖v‖ ≤ ‖H x N v‖)
  · intro δ δ' N₀ x hle hgap N hN v hv
    exact (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap N hN v hv)
  · intro δ N₀ N₁ x hle hgap N hN
    exact hgap N (hle.trans hN)
  · exact hlocal

end IsCompact

namespace ContinuousLinearMap

/-- Continuous operators with continuous orthogonal kernel projections have a
uniform positive norm gap on compact parameter sets. The pointwise gaps follow
from finite dimensionality. Source: arXiv:1010.3732, Appendix A, lines 2575--2578,
for the application to finite-window parent Hamiltonians. -/
theorem exists_uniform_norm_gap_of_compact
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (H : X → E →L[ℂ] E) (hH : Continuous H)
    (hK : Continuous fun x => (LinearMap.ker (H x).toLinearMap).starProjection)
    {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S,
      ∀ v ∈ (LinearMap.ker (H x).toLinearMap)ᗮ, δ * ‖v‖ ≤ ‖H x v‖ := by
  suffices ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ x ∈ S,
      ∀ v ∈ (LinearMap.ker (H x).toLinearMap)ᗮ, δ * ‖v‖ ≤ ‖H x v‖ by
    obtain ⟨δ, hδ, _, hgap⟩ := this
    exact ⟨δ, hδ, hgap⟩
  apply hS.exists_uniform_pos_nat_bounds
    (fun δ _ x => ∀ v ∈ (LinearMap.ker (H x).toLinearMap)ᗮ,
      δ * ‖v‖ ≤ ‖H x v‖)
  · exact fun hle hgap v hv =>
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap v hv)
  · exact fun _ hgap => hgap
  · intro x _hx
    obtain ⟨γ, hγ, hgap⟩ :=
      (H x).toLinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
    refine ⟨γ / 2, half_pos hγ, 0, ?_⟩
    apply eventually_norm_gap_on_orthogonal H
      (fun y => LinearMap.ker (H y).toLinearMap)
      hH.continuousAt hK.continuousAt le_rfl hγ (half_lt_self hγ) hgap

end ContinuousLinearMap

end CompactKernelGap
