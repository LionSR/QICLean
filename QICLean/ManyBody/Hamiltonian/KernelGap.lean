/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Gap.EigenvalueGap
import QICLean.Spectral.Perturbation.KernelGapPerturbation
import QICLean.Spectral.Gap.PositiveComparisonGap
import QICLean.Analysis.Norm.MatrixToEuclidean
import QICLean.Analysis.Support.InverseSandwich
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.Analysis.Topology.CompactUniformBounds

/-!
# The gap above the kernel

For a positive semidefinite matrix `H`, the ground space at energy `0` is the kernel, and `H` is
gapped at `0` with gap `Δ` exactly when the kernel is nonzero and either of two inequalities
holds on its orthogonal complement: the quadratic-form bound `Δ ‖v‖² ≤ Re ⟨v, H v⟩` or the norm
bound `Δ ‖v‖ ≤ ‖H v‖`. No sign of `Δ` is assumed. Without the nonzero kernel, each inequality is
equivalent to the spectral half of the gap, that every eigenvalue other than `0` is at least `Δ`;
the quadratic-form bound follows from that spectral bound for every Hermitian `H`.

A larger positive matrix with the same kernel keeps the gap; this covers the interpolation
`A + t (B - A)`, `t ≥ 0`, between `A` and a larger `B` whose kernel contains that of `A`. For
positive matrices depending continuously on a parameter, with continuous kernel projections,
every smaller gap persists nearby, and locally uniform gaps are uniform on compact parameter
sets; these are the continuity and compactness steps of arXiv:1010.3732, Appendix A.

The statements generalize those of `TNLean/Algebra/CommonKernelGapInterpolation.lean` and
`TNLean/Algebra/CommonKernelSpectralGap.lean` at commit `414a18fb88`, restated with
`ManyBody.IsGapped` and the eigenvalues of `toEuclideanLin H`; the continuity and compactness
steps use the norm estimates moved unchanged from `TNLean/Algebra/KernelGapPerturbation.lean`
and `TNLean/Algebra/CompactGapBounds.lean`.

## Main results

* `ManyBody.groundSpace_zero` — the ground space at energy `0` is the kernel.
* `ManyBody.mul_norm_sq_le_re_inner_of_hasEigenvalue`, `ManyBody.IsGapped.mul_norm_sq_le_re_inner`
  — for Hermitian `H`, a spectral bound above `0` bounds the quadratic form on the orthogonal
  complement of the kernel.
* `ManyBody.forall_hasEigenvalue_iff_re_inner`, `ManyBody.forall_hasEigenvalue_iff_norm` — for
  positive semidefinite `H`, the spectral bound above `0` in quadratic and norm form.
* `ManyBody.isGapped_zero_iff_inner`, `ManyBody.isGapped_zero_iff_norm` — for positive
  semidefinite `H`, the gap at `0` in quadratic and norm form.
* `ManyBody.groundSpace_zero_eq_of_le`, `ManyBody.forall_hasEigenvalue_of_le`,
  `ManyBody.IsGapped.of_le` — a larger positive matrix whose kernel contains that of `A` has the
  same kernel and keeps the spectral bound and the gap of `A`.
* `ManyBody.forall_hasEigenvalue_of_smul_le_of_le_smul` — a two-sided comparison
  `κ A ≤ B ≤ C A` turns a bound `γ` above `0` on the spectrum of `A` into `κ γ` for `B`.
* `ManyBody.eventually_isGapped_zero` — every smaller gap persists under continuous
  perturbation with continuous kernel projections.
* `IsCompact.exists_uniform_isGapped` — locally uniform gaps beyond a threshold are uniform on a
  compact parameter set.
* `ManyBody.eventually_forall_hasEigenvalue` — the spectral half of `eventually_isGapped_zero`,
  without a ground state.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder Topology

namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ground space at energy `0` is the kernel. -/
theorem groundSpace_zero (H : Matrix n n ℂ) :
    groundSpace H 0 = LinearMap.ker (toEuclideanLin H) := by
  rw [groundSpace, Complex.ofReal_zero, Module.End.eigenspace_zero]

/-- **The quadratic form above the kernel, without a ground state.** If every eigenvalue of a
Hermitian matrix `H` other than `0` is at least `Δ`, then `Δ ‖v‖² ≤ Re ⟨v, H v⟩` for every `v`
orthogonal to the kernel. The kernel may be zero; this is the spectral half of `IsGapped H 0 Δ`.
-/
theorem mul_norm_sq_le_re_inner_of_hasEigenvalue {H : Matrix n n ℂ} {Δ : ℝ}
    (hH : H.IsHermitian)
    (h : ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin H) μ → μ = 0 ∨ (Δ : ℂ) ≤ μ)
    {v : EuclideanSpace ℂ n} (hv : v ∈ (LinearMap.ker (toEuclideanLin H))ᗮ) :
    Δ * ‖v‖ ^ 2 ≤ (⟪v, toEuclideanLin H v⟫_ℂ).re :=
  (isSymmetric_toEuclideanLin_iff.mpr hH).mul_norm_sq_le_re_inner_of_forall_hasEigenvalue h hv

/-- **The quadratic form above the kernel.** If a Hermitian matrix `H` is gapped at `0` with
gap `Δ`, then `Δ ‖v‖² ≤ Re ⟨v, H v⟩` for every `v` orthogonal to the kernel. -/
theorem IsGapped.mul_norm_sq_le_re_inner {H : Matrix n n ℂ} {Δ : ℝ} (hH : H.IsHermitian)
    (h : IsGapped H 0 Δ) {v : EuclideanSpace ℂ n}
    (hv : v ∈ (LinearMap.ker (toEuclideanLin H))ᗮ) :
    Δ * ‖v‖ ^ 2 ≤ (⟪v, toEuclideanLin H v⟫_ℂ).re :=
  mul_norm_sq_le_re_inner_of_hasEigenvalue hH (fun μ hμ ↦ by simpa using h.2 μ hμ) hv

/-- **The spectrum above the kernel, in quadratic form.** For a positive semidefinite matrix `H`,
every eigenvalue other than `0` is at least `Δ` exactly when `Δ ‖v‖² ≤ Re ⟨v, H v⟩` for every
`v` orthogonal to the kernel. No ground state is assumed: for a zero kernel both sides say
`H ≥ Δ`. -/
theorem forall_hasEigenvalue_iff_re_inner {H : Matrix n n ℂ} (hH : H.PosSemidef) {Δ : ℝ} :
    (∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin H) μ → μ = 0 ∨ (Δ : ℂ) ≤ μ) ↔
      ∀ v ∈ (LinearMap.ker (toEuclideanLin H))ᗮ,
        Δ * ‖v‖ ^ 2 ≤ (⟪v, toEuclideanLin H v⟫_ℂ).re :=
  (isPositive_toEuclideanLin_iff.mpr hH).forall_hasEigenvalue_iff_re_inner

/-- **The spectrum above the kernel, in norm form.** For a positive semidefinite matrix `H`,
every eigenvalue other than `0` is at least `Δ` exactly when `Δ ‖v‖ ≤ ‖H v‖` for every `v`
orthogonal to the kernel. No ground state is assumed. -/
theorem forall_hasEigenvalue_iff_norm {H : Matrix n n ℂ} (hH : H.PosSemidef) {Δ : ℝ} :
    (∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin H) μ → μ = 0 ∨ (Δ : ℂ) ≤ μ) ↔
      ∀ v ∈ (LinearMap.ker (toEuclideanLin H))ᗮ, Δ * ‖v‖ ≤ ‖toEuclideanLin H v‖ :=
  (isPositive_toEuclideanLin_iff.mpr hH).forall_hasEigenvalue_iff_norm

/-- The gap at `0` is a nonzero kernel together with the spectral bound above it. -/
theorem isGapped_zero_iff {H : Matrix n n ℂ} {Δ : ℝ} :
    IsGapped H 0 Δ ↔ groundSpace H 0 ≠ ⊥ ∧
      ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin H) μ → μ = 0 ∨ (Δ : ℂ) ≤ μ := by
  simp only [IsGapped, Complex.ofReal_zero, zero_add]

/-- **The gap above the kernel, in quadratic form.** A positive semidefinite matrix `H` is gapped
at `0` with gap `Δ` exactly when its kernel is nonzero and `Δ ‖v‖² ≤ Re ⟨v, H v⟩` for every `v`
orthogonal to the kernel. -/
theorem isGapped_zero_iff_inner {H : Matrix n n ℂ} (hH : H.PosSemidef) {Δ : ℝ} :
    IsGapped H 0 Δ ↔ groundSpace H 0 ≠ ⊥ ∧
      ∀ v ∈ (LinearMap.ker (toEuclideanLin H))ᗮ,
        Δ * ‖v‖ ^ 2 ≤ (⟪v, toEuclideanLin H v⟫_ℂ).re := by
  rw [isGapped_zero_iff, forall_hasEigenvalue_iff_re_inner hH]

/-- **The gap above the kernel, in norm form.** A positive semidefinite matrix `H` is gapped at
`0` with gap `Δ` exactly when its kernel is nonzero and `Δ ‖v‖ ≤ ‖H v‖` for every `v` orthogonal
to the kernel. -/
theorem isGapped_zero_iff_norm {H : Matrix n n ℂ} (hH : H.PosSemidef) {Δ : ℝ} :
    IsGapped H 0 Δ ↔ groundSpace H 0 ≠ ⊥ ∧
      ∀ v ∈ (LinearMap.ker (toEuclideanLin H))ᗮ, Δ * ‖v‖ ≤ ‖toEuclideanLin H v‖ := by
  rw [isGapped_zero_iff, forall_hasEigenvalue_iff_norm hH]

/-- If `0 ≤ A ≤ C` and the kernel of `A` lies in that of `C`, the two kernels agree. -/
theorem groundSpace_zero_eq_of_le {A C : Matrix n n ℂ} (hA : A.PosSemidef) (hAC : A ≤ C)
    (hker : groundSpace A 0 ≤ groundSpace C 0) : groundSpace C 0 = groundSpace A 0 := by
  refine le_antisymm (fun x hx ↦ ?_) hker
  rw [mem_groundSpace_iff_mulVec, Complex.ofReal_zero, zero_smul] at hx ⊢
  exact hA.mulVec_eq_zero_of_le hAC _ hx

/-- **Domination keeps the spectrum above the kernel.** If `0 ≤ A ≤ C`, the kernel of `A` lies
in that of `C`, and every eigenvalue of `A` other than `0` is at least `Δ`, then the same holds
for `C`. No ground state is assumed. For `t ≥ 0`, `A ≤ B`, and the kernel of `A` contained in
that of `B`, this applies to the interpolation `C = A + t (B - A)`. -/
theorem forall_hasEigenvalue_of_le {A C : Matrix n n ℂ} {Δ : ℝ} (hA : A.PosSemidef)
    (hAC : A ≤ C) (hker : groundSpace A 0 ≤ groundSpace C 0)
    (h : ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin A) μ → μ = 0 ∨ (Δ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin C) μ → μ = 0 ∨ (Δ : ℂ) ≤ μ := by
  have hD := Matrix.le_iff.mp hAC
  have hC : C.PosSemidef := by simpa using hA.add hD
  have heq := groundSpace_zero_eq_of_le hA hAC hker
  rw [forall_hasEigenvalue_iff_re_inner hA] at h
  rw [forall_hasEigenvalue_iff_re_inner hC]
  refine fun v hv ↦ (h v (by rwa [← groundSpace_zero, ← heq, groundSpace_zero])).trans ?_
  have hDv := (isPositive_toEuclideanLin_iff.mpr hD).re_inner_nonneg_right v
  rwa [map_sub, LinearMap.sub_apply, inner_sub_right, map_sub, sub_nonneg] at hDv

/-- **Domination keeps the gap.** If `0 ≤ A ≤ C`, the kernel of `A` lies in that of `C`, and `A`
is gapped at `0` with gap `Δ`, then so is `C`, with the same ground space
(`groundSpace_zero_eq_of_le`). For `t ≥ 0`, `A ≤ B`, and the kernel of `A` contained in that of
`B`, this applies to `C = A + t (B - A)`. -/
theorem IsGapped.of_le {A C : Matrix n n ℂ} {Δ : ℝ} (hA : A.PosSemidef) (hAC : A ≤ C)
    (hker : groundSpace A 0 ≤ groundSpace C 0) (h : IsGapped A 0 Δ) : IsGapped C 0 Δ := by
  rw [isGapped_zero_iff] at h ⊢
  exact ⟨groundSpace_zero_eq_of_le hA hAC hker ▸ h.1, forall_hasEigenvalue_of_le hA hAC hker h.2⟩

/-- **Gap transfer along a comparison.** If positive semidefinite matrices satisfy
`κ A ≤ B ≤ C A` with `κ, C > 0` and every eigenvalue of `A` other than `0` is at least
`γ > 0`, then every eigenvalue of `B` other than `0` is at least `κ γ`. CPGSV21,
arXiv:2011.12127, Section IV.C, lines 1995–2007 and 2183–2187. -/
theorem forall_hasEigenvalue_of_smul_le_of_le_smul {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) {κ C γ : ℝ} (hκ : 0 < κ) (hC : 0 < C) (hγ : 0 < γ)
    (hLower : (κ : ℂ) • A ≤ B) (hUpper : B ≤ (C : ℂ) • A)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin A) μ → μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin B) μ →
      μ = 0 ∨ ((κ * γ : ℝ) : ℂ) ≤ μ := by
  have h1 := toEuclideanLin_le_toEuclideanLin_iff.mpr hLower
  have h2 := toEuclideanLin_le_toEuclideanLin_iff.mpr hUpper
  rw [map_smul] at h1 h2
  simpa only [div_one] using
    (isPositive_toEuclideanLin_iff.mpr hA).forall_hasEigenvalue_of_smul_le_of_le_smul
      (isPositive_toEuclideanLin_iff.mpr hB) (b := 1) hκ zero_lt_one hC hγ
      (by simpa only [Complex.ofReal_one, one_smul] using h1)
      (by simpa only [Complex.ofReal_one, one_smul] using h2) hGap

/-! ### Continuity and compactness -/

/-- **Persistence of the spectrum above the kernel.** Let `H x` be positive semidefinite
matrices depending on a parameter, continuous at `x₀`, whose kernel projections are continuous
at `x₀`. If every eigenvalue of `H x₀` other than `0` is at least `Δ`, then for every `Δ' < Δ`
every eigenvalue of `H x` other than `0` is at least `Δ'` near `x₀`. No ground state is assumed.
arXiv:1010.3732, Appendix A, finite-window gap continuity. -/
theorem eventually_forall_hasEigenvalue {X : Type*} [TopologicalSpace X]
    {H : X → Matrix n n ℂ} {x₀ : X} (hH : ContinuousAt H x₀)
    (hpos : ∀ᶠ x in 𝓝 x₀, (H x).PosSemidef)
    (hK : ContinuousAt (fun x ↦ (groundSpace (H x) 0).starProjection) x₀) {Δ Δ' : ℝ}
    (hgap : ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin (H x₀)) μ → μ = 0 ∨ (Δ : ℂ) ≤ μ)
    (hΔ' : Δ' < Δ) :
    ∀ᶠ x in 𝓝 x₀,
      ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin (H x)) μ → μ = 0 ∨ (Δ' : ℂ) ≤ μ := by
  rcases le_or_gt Δ 0 with hΔ | hΔ
  · filter_upwards [hpos] with x hx
    refine (forall_hasEigenvalue_iff_norm hx).mpr fun v _ ↦ ?_
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (norm_nonneg v)).trans (norm_nonneg _)
  have hT : ContinuousAt (fun x ↦ toEuclideanCLM (n := n) (𝕜 := ℂ) (H x)) x₀ :=
    ((toEuclideanCLM (n := n) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
      ).continuousAt.comp hH
  have hgap₀ := (forall_hasEigenvalue_iff_norm hpos.self_of_nhds).mp hgap
  have hev := ContinuousLinearMap.eventually_norm_gap_on_orthogonal
    (fun x ↦ toEuclideanCLM (n := n) (𝕜 := ℂ) (H x)) (fun x ↦ groundSpace (H x) 0) hT hK
    (groundSpace_zero (H x₀)).le hΔ (max_lt hΔ' (half_lt_self hΔ))
    (fun v hv ↦ hgap₀ v (by rwa [groundSpace_zero] at hv))
  filter_upwards [hpos, hev] with x hx hxgap
  have hmax := (forall_hasEigenvalue_iff_norm hx).mpr fun v hv ↦
    hxgap v (by rwa [groundSpace_zero])
  exact fun μ hμ ↦ (hmax μ hμ).imp_right
    (Complex.real_le_real.mpr (le_max_left Δ' (Δ / 2))).trans

/-- **Persistence of the gap.** Let `H x` be positive semidefinite matrices depending on a
parameter, continuous at `x₀`, whose kernel projections are continuous at `x₀`. If `H x₀` is
gapped at `0` with gap `Δ`, then every smaller gap `Δ' < Δ` holds for `H x` near `x₀`.
arXiv:1010.3732, Appendix A, finite-window gap continuity. -/
theorem eventually_isGapped_zero {X : Type*} [TopologicalSpace X] {H : X → Matrix n n ℂ}
    {x₀ : X} (hH : ContinuousAt H x₀) (hpos : ∀ᶠ x in 𝓝 x₀, (H x).PosSemidef)
    (hK : ContinuousAt (fun x ↦ (groundSpace (H x) 0).starProjection) x₀) {Δ Δ' : ℝ}
    (hgap : IsGapped (H x₀) 0 Δ) (hΔ' : Δ' < Δ) :
    ∀ᶠ x in 𝓝 x₀, IsGapped (H x) 0 Δ' := by
  rw [isGapped_zero_iff] at hgap
  have hne : ∀ᶠ x in 𝓝 x₀, groundSpace (H x) 0 ≠ ⊥ := by
    have h0 : (groundSpace (H x₀) 0).starProjection ≠ 0 := fun h ↦ by
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hgap.1
      exact hv0 (by rw [← Submodule.starProjection_eq_self_iff.mpr hv, h,
        _root_.zero_apply])
    filter_upwards [hK.eventually_ne h0] with x hx hbot
    exact hx (by rw [hbot, Submodule.starProjection_bot])
  filter_upwards [hne, eventually_forall_hasEigenvalue hH hpos hK hgap.2 hΔ'] with x hxne hx
  exact isGapped_zero_iff.mpr ⟨hxne, hx⟩

/-- **A uniform gap on a compact parameter set.** If every point of a compact set `S` has a
neighbourhood on which the matrices `H y N` are gapped at the energies `E y N` with one positive
gap for all `N` beyond one threshold, then one gap and one threshold serve for all of `S`.
arXiv:1010.3732, Appendix A, the compactness step. -/
theorem _root_.IsCompact.exists_uniform_isGapped {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsCompact S) {m : ℕ → Type*} [∀ N, Fintype (m N)] [∀ N, DecidableEq (m N)]
    (H : X → ∀ N, Matrix (m N) (m N) ℂ) (E : X → ℕ → ℝ)
    (hlocal : ∀ x ∈ S, ∃ Δ : ℝ, 0 < Δ ∧ ∃ N₀ : ℕ,
      ∀ᶠ y in 𝓝 x, ∀ N, N₀ ≤ N → IsGapped (H y N) (E y N) Δ) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∃ N₀ : ℕ, ∀ x ∈ S, ∀ N, N₀ ≤ N → IsGapped (H x N) (E x N) Δ :=
  hS.exists_uniform_pos_nat_bounds (fun Δ N₀ x ↦ ∀ N, N₀ ≤ N → IsGapped (H x N) (E x N) Δ)
    (fun hle h N hN ↦ (h N hN).mono hle) (fun hle h N hN ↦ h N (hle.trans hN)) hlocal

/-- The spectral bound above the kernel is weaker for a smaller gap. -/
theorem forall_hasEigenvalue_mono {H : Matrix n n ℂ} {Δ Δ' : ℝ} (hΔ : Δ' ≤ Δ)
    (h : ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin H) μ → μ = 0 ∨ (Δ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin H) μ → μ = 0 ∨ (Δ' : ℂ) ≤ μ :=
  fun μ hμ ↦ (h μ hμ).imp_right (Complex.real_le_real.mpr hΔ).trans

/-- A positive semidefinite matrix has a positive gap above its kernel: every nonzero
eigenvalue is at least some `Δ > 0`. -/
theorem exists_pos_forall_hasEigenvalue {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    ∃ Δ : ℝ, 0 < Δ ∧
      ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin H) μ → μ = 0 ∨ (Δ : ℂ) ≤ μ := by
  obtain ⟨Δ, hΔ, h⟩ := (toEuclideanLin H).exists_pos_mul_norm_le_of_mem_orthogonal_ker
  exact ⟨Δ, hΔ, (forall_hasEigenvalue_iff_norm hH).mpr h⟩

/-- An orthogonal projection has eigenvalues `0` and `1` only, so its gap above the kernel
is `1`. -/
theorem forall_hasEigenvalue_one_of_isStarProjection {P : Matrix n n ℂ}
    (hP : IsStarProjection P) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin P) μ → μ = 0 ∨ (1 : ℂ) ≤ μ := by
  intro μ hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have h1 : toEuclideanLin P v = μ • v := hv.apply_eq_smul
  have h2 : toEuclideanLin P (toEuclideanLin P v) = toEuclideanLin P v := by
    simp only [← coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe,
      ← mul_apply_eq_comp, ← map_mul, hP.isIdempotentElem.eq]
  rw [h1, map_smul, h1, smul_smul] at h2
  have h3 : (μ * μ - μ) • v = 0 := by rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h | h
  · have : μ * (μ - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h1'
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1').ge
  · exact absurd h hv.2

/-- **A uniform gap above the kernel on a compact parameter set.** For a continuous family of
positive semidefinite matrices whose kernel projections depend continuously on the parameter,
one `Δ > 0` bounds every nonzero eigenvalue from below on a compact set of parameters. -/
theorem _root_.IsCompact.exists_uniform_forall_hasEigenvalue {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsCompact S) {H : X → Matrix n n ℂ} (hH : Continuous H)
    (hpos : ∀ x, (H x).PosSemidef)
    (hK : Continuous fun x ↦ (groundSpace (H x) 0).starProjection) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ x ∈ S,
      ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin (H x)) μ → μ = 0 ∨ (Δ : ℂ) ≤ μ := by
  have hcont : Continuous fun x ↦ toEuclideanCLM (𝕜 := ℂ) (H x) :=
    (LinearMap.continuous_of_finiteDimensional
      (toEuclideanCLM (n := n) (𝕜 := ℂ)).toAlgEquiv.toLinearMap).comp hH
  have hK' : Continuous fun x ↦
      (LinearMap.ker (toEuclideanCLM (𝕜 := ℂ) (H x)).toLinearMap).starProjection := by
    simpa only [groundSpace_zero, coe_toEuclideanCLM_eq_toEuclideanLin] using hK
  obtain ⟨Δ, hΔ, h⟩ := ContinuousLinearMap.exists_uniform_norm_gap_of_compact
    (fun x ↦ toEuclideanCLM (𝕜 := ℂ) (H x)) hcont hK' hS
  exact ⟨Δ, hΔ, fun x hx ↦ (forall_hasEigenvalue_iff_norm (hpos x)).mpr (h x hx)⟩

end ManyBody
