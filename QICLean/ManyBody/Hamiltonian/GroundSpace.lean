/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixReindexEuclidean
import QICLean.Analysis.PositiveGapUniqueness
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order

/-!
# Ground spaces and spectral gaps

For a matrix `H` and an energy `E₀`, the ground space is the eigenspace of `H` at `E₀`.
The matrix is gapped at `E₀` with gap `Δ` when this eigenspace is nonzero and every other
eigenvalue is real and at least `E₀ + Δ`; for `0 < Δ` this makes `E₀` the ground energy and
`Δ` a lower bound on the spectral gap above it. Both notions are stated for any finite index
type, so they apply to the Hamiltonian of an interaction as they stand.

The gap condition used by the area-law and polynomial-PEPS theorems is a unit eigenvector `Ω`
at `E₀` with the operator inequality `H - E₀ I ≥ Δ (I - |Ω⟩⟨Ω|)`. For `0 < Δ` it is
equivalent to `H` being Hermitian and gapped at `E₀` with ground space the line through `Ω`
(`ManyBody.isGapped_and_groundSpace_eq_span_iff`).

Moved from TNLean, `TNLean/Lattice/GaussianFilteredTerm.lean` (`groundEigenspace`,
`mem_groundEigenspace_iff`) at commit `71c1185e9352a3b5237b37a6840640751da6ca2d`. Changes:
`groundSpace` is a definition, not an abbreviation. `ManyBody.IsGapped` is new: the
eigenvalue form of `Lattice/LowEnergyBasis*` is `ManyBody.isGapped_iff_eigenvalues`, and
TNLean's `Matrix.IsGappedGroundState` is the left side of
`ManyBody.isGapped_and_groundSpace_eq_span_iff`.

## Main definitions

* `ManyBody.groundSpace` — the eigenspace at an energy.
* `ManyBody.IsGapped` — a nonzero ground space and every other eigenvalue at least `E₀ + Δ`.

## Main results

* `ManyBody.mem_groundSpace_iff_mulVec` — membership as an equation of coordinate vectors.
* `ManyBody.isGapped_iff_eigenvalues` — for Hermitian `H`, the gap in terms of the eigenvalues.
* `ManyBody.IsGapped.posSemidef_sub_smul_one` — a gapped Hermitian matrix with ground space the
  line through a unit vector `Ω` satisfies `H - E₀ I ≥ Δ (I - |Ω⟩⟨Ω|)`, for any `Δ`.
* `ManyBody.mulVec_eq_of_groundSpace_eq_span` — a vector spanning the ground space is an
  eigenvector at `E₀`.
* `ManyBody.isGapped_and_groundSpace_eq_span_iff` — the operator form of a gapped unique
  ground state.
* `ManyBody.groundSpace_eq_map_of_intertwine`, `ManyBody.isGapped_iff_of_intertwine` — a linear
  equivalence intertwining two matrices carries the ground space and preserves the gap.
* `ManyBody.groundSpace_reindex`, `ManyBody.isGapped_reindex_iff` and their `submatrix` forms,
  `ManyBody.groundSpace_unitary_conj` and `ManyBody.isGapped_unitary_conj_iff` — relabelling the
  basis and unitary conjugation carry the ground space and preserve the gap, for every `Δ`.
* `ManyBody.IsGapped.mono`, `ManyBody.IsGapped.posSemidef_sub_ground` — a smaller gap, and
  `H ≥ E₀` for a Hermitian `H` with a nonnegative gap.
* `ManyBody.groundSpace_smul`, `ManyBody.IsGapped.smul`, `ManyBody.groundSpace_sub_smul_one`,
  `ManyBody.IsGapped.sub_smul_one` — scaling `H` by `c > 0` scales the ground energy and the gap
  by `c`, and shifting `H` by `-a` shifts the ground energy by `-a`, for every `Δ`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `00-introduction.tex`, lines 44–47 (`thm:area`).
* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `00-introduction.tex`, lines 47–50 (`eq:global-gap`).
-/

open Matrix
open scoped InnerProductSpace ComplexOrder

/-- The eigenvalues of a Hermitian matrix, as an operator on the Euclidean space, are its
eigenvalues `hH.eigenvalues k`. -/
theorem Matrix.IsHermitian.hasEigenvalue_toEuclideanLin_iff {n : Type*} [Fintype n]
    [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {μ : ℂ} :
    Module.End.HasEigenvalue (toEuclideanLin H) μ ↔ ∃ k, μ = hH.eigenvalues k := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLpLin,
    hH.spectrum_eq_image_range]
  simp [eq_comm]

open scoped MatrixOrder in
/-- A Hermitian matrix dominates any lower bound of its eigenvalues: if `a ≤ λₖ` for every
eigenvalue, then `H - a ≥ 0`. -/
theorem Matrix.IsHermitian.posSemidef_sub_smul_one_of_le_eigenvalues {n : Type*} [Fintype n]
    [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {a : ℝ}
    (ha : ∀ i, a ≤ hH.eigenvalues i) : (H - (a : ℂ) • 1).PosSemidef := by
  have h : algebraMap ℝ (Matrix n n ℂ) a ≤ H := by
    rw [algebraMap_le_iff_le_spectrum (a := H) hH.isSelfAdjoint]
    intro x hx
    rw [hH.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ha i
  rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] at h
  simpa [Complex.coe_smul] using h

namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ground space of `H` at the energy `E₀`: the eigenspace of `H` at `E₀`, as a subspace of
the Euclidean space. Area law, `00-introduction.tex`, lines 44–47. -/
noncomputable def groundSpace (H : Matrix n n ℂ) (E₀ : ℝ) : Submodule ℂ (EuclideanSpace ℂ n) :=
  Module.End.eigenspace (toEuclideanLin H) (E₀ : ℂ)

theorem mem_groundSpace_iff {H : Matrix n n ℂ} {E₀ : ℝ} {ψ : EuclideanSpace ℂ n} :
    ψ ∈ groundSpace H E₀ ↔ toEuclideanLin H ψ = (E₀ : ℂ) • ψ :=
  Module.End.mem_eigenspace_iff

/-- A vector lies in the ground space exactly when `H` acts on its coordinates as `E₀`. -/
theorem mem_groundSpace_iff_mulVec {H : Matrix n n ℂ} {E₀ : ℝ} {ψ : EuclideanSpace ℂ n} :
    ψ ∈ groundSpace H E₀ ↔ H *ᵥ WithLp.ofLp ψ = (E₀ : ℂ) • WithLp.ofLp ψ := by
  rw [mem_groundSpace_iff, ← (WithLp.ofLp_injective 2).eq_iff]
  simp [toLpLin_apply]

/-- `H` is gapped at `E₀` with gap `Δ`: its ground space at `E₀` is nonzero, and every other
eigenvalue is real and at least `E₀ + Δ`. For `0 < Δ` this makes `E₀` the ground energy and
`Δ` a lower bound on the gap. Area law, `00-introduction.tex`, lines 44–47; polynomial-PEPS,
`eq:global-gap`. -/
def IsGapped (H : Matrix n n ℂ) (E₀ Δ : ℝ) : Prop :=
  groundSpace H E₀ ≠ ⊥ ∧
    ∀ μ : ℂ, Module.End.HasEigenvalue (toEuclideanLin H) μ → μ = E₀ ∨ ((E₀ + Δ : ℝ) : ℂ) ≤ μ

/-- For a Hermitian matrix, the gap condition in terms of its eigenvalues. Without the first
conjunct the second is only a spectral lower bound. -/
theorem isGapped_iff_eigenvalues {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ Δ : ℝ} :
    IsGapped H E₀ Δ ↔ groundSpace H E₀ ≠ ⊥ ∧
      ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k := by
  refine and_congr_right fun _ ↦ ?_
  simp only [hH.hasEigenvalue_toEuclideanLin_iff]
  constructor
  · intro h k
    exact (h _ ⟨k, rfl⟩).imp Complex.ofReal_inj.mp Complex.real_le_real.mp
  · rintro h μ ⟨k, rfl⟩
    exact (h k).imp (congrArg _) Complex.real_le_real.mpr

/-- The action of the gap defect `H - E₀ I - Δ (I - |Ω⟩⟨Ω|)` on a vector. -/
private theorem toEuclideanLin_gap_apply (H : Matrix n n ℂ) (E₀ Δ : ℝ)
    (Ω ψ : EuclideanSpace ℂ n) :
    toEuclideanLin (H - (E₀ : ℂ) • 1 -
        (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))) ψ =
      toEuclideanLin H ψ - (E₀ : ℂ) • ψ - (Δ : ℂ) • (ψ - ⟪Ω, ψ⟫_ℂ • Ω) := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, toLpLin_one,
    LinearMap.id_apply, toEuclideanLin_vecMulVec_star_self_apply]

/-- A vector spanning the ground space is an eigenvector of `H` at `E₀`. -/
theorem mulVec_eq_of_groundSpace_eq_span {H : Matrix n n ℂ} {E₀ : ℝ}
    {Ω : EuclideanSpace ℂ n} (hspan : groundSpace H E₀ = Submodule.span ℂ {Ω}) :
    H *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω :=
  mem_groundSpace_iff_mulVec.mp (hspan ▸ Submodule.mem_span_singleton_self Ω)

/-- **The operator gap inequality.** If `H` is Hermitian and gapped at `E₀` with gap `Δ`, and
its ground space is the line through the unit vector `Ω`, then
`H - E₀ I ≥ Δ (I - |Ω⟩⟨Ω|)`. No sign of `Δ` is needed. Area law, `00-introduction.tex`,
lines 44–47 (`thm:area`); polynomial-PEPS, `eq:global-gap`. -/
theorem IsGapped.posSemidef_sub_smul_one {H : Matrix n n ℂ} {E₀ Δ : ℝ}
    {Ω : EuclideanSpace ℂ n} (hH : H.IsHermitian) (hΩ : ‖Ω‖ = 1) (hgap : IsGapped H E₀ Δ)
    (hspan : groundSpace H E₀ = Submodule.span ℂ {Ω}) :
    (H - (E₀ : ℂ) • (1 : Matrix n n ℂ) - (Δ : ℂ) •
      (1 - vecMulVec (fun x ↦ Ω x) (star (fun x ↦ Ω x)))).PosSemidef := by
  have hT := isSymmetric_toEuclideanLin_iff.mpr hH
  have hlin : toEuclideanLin H Ω = (E₀ : ℂ) • Ω :=
    mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Ω)
  rw [← isPositive_toEuclideanLin_iff]
  refine ⟨isSymmetric_toEuclideanLin_iff.mpr (hH.gap E₀ Δ Ω), fun ψ ↦ ?_⟩
  set G := toEuclideanLin (H - (E₀ : ℂ) • 1 -
    (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))))
  have hG : G.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr (hH.gap E₀ Δ Ω)
  let b := hH.eigenvectorBasis
  have hTb (k : n) : toEuclideanLin H (b k) = ((hH.eigenvalues k : ℝ) : ℂ) • b k := by
    apply WithLp.ofLp_injective 2
    rw [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul]
    exact (hH.mulVec_eigenvectorBasis k).trans (RCLike.real_smul_eq_coe_smul _ _)
  -- Every eigenvector of `H` is an eigenvector of the gap defect, with eigenvalue `≥ 0`.
  have hGb (k : n) : ∃ ν : ℝ, 0 ≤ ν ∧ G (b k) = (ν : ℂ) • b k := by
    by_cases hk : hH.eigenvalues k = E₀
    · have hmem : b k ∈ groundSpace H E₀ := mem_groundSpace_iff.mpr (by rw [hTb, hk])
      rw [hspan] at hmem
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
      have hinner : ⟪Ω, b k⟫_ℂ = a := by
        rw [← ha, inner_smul_right, inner_self_eq_norm_sq_to_K, hΩ]
        simp
      refine ⟨0, le_rfl, ?_⟩
      rw [toEuclideanLin_gap_apply, hTb, hk, hinner, ha]
      simp
    · have hne : b k ≠ 0 := b.orthonormal.ne_zero k
      have hev : Module.End.HasEigenvalue (toEuclideanLin H) (hH.eigenvalues k : ℂ) :=
        Module.End.hasEigenvalue_of_hasEigenvector
          ⟨Module.End.mem_eigenspace_iff.mpr (hTb k), hne⟩
      have hge : E₀ + Δ ≤ hH.eigenvalues k := by
        rcases hgap.2 _ hev with h | h
        · exact absurd (Complex.ofReal_inj.mp h) hk
        · exact Complex.real_le_real.mp h
      have horth : ⟪Ω, b k⟫_ℂ = 0 := by
        have h := hT Ω (b k)
        rw [hlin, hTb, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
        have h' : ((hH.eigenvalues k : ℂ) - E₀) * ⟪Ω, b k⟫_ℂ = 0 := by
          linear_combination -h
        exact (mul_eq_zero.mp h').resolve_left
          (sub_ne_zero.mpr (fun h ↦ hk (Complex.ofReal_inj.mp h)))
      refine ⟨hH.eigenvalues k - E₀ - Δ, by linarith, ?_⟩
      rw [toEuclideanLin_gap_apply, hTb, horth, zero_smul, sub_zero]
      push_cast
      module
  choose ν hν hGν using hGb
  rw [← b.sum_inner_mul_inner (G ψ) ψ, map_sum]
  refine Finset.sum_nonneg fun k _ ↦ ?_
  rw [hG ψ (b k), hGν k, inner_smul_right, mul_assoc, RCLike.re_to_complex,
    Complex.re_ofReal_mul]
  exact mul_nonneg (hν k) (by rw [← RCLike.re_to_complex, inner_mul_symm_re_eq_norm]; positivity)

/-- **A gapped unique ground state.** For `0 < Δ`, a unit vector `Ω` with `H Ω = E₀ Ω` and
`H - E₀ I ≥ Δ (I - |Ω⟩⟨Ω|)` is the same as a Hermitian `H`, gapped at `E₀` with gap `Δ`, whose
ground space is the line through the unit vector `Ω`. The left side is TNLean's
`Matrix.IsGappedGroundState H E₀ Ω Δ`. Area law, `00-introduction.tex`, lines 44–47;
polynomial-PEPS, `eq:global-gap`. -/
theorem isGapped_and_groundSpace_eq_span_iff {H : Matrix n n ℂ} {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (Ω : EuclideanSpace ℂ n) :
    (‖Ω‖ = 1 ∧ toEuclideanCLM (n := n) (𝕜 := ℂ) H Ω = (E₀ : ℂ) • Ω ∧
      (H - (E₀ : ℂ) • (1 : Matrix n n ℂ) - (Δ : ℂ) •
        (1 - vecMulVec (fun x ↦ Ω x) (star (fun x ↦ Ω x)))).PosSemidef) ↔
    H.IsHermitian ∧ ‖Ω‖ = 1 ∧ IsGapped H E₀ Δ ∧ groundSpace H E₀ = Submodule.span ℂ {Ω} := by
  have hCLM (x : EuclideanSpace ℂ n) :
      toEuclideanCLM (n := n) (𝕜 := ℂ) H x = toEuclideanLin H x := by
    rw [← coe_toEuclideanCLM_eq_toEuclideanLin]
    rfl
  simp only [hCLM]
  constructor
  · rintro ⟨hΩ, hlin, hgap⟩
    have hH : H.IsHermitian := by
      have hP : (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).IsHermitian := by
        rw [IsHermitian, conjTranspose_vecMulVec, star_star]
      have hr (r : ℝ) : IsSelfAdjoint (r : ℂ) := Complex.conj_ofReal r
      simpa only [sub_add_cancel] using (hgap.isHermitian.add
        ((isHermitian_one.sub hP).smul (hr Δ))).add (isHermitian_one.smul (hr E₀))
    have hspan : groundSpace H E₀ = Submodule.span ℂ {Ω} :=
      hgap.eigenspace_eq_span_of_gap hΔ hΩ (mem_groundSpace_iff_mulVec.mp
        (mem_groundSpace_iff.mpr hlin))
    refine ⟨hH, hΩ, ⟨?_, fun μ hμ ↦ ?_⟩, hspan⟩
    · rw [hspan, Ne, Submodule.span_singleton_eq_bot]
      intro h
      rw [h, norm_zero] at hΩ
      exact zero_ne_one hΩ
    by_cases hμE : μ = E₀
    · exact Or.inl hμE
    right
    have hT := isSymmetric_toEuclideanLin_iff.mpr hH
    obtain ⟨ψ, hψ⟩ := hμ.exists_hasEigenvector
    have hreal : μ.im = 0 := Complex.conj_eq_iff_im.mp (hT.conj_eigenvalue_eq_self hμ)
    have horth : ⟪Ω, ψ⟫_ℂ = 0 := by
      have h := hT Ω ψ
      rw [hlin, hψ.apply_eq_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
      have h' : (μ - E₀) * ⟪Ω, ψ⟫_ℂ = 0 := by linear_combination -h
      exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hμE)
    have hre : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re = μ.re * ‖ψ‖ ^ 2 := by
      rw [hψ.apply_eq_smul, inner_smul_right, inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]
    have hg := hgap.gap_le ψ
    rw [hre, horth, norm_zero] at hg
    have hpos : 0 < ‖ψ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hψ.2) 2
    rw [Complex.le_def]
    refine ⟨?_, by simp [hreal]⟩
    simp only [Complex.ofReal_re]
    nlinarith
  · rintro ⟨hH, hΩ, hgap, hspan⟩
    exact ⟨hΩ, mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Ω),
      hgap.posSemidef_sub_smul_one hH hΩ hspan⟩

/-! ### Transport along an intertwining equivalence -/

section Intertwine

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- If a linear equivalence `f` of Euclidean spaces satisfies `H' f = f H`, it carries the
ground space of `H` onto that of `H'`. -/
theorem groundSpace_eq_map_of_intertwine (f : EuclideanSpace ℂ n ≃ₗ[ℂ] EuclideanSpace ℂ m)
    {H : Matrix n n ℂ} {H' : Matrix m m ℂ}
    (h : ∀ ψ, toEuclideanLin H' (f ψ) = f (toEuclideanLin H ψ)) (E₀ : ℝ) :
    groundSpace H' E₀ = (groundSpace H E₀).map (f : EuclideanSpace ℂ n →ₗ[ℂ] _) :=
  Module.End.eigenspace_eq_map_of_intertwine f _ _ h _

/-- If a linear equivalence `f` of Euclidean spaces satisfies `H' f = f H`, then `H'` and `H`
have the same eigenvalues. -/
theorem hasEigenvalue_iff_of_intertwine (f : EuclideanSpace ℂ n ≃ₗ[ℂ] EuclideanSpace ℂ m)
    {H : Matrix n n ℂ} {H' : Matrix m m ℂ}
    (h : ∀ ψ, toEuclideanLin H' (f ψ) = f (toEuclideanLin H ψ)) (μ : ℂ) :
    Module.End.HasEigenvalue (toEuclideanLin H') μ ↔
      Module.End.HasEigenvalue (toEuclideanLin H) μ := by
  rw [Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff,
    Module.End.eigenspace_eq_map_of_intertwine f _ _ h, Ne, Ne, Submodule.map_eq_bot_iff]

/-- If a linear equivalence `f` of Euclidean spaces satisfies `H' f = f H`, then `H'` is
gapped exactly when `H` is, for every `Δ`. -/
theorem isGapped_iff_of_intertwine (f : EuclideanSpace ℂ n ≃ₗ[ℂ] EuclideanSpace ℂ m)
    {H : Matrix n n ℂ} {H' : Matrix m m ℂ}
    (h : ∀ ψ, toEuclideanLin H' (f ψ) = f (toEuclideanLin H ψ)) {E₀ Δ : ℝ} :
    IsGapped H' E₀ Δ ↔ IsGapped H E₀ Δ := by
  simp only [IsGapped, hasEigenvalue_iff_of_intertwine f h, groundSpace_eq_map_of_intertwine f h,
    Ne, Submodule.map_eq_bot_iff]

end Intertwine

/-! ### Relabelling the basis -/

section Reindex

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A vector lies in the ground space of the relabelled matrix exactly when the relabelled
vector lies in the ground space of `H`. -/
theorem mem_groundSpace_reindex_iff (e : n ≃ m) {H : Matrix n n ℂ} {E₀ : ℝ}
    {ψ : EuclideanSpace ℂ m} :
    ψ ∈ groundSpace (reindex e e H) E₀ ↔
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm ψ ∈ groundSpace H E₀ :=
  mem_eigenspace_toEuclideanLin_reindex_iff e H _ ψ

/-- The ground space of the relabelled matrix is the image of the ground space under the
induced isometry. -/
theorem groundSpace_reindex (e : n ≃ m) (H : Matrix n n ℂ) (E₀ : ℝ) :
    groundSpace (reindex e e H) E₀ =
      (groundSpace H E₀).map
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearEquiv :
          EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m) :=
  groundSpace_eq_map_of_intertwine _ (toEuclideanLin_reindex_piLpCongrLeft e H) E₀

/-- A ground space spanned by `Ω` is carried to the line through the relabelled `Ω`. -/
theorem groundSpace_reindex_eq_span (e : n ≃ m) {H : Matrix n n ℂ} {E₀ : ℝ}
    {Ω : EuclideanSpace ℂ n} (hspan : groundSpace H E₀ = Submodule.span ℂ {Ω}) :
    groundSpace (reindex e e H) E₀ =
      Submodule.span ℂ {LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e Ω} := by
  rw [groundSpace_reindex, hspan, Submodule.map_span, Set.image_singleton]
  rfl

/-- Relabelling the basis preserves the gap, for every `Δ`. -/
theorem isGapped_reindex_iff (e : n ≃ m) {H : Matrix n n ℂ} {E₀ Δ : ℝ} :
    IsGapped (reindex e e H) E₀ Δ ↔ IsGapped H E₀ Δ :=
  isGapped_iff_of_intertwine _ (toEuclideanLin_reindex_piLpCongrLeft e H)

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
private theorem submatrix_eq_reindex (e : m ≃ n) (H : Matrix n n ℂ) :
    H.submatrix e e = reindex e.symm e.symm H := by
  simp [reindex_apply]

/-- The ground space of `H.submatrix e e` is the image of the ground space of `H`. -/
theorem groundSpace_submatrix (e : m ≃ n) (H : Matrix n n ℂ) (E₀ : ℝ) :
    groundSpace (H.submatrix e e) E₀ =
      (groundSpace H E₀).map
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).toLinearEquiv :
          EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m) := by
  rw [submatrix_eq_reindex, groundSpace_reindex]

/-- A ground space spanned by `Ω` is carried to the line through the relabelled `Ω`. -/
theorem groundSpace_submatrix_eq_span (e : m ≃ n) {H : Matrix n n ℂ} {E₀ : ℝ}
    {Ω : EuclideanSpace ℂ n} (hspan : groundSpace H E₀ = Submodule.span ℂ {Ω}) :
    groundSpace (H.submatrix e e) E₀ =
      Submodule.span ℂ {LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm Ω} := by
  rw [submatrix_eq_reindex]
  exact groundSpace_reindex_eq_span e.symm hspan

/-- Restricting along an equivalence of bases preserves the gap, for every `Δ`. -/
theorem isGapped_submatrix_iff (e : m ≃ n) {H : Matrix n n ℂ} {E₀ Δ : ℝ} :
    IsGapped (H.submatrix e e) E₀ Δ ↔ IsGapped H E₀ Δ := by
  rw [submatrix_eq_reindex, isGapped_reindex_iff]

end Reindex

/-! ### Unitary conjugation -/

section Unitary

/-- A unitary matrix as a linear equivalence of the Euclidean space. -/
private noncomputable def unitaryLinearEquiv {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) :
    EuclideanSpace ℂ n ≃ₗ[ℂ] EuclideanSpace ℂ n :=
  LinearEquiv.ofLinearMap (toEuclideanLin U) (toEuclideanLin Uᴴ)
    (by rw [← toLpLin_mul_same, ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hU,
      toLpLin_one])
    (by rw [← toLpLin_mul_same, ← star_eq_conjTranspose, mem_unitaryGroup_iff'.mp hU,
      toLpLin_one])

private theorem toEuclideanLin_unitary_conj {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (H : Matrix n n ℂ) (ψ : EuclideanSpace ℂ n) :
    toEuclideanLin (U * H * Uᴴ) (unitaryLinearEquiv hU ψ) =
      unitaryLinearEquiv hU (toEuclideanLin H ψ) := by
  have hback : toEuclideanLin Uᴴ (toEuclideanLin U ψ) = ψ := by
    rw [← LinearMap.comp_apply, ← toLpLin_mul_same, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff'.mp hU, toLpLin_one, LinearMap.id_apply]
  change toEuclideanLin (U * H * Uᴴ) (toEuclideanLin U ψ) = toEuclideanLin U (toEuclideanLin H ψ)
  rw [toLpLin_mul_same, toLpLin_mul_same, LinearMap.comp_apply, LinearMap.comp_apply, hback]

/-- The ground space of `U H Uᴴ` is the image of the ground space of `H` under `U`. -/
theorem groundSpace_unitary_conj {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (H : Matrix n n ℂ) (E₀ : ℝ) :
    groundSpace (U * H * Uᴴ) E₀ = (groundSpace H E₀).map (toEuclideanLin U) :=
  groundSpace_eq_map_of_intertwine (unitaryLinearEquiv hU) (toEuclideanLin_unitary_conj hU H) E₀

/-- A ground space spanned by `Ω` is carried to the line through `U Ω`. -/
theorem groundSpace_unitary_conj_eq_span {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    {H : Matrix n n ℂ} {E₀ : ℝ} {Ω : EuclideanSpace ℂ n}
    (hspan : groundSpace H E₀ = Submodule.span ℂ {Ω}) :
    groundSpace (U * H * Uᴴ) E₀ = Submodule.span ℂ {toEuclideanLin U Ω} := by
  rw [groundSpace_unitary_conj hU, hspan, Submodule.map_span, Set.image_singleton]

/-- Unitary conjugation preserves the gap, for every `Δ`. -/
theorem isGapped_unitary_conj_iff {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    {H : Matrix n n ℂ} {E₀ Δ : ℝ} :
    IsGapped (U * H * Uᴴ) E₀ Δ ↔ IsGapped H E₀ Δ :=
  isGapped_iff_of_intertwine (unitaryLinearEquiv hU) (toEuclideanLin_unitary_conj hU H)

end Unitary

/-- A gap `Δ` is also a gap `Δ' ≤ Δ`. -/
theorem IsGapped.mono {H : Matrix n n ℂ} {E₀ Δ Δ' : ℝ} (h : IsGapped H E₀ Δ) (hΔ : Δ' ≤ Δ) :
    IsGapped H E₀ Δ' :=
  ⟨h.1, fun μ hμ ↦ (h.2 μ hμ).imp_right fun h' ↦
    (Complex.real_le_real.mpr (by linarith)).trans h'⟩

/-- A Hermitian matrix gapped at `E₀` with a nonnegative gap satisfies `H ≥ E₀`: its ground
energy is the bottom of its spectrum. -/
theorem IsGapped.posSemidef_sub_ground {H : Matrix n n ℂ} {E₀ Δ : ℝ} (hH : H.IsHermitian)
    (h : IsGapped H E₀ Δ) (hΔ : 0 ≤ Δ) : (H - (E₀ : ℂ) • 1).PosSemidef := by
  refine hH.posSemidef_sub_smul_one_of_le_eigenvalues fun k ↦ ?_
  rcases ((isGapped_iff_eigenvalues hH).mp h).2 k with hk | hk
  · exact hk.ge
  · linarith

/-! ### Scaling and shifting the energy -/

/-- Scaling `H` by a nonzero real `c` scales its eigenvalues by `c` and keeps the
eigenspaces. -/
theorem eigenspace_toEuclideanLin_smul {c : ℝ} (hc : c ≠ 0) (H : Matrix n n ℂ) (μ : ℂ) :
    Module.End.eigenspace (toEuclideanLin ((c : ℂ) • H)) ((c : ℂ) * μ) =
      Module.End.eigenspace (toEuclideanLin H) μ := by
  ext ψ
  rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, map_smul,
    LinearMap.smul_apply, mul_smul]
  exact (smul_right_injective _ (by exact_mod_cast hc : (c : ℂ) ≠ 0)).eq_iff

/-- Subtracting `a` times the identity shifts the eigenvalues by `-a` and keeps the
eigenspaces. -/
theorem eigenspace_toEuclideanLin_sub_smul_one (H : Matrix n n ℂ) (a : ℝ) (μ : ℂ) :
    Module.End.eigenspace (toEuclideanLin (H - (a : ℂ) • 1)) (μ - a) =
      Module.End.eigenspace (toEuclideanLin H) μ := by
  ext ψ
  rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, toLpLin_one,
    LinearMap.id_apply, sub_smul, sub_left_inj]

/-- Scaling `H` and the energy by a nonzero real `c` keeps the ground space. -/
theorem groundSpace_smul {c : ℝ} (hc : c ≠ 0) (H : Matrix n n ℂ) (E₀ : ℝ) :
    groundSpace ((c : ℂ) • H) (c * E₀) = groundSpace H E₀ := by
  rw [groundSpace, groundSpace, Complex.ofReal_mul, eigenspace_toEuclideanLin_smul hc]

/-- Shifting `H` by `-a` and the energy by `-a` keeps the ground space. -/
theorem groundSpace_sub_smul_one (H : Matrix n n ℂ) (a E₀ : ℝ) :
    groundSpace (H - (a : ℂ) • 1) (E₀ - a) = groundSpace H E₀ := by
  rw [groundSpace, groundSpace, Complex.ofReal_sub, eigenspace_toEuclideanLin_sub_smul_one]

/-- The ground space of `H` at `E₀` is the kernel of `H - E₀`. -/
theorem groundSpace_sub_smul_one_self (H : Matrix n n ℂ) (E₀ : ℝ) :
    groundSpace (H - (E₀ : ℂ) • 1) 0 = groundSpace H E₀ := by
  simpa using groundSpace_sub_smul_one H E₀ E₀

/-- Scaling by a positive real `c` scales the ground energy and the gap by `c`, for every
`Δ`. -/
theorem IsGapped.smul {H : Matrix n n ℂ} {E₀ Δ c : ℝ} (hc : 0 < c) (h : IsGapped H E₀ Δ) :
    IsGapped ((c : ℂ) • H) (c * E₀) (c * Δ) := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨by rw [groundSpace_smul hc.ne']; exact h.1, fun ν hν ↦ ?_⟩
  have hν' : Module.End.HasEigenvalue (toEuclideanLin H) (ν / c) := by
    rw [Module.End.hasEigenvalue_iff, ← eigenspace_toEuclideanLin_smul hc.ne',
      mul_div_cancel₀ _ hc0]
    exact Module.End.hasEigenvalue_iff.mp hν
  have hνc : ν = (c : ℂ) * (ν / c) := (mul_div_cancel₀ _ hc0).symm
  rcases h.2 _ hν' with h' | h'
  · left
    rw [hνc, h']
    push_cast
    ring
  · right
    have hcle : (0 : ℂ) ≤ c := by exact_mod_cast hc.le
    have := mul_le_mul_of_nonneg_left h' hcle
    rw [← hνc] at this
    convert this using 1
    push_cast
    ring

/-- Shifting `H` and the energy by `-a` keeps the gap, for every `Δ`. -/
theorem IsGapped.sub_smul_one {H : Matrix n n ℂ} {E₀ Δ : ℝ} (a : ℝ) (h : IsGapped H E₀ Δ) :
    IsGapped (H - (a : ℂ) • 1) (E₀ - a) Δ := by
  refine ⟨by rw [groundSpace_sub_smul_one]; exact h.1, fun ν hν ↦ ?_⟩
  have hν' : Module.End.HasEigenvalue (toEuclideanLin H) (ν + a) := by
    rw [Module.End.hasEigenvalue_iff, ← eigenspace_toEuclideanLin_sub_smul_one H a,
      add_sub_cancel_right]
    exact Module.End.hasEigenvalue_iff.mp hν
  rcases h.2 _ hν' with h' | h'
  · left
    push_cast
    linear_combination h'
  · right
    have := sub_le_sub_right h' (a : ℂ)
    rw [add_sub_cancel_right] at this
    convert this using 1
    push_cast
    ring

/-- If `H` is gapped at `E₀`, then `H - E₀` is gapped at `0` with the same gap. -/
theorem IsGapped.sub_smul_one_self {H : Matrix n n ℂ} {E₀ Δ : ℝ} (h : IsGapped H E₀ Δ) :
    IsGapped (H - (E₀ : ℂ) • 1) 0 Δ := by
  simpa using h.sub_smul_one E₀

end ManyBody
