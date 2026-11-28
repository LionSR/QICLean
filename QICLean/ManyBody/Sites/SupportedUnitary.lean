/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Eigenvalue.MatrixReindexEuclidean
import QICLean.Analysis.Isometry.PolarUnitaryCorrection
import QICLean.ManyBody.Sites.Placement.Basic

/-!
# A supported unitary polar correction

An operator `D` supported on a region `S` has a unitary polar factor supported on the same
region. For all vectors `x, y` this unitary satisfies the two-sided correction estimate
`‖U x - y‖ ≤ ‖D x - y‖ + ‖Dᴴ y - x‖`. No auxiliary system is adjoined, and no invertibility or
normalization of `D` is required.

Moved from TNLean, `TNLean/Lattice/SupportedPolarUnitary.lean` at commit `e41c3b63`, restated
for an arbitrary family of local alphabets.

## Main results

* `ManyBody.exists_supported_unitary_polar_correction`.
* `ManyBody.exists_supported_unitary_of_two_sided` — the polar step of the information
  reset.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, `02-information.tex`, lines 565–595, equations `eq:info-reset-polar-errors` and
  `eq:info-reset-unitary`.
-/

open Matrix
open scoped Kronecker

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- **A unitary polar factor on the same support.** Every operator `D` supported on a region
`S` has a unitary `U`, also supported on `S`, with `‖U x - y‖ ≤ ‖D x - y‖ + ‖Dᴴ y - x‖` for
all vectors `x, y`. The unitary is the placement of the polar factor of the regional operator
of `D`. Polynomial PEPS approximation, `02-information.tex`, lines 580–595
(`eq:info-reset-unitary`). -/
theorem exists_supported_unitary_polar_correction {S : Finset V}
    {D : Matrix (Config X) (Config X) ℂ} (hD : D ∈ supportedOperators X S) :
    ∃ U ∈ unitaryGroup (Config X) ℂ, U ∈ supportedOperators X S ∧
      ∀ x y : EuclideanSpace ℂ (Config X),
        ‖toEuclideanLin U x - y‖ ≤ ‖toEuclideanLin D x - y‖ + ‖toEuclideanLin Dᴴ y - x‖ := by
  obtain ⟨K, rfl⟩ := exists_eq_place_of_mem_supportedOperators hD
  obtain ⟨U', hpolar, -, -⟩ := exists_unitary_polar_correction K
  obtain ⟨-, -, -, hcorr⟩ :=
    unitary_polar_correction_kronecker_one (m := ComplConfig X S) K U' hpolar
  refine ⟨place S U', ?_, place_mem_supportedOperators _, fun x y ↦ ?_⟩
  · rw [mem_unitaryGroup_iff', star_eq_conjTranspose, ← place_conjTranspose, ← place_mul,
      ← star_eq_conjTranspose, (mem_unitaryGroup_iff'.mp U'.prop), place_one]
  set e := (cutEquiv X S).symm
  set φ := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  have hlin (A : Matrix (RegionConfig X S) (RegionConfig X S) ℂ) (z : EuclideanSpace ℂ _) :
      toEuclideanLin (place S A) z =
        φ (toEuclideanLin (A ⊗ₖ (1 : Matrix (ComplConfig X S) (ComplConfig X S) ℂ))
          (φ.symm z)) := by
    rw [← toEuclideanLin_reindex_piLpCongrLeft, LinearIsometryEquiv.apply_symm_apply]
    rfl
  have h := hcorr (φ.symm x) (φ.symm y)
  rw [← place_conjTranspose, hlin, hlin, hlin]
  have hcl (A : Matrix (RegionConfig X S × ComplConfig X S)
      (RegionConfig X S × ComplConfig X S) ℂ) (z : EuclideanSpace ℂ _) :
      toEuclideanCLM (n := _) (𝕜 := ℂ) A z = toEuclideanLin A z :=
    rfl
  simp only [hcl] at h
  rw [← φ.apply_symm_apply y, ← φ.apply_symm_apply x, ← map_sub, ← map_sub, ← map_sub,
    φ.norm_map, φ.norm_map, φ.norm_map, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]
  simpa [conjTranspose_kronecker] using h

/-- **The polar step of the information reset.** Let `M` be supported on `S`, and let a real
`z ≥ exp (-2 b)`, with `b ≥ 0`, satisfy `‖M ψ - z φ‖, ‖Mᴴ φ - z ψ‖ ≤ C exp (-10 b) ε`. Then a
unitary `U` supported on `S` satisfies `‖U ψ - φ‖ ≤ 2 C ε`. It is the polar factor of
`M / z`, whose residuals are at most `C exp (-8 b) ε` because `z⁻¹ ≤ exp (2 b)`.
Polynomial PEPS approximation, `02-information.tex`, lines 563–599,
`eq:info-reset-polar-errors` and `eq:info-reset-unitary`. -/
theorem exists_supported_unitary_of_two_sided {S : Finset V}
    {M : Matrix (Config X) (Config X) ℂ} (hM : M ∈ supportedOperators X S)
    {ψ φ : EuclideanSpace ℂ (Config X)} {z b C ε : ℝ} (hb : 0 ≤ b)
    (hz : Real.exp (-2 * b) ≤ z)
    (hfwd : ‖toEuclideanLin M ψ - (z : ℂ) • φ‖ ≤ C * Real.exp (-10 * b) * ε)
    (hrev : ‖toEuclideanLin Mᴴ φ - (z : ℂ) • ψ‖ ≤ C * Real.exp (-10 * b) * ε) :
    ∃ U ∈ unitaryGroup (Config X) ℂ, U ∈ supportedOperators X S ∧
      ‖toEuclideanLin U ψ - φ‖ ≤ 2 * C * ε := by
  have hz0 : 0 < z := (Real.exp_pos _).trans_le hz
  obtain ⟨U, hU, hUsupp, hcorr⟩ := exists_supported_unitary_polar_correction
    (SMulMemClass.smul_mem ((z : ℂ)⁻¹) hM)
  refine ⟨U, hU, hUsupp, (hcorr ψ φ).trans ?_⟩
  have hzinv : (z : ℂ)⁻¹ = ((z⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have hstar : star ((z : ℂ)⁻¹) = (z : ℂ)⁻¹ := by
    rw [hzinv, Complex.star_def, Complex.conj_ofReal]
  have hscale (A : Matrix (Config X) (Config X) ℂ) (x y : EuclideanSpace ℂ (Config X)) :
      ‖toEuclideanLin ((z : ℂ)⁻¹ • A) x - y‖ = z⁻¹ * ‖toEuclideanLin A x - (z : ℂ) • y‖ := by
    rw [← Real.norm_of_nonneg (inv_nonneg.mpr hz0.le), ← Complex.norm_real, ← hzinv,
      ← norm_smul, smul_sub, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hz0.ne'),
      one_smul, map_smul, LinearMap.smul_apply]
  rw [conjTranspose_smul, hstar, hscale, hscale]
  have hzb : z⁻¹ ≤ Real.exp (2 * b) := by
    have h₁ := inv_anti₀ (Real.exp_pos (-2 * b)) hz
    rwa [← Real.exp_neg, show -(-2 * b) = 2 * b by ring] at h₁
  have hdecay : Real.exp (2 * b) * Real.exp (-10 * b) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hX : 0 ≤ C * Real.exp (-10 * b) * ε := (norm_nonneg _).trans hfwd
  have hCε : 0 ≤ C * ε := by
    have : C * Real.exp (-10 * b) * ε = C * ε * Real.exp (-10 * b) := by ring
    rw [this] at hX
    exact nonneg_of_mul_nonneg_left hX (Real.exp_pos _)
  calc z⁻¹ * ‖toEuclideanLin M ψ - (z : ℂ) • φ‖ + z⁻¹ * ‖toEuclideanLin Mᴴ φ - (z : ℂ) • ψ‖
      ≤ Real.exp (2 * b) * (C * Real.exp (-10 * b) * ε) +
        Real.exp (2 * b) * (C * Real.exp (-10 * b) * ε) := by
        gcongr
    _ = 2 * (C * ε) * (Real.exp (2 * b) * Real.exp (-10 * b)) := by ring
    _ ≤ 2 * (C * ε) * 1 := by gcongr
    _ = 2 * C * ε := by ring

end ManyBody
