/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowEnergyCoordinates
import QICLean.Analysis.GroundEnergyBounds
import QICLean.Analysis.EuclideanEigenvectorBasis

/-!
# Low-energy spaces under scalar shifts

Subtracting a real scalar from a Hermitian matrix shifts its spectral cutoff
by the same scalar. The result uses the actual canonical eigenbases of both
matrices, without a prescribed relation between those bases. A normalized
centered ground vector then identifies every original low-energy window with
one window based at the original canonical ground energy.

These identities support ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`,
lines 1027–1041, and Proposition `prop:albootstrap-ld`, lines 1112–1128.
No spectral gap, simple spectrum or bound on a perturbation is required.
-/

open scoped ComplexOrder

namespace Submodule

/-- Shifting every real eigenvalue and the cutoff by the same scalar preserves
its closed spectral span. Auxiliary to the scalar normalizations in ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041. -/
theorem spectralSpanLE_sub
    {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (a : ι → ℝ) (s c : ℝ) :
    spectralSpanLE b (fun i ↦ a i - s) (c - s) = spectralSpanLE b a c := by
  simp only [spectralSpanLE, sub_le_sub_iff_right]

end Submodule

namespace Matrix.IsHermitian

/-- The actual canonical low-energy spaces of a Hermitian matrix and its real
scalar shift agree after shifting the cutoff. Degenerate eigenvalues and the
empty matrix index are included. Auxiliary to ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041, and the canonical windows in
Proposition `prop:albootstrap-ld`, lines 1112–1128. -/
theorem spectralSpanLE_sub_smul_one
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    {H : Matrix σ σ ℂ} (hH : H.IsHermitian) (s c : ℝ) :
    let hC : (H - (s : ℂ) • 1).IsHermitian :=
      hH.sub (Matrix.isHermitian_one.smul (isSelfAdjoint_iff.mpr (by simp)))
    Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (c - s) =
      Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues c := by
  intro hC
  have hshift (i : σ) :
      (H - (s : ℂ) • 1).toEuclideanLin (hH.eigenvectorBasis i) =
        ((hH.eigenvalues i - s : ℝ) : ℂ) • hH.eigenvectorBasis i := by
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ)
      (H - (s : ℂ) • 1) (hH.eigenvectorBasis i) = _
    rw [map_sub, map_smul, map_one]
    simp only [_root_.sub_apply, _root_.smul_apply,
      one_apply_eq_self, hH.toEuclideanCLM_eigenvectorBasis,
      Complex.ofReal_sub, sub_smul]
    rfl
  have hcenter (i : σ) :
      (H - (s : ℂ) • 1).toEuclideanLin (hC.eigenvectorBasis i) =
        (hC.eigenvalues i : ℂ) • hC.eigenvectorBasis i :=
    hC.toEuclideanCLM_eigenvectorBasis i
  exact (Submodule.spectralSpanLE_eq_of_eigenbases
    hC.eigenvectorBasis hH.eigenvectorBasis hC.eigenvalues
    (fun i ↦ hH.eigenvalues i - s) hcenter hshift (c - s)).trans
      (Submodule.spectralSpanLE_sub hH.eigenvectorBasis hH.eigenvalues s c)

/-- An actual normalized ground vector of the centered matrix identifies the
original canonical ground energy and every original low-energy window.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`,
lines 1027–1041, and Proposition `prop:albootstrap-ld`, lines 1112–1128.
The nonempty index is the usual domain of the minimum eigenvalue; no gap or
uniqueness hypothesis is present. -/
theorem spectralSpanLE_centered_ground
    {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ]
    {H : Matrix σ σ ℂ} (hH : H.IsHermitian) (s E0 eta : ℝ) (z : σ → ℂ)
    (hzunit : star z ⬝ᵥ z = 1)
    (hzeigen : (H - (s : ℂ) • 1) *ᵥ z = (E0 : ℂ) • z)
    (hlow : ((H - (s : ℂ) • 1) - (E0 : ℂ) • 1).PosSemidef) :
    let hC : (H - (s : ℂ) • 1).IsHermitian :=
      hH.sub (Matrix.isHermitian_one.smul (isSelfAdjoint_iff.mpr (by simp)))
    minEigenvalue hH = E0 + s ∧
      Submodule.spectralSpanLE hC.eigenvectorBasis hC.eigenvalues (E0 + eta) =
        Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues
          (minEigenvalue hH + eta) := by
  intro hC
  have hmin := hH.minEigenvalue_eq_add_of_centered_ground s E0 z hzunit hzeigen hlow
  refine ⟨hmin, ?_⟩
  have hcut : minEigenvalue hH + eta - s = E0 + eta := by
    rw [hmin]
    ring
  simpa only [hcut] using hH.spectralSpanLE_sub_smul_one s (minEigenvalue hH + eta)

/-- A centered presentation of an actual Hermitian matrix gives the same
canonical low-energy spaces, regardless of how that presentation is written.
The minimum and all cutoff identifications follow from the normalized
centered ground vector and positive-semidefinite lower bound. Auxiliary to
ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041, and
Proposition `prop:albootstrap-ld`, lines 1112–1128. -/
theorem spectralSpanLE_centered_ground_of_eq
    {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ]
    {H B : Matrix σ σ ℂ} (hH : H.IsHermitian) (hB : B.IsHermitian)
    (s E0 : ℝ) (z : σ → ℂ) (hB_eq : B = H - (s : ℂ) • 1)
    (hzunit : star z ⬝ᵥ z = 1)
    (hzeigen : B *ᵥ z = (E0 : ℂ) • z)
    (hlow : (B - (E0 : ℂ) • 1).PosSemidef) :
    minEigenvalue hH = E0 + s ∧
      ∀ eta : ℝ,
        Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues (E0 + eta) =
          Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues
            (minEigenvalue hH + eta) := by
  subst B
  have hcanonical (eta : ℝ) :=
    hH.spectralSpanLE_centered_ground s E0 eta z hzunit hzeigen hlow
  exact ⟨(hcanonical 0).1, fun eta ↦ (hcanonical eta).2⟩

end Matrix.IsHermitian
