/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import QICLean.Analysis.LowEnergyPerturbation

/-!
# Closed spectral subspaces in isometric coordinates

Closed low-energy spans are independent of a complete real-eigenvalue orthonormal basis.
Isometric intertwining transports these spans and yields canonical spectral data for an actual
Hermitian matrix. Two distinct spectral values also force the local dimension of a product
configuration space to be at least two.

These results support ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and Theorem `t:ais`, lines 1010–1024.
-/

section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {n m : Type*} [Fintype n] [Fintype m]

/-- The closed low-energy span in one complete eigenbasis is contained in
that of another basis of the same operator. Auxiliary to the spectral
subspace identifications in ALVV, arXiv:1602.08828v2, `lem:hard-trunc`,
lines 955–968, and `t:ais`, lines 1010–1024. -/
private theorem spectralSpanLE_le_of_eigenbases
    (b : OrthonormalBasis n 𝕜 E) (b' : OrthonormalBasis m 𝕜 E)
    (a : n → ℝ) (a' : m → ℝ) {H : E →ₗ[𝕜] E}
    (hH : ∀ i, H (b i) = (a i : 𝕜) • b i)
    (hH' : ∀ j, H (b' j) = (a' j : 𝕜) • b' j) (c : ℝ) :
    spectralSpanLE b a c ≤ spectralSpanLE b' a' c := by
  apply span_le.mpr
  rintro _ ⟨i, hi, rfl⟩
  apply (mem_spectralSpanLE_iff b' a' c (b i)).mpr
  intro j hj
  have hcoord := b'.repr_apply_of_eigen a' hH' (b i) j
  rw [hH i, map_smul] at hcoord
  change (a i : 𝕜) * b'.repr (b i) j = (a' j : 𝕜) * b'.repr (b i) j at hcoord
  have hne : (a i : 𝕜) ≠ (a' j : 𝕜) :=
    RCLike.ofReal_injective.ne (ne_of_lt (lt_of_le_of_lt hi hj))
  have hzero : ((a i : 𝕜) - (a' j : 𝕜)) * b'.repr (b i) j = 0 := by
    rw [sub_mul, hcoord, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

/-- The closed low-energy span is independent of the complete real-eigenvalue
orthonormal basis of a fixed operator. Repeated eigenvalues, different finite
index types, and zero-dimensional spaces are included. No symmetry, simple
spectrum, or nonempty-index premise is needed. Auxiliary to ALVV,
arXiv:1602.08828v2, `lem:hard-trunc`, lines 955–968, and `t:ais`, lines 1010–1024. -/
private theorem spectralSpanLE_eq_of_eigenbases
    (b : OrthonormalBasis n 𝕜 E) (b' : OrthonormalBasis m 𝕜 E)
    (a : n → ℝ) (a' : m → ℝ) {H : E →ₗ[𝕜] E}
    (hH : ∀ i, H (b i) = (a i : 𝕜) • b i)
    (hH' : ∀ j, H (b' j) = (a' j : 𝕜) • b' j) (c : ℝ) :
    spectralSpanLE b a c = spectralSpanLE b' a' c :=
  le_antisymm (spectralSpanLE_le_of_eigenbases b b' a a' hH hH' c)
    (spectralSpanLE_le_of_eigenbases b' b a' a hH' hH c)
end Submodule

namespace Submodule

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {n m : Type*} [Fintype n] [Fintype m]

/-- An isometry intertwining two operators transports their closed low-energy
spans, independently of the complete eigenbases used on the two sides.
Auxiliary to the spectral-subspace identifications in ALVV,
arXiv:1602.08828v2, `lem:hard-trunc`, lines 955–968, and `t:ais`, lines 1010–1024.
No symmetry, simple spectrum, nonempty-index, or additional dimension premise is used. -/
private theorem map_spectralSpanLE_eq_of_intertwining
    (u : E ≃ₗᵢ[𝕜] F) (H : E →ₗ[𝕜] E) (K : F →ₗ[𝕜] F)
    (b : OrthonormalBasis n 𝕜 E) (b' : OrthonormalBasis m 𝕜 F)
    (a : n → ℝ) (a' : m → ℝ)
    (hH : ∀ i, H (b i) = (a i : 𝕜) • b i)
    (hK : ∀ j, K (b' j) = (a' j : 𝕜) • b' j)
    (hUK : ∀ x, K (u x) = u (H x)) (c : ℝ) :
    (spectralSpanLE b a c).map (u.toLinearEquiv : E →ₗ[𝕜] F) =
      spectralSpanLE b' a' c := by
  have hmap : ∀ i, K ((b.map u) i) = (a i : 𝕜) • (b.map u) i := by
    intro i
    rw [OrthonormalBasis.map_apply, hUK, hH i, map_smul]
  have hspan : (spectralSpanLE b a c).map (u.toLinearEquiv : E →ₗ[𝕜] F) =
      spectralSpanLE (b.map u) a c := by
    unfold spectralSpanLE
    rw [map_span, Set.image_image]
    rfl
  exact hspan.trans (spectralSpanLE_eq_of_eigenbases (b.map u) b' a a' hmap hK c)
end Submodule

open scoped Matrix.Norms.L2Operator

namespace Matrix

/-- Actual matrix cluster data supply the canonical spectral data after an
isometric change of coordinates. Symmetry, the canonical gap alternatives,
and the spectral upper bound are derived, rather than assumed separately.
Auxiliary to ALVV, arXiv:1602.08828v2, `lem:hard-trunc`, lines 955–968,
and the Chebyshev step of `t:ais`, lines 1010–1024. -/
theorem exists_canonical_isometric_spectral_data
    {σ ι F : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (B : Matrix σ σ ℂ) (hB : B.IsHermitian)
    (v : OrthonormalBasis ι ℂ (EuclideanSpace ℂ σ)) (lam : ι → ℝ)
    (hv : ∀ i, B.toEuclideanLin (v i) = (lam i : ℂ) • v i)
    (η₀ η₁ U : ℝ)
    (hcluster : Submodule.spectralSpanLE v lam η₀ = Submodule.spectralSpanLE v lam η₁)
    (hnorm : ‖B‖ ≤ U) (u : EuclideanSpace ℂ σ ≃ₗᵢ[ℂ] F) :
    let K : F →ₗ[ℂ] F := u.toLinearMap ∘ₗ B.toEuclideanLin ∘ₗ u.symm.toLinearMap
    ∃ hK : K.IsSymmetric,
      let bK : OrthonormalBasis (Fin (Module.finrank ℂ F)) ℂ F :=
        hK.eigenvectorBasis (rfl : Module.finrank ℂ F = Module.finrank ℂ F)
      let lamK : Fin (Module.finrank ℂ F) → ℝ :=
        hK.eigenvalues (rfl : Module.finrank ℂ F = Module.finrank ℂ F)
      (∀ j, lamK j ≤ η₀ ∨ η₁ ≤ lamK j) ∧ (∀ j, lamK j ≤ U) ∧
        ∀ c : ℝ, (Submodule.spectralSpanLE v lam c).map
            (u.toLinearEquiv : EuclideanSpace ℂ σ →ₗ[ℂ] F) =
          Submodule.spectralSpanLE bK lamK c := by
  intro K
  have hK : K.IsSymmetric :=
    (LinearMap.isSymmetric_linearIsometryEquiv_conj_iff B.toEuclideanLin u).mpr
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB)
  refine ⟨hK, ?_⟩
  intro bK lamK
  have hKeig : ∀ j, K (bK j) = (lamK j : ℂ) • bK j :=
    hK.apply_eigenvectorBasis rfl
  have hUK : ∀ x, K (u x) = u (B.toEuclideanLin x) := by
    intro x
    change u (B.toEuclideanLin (u.symm (u x))) = u (B.toEuclideanLin x)
    rw [u.symm_apply_apply]
  have hmap (c : ℝ) : (Submodule.spectralSpanLE v lam c).map
        (u.toLinearEquiv : EuclideanSpace ℂ σ →ₗ[ℂ] F) =
      Submodule.spectralSpanLE bK lamK c :=
    Submodule.map_spectralSpanLE_eq_of_intertwining
      u B.toEuclideanLin K v bK lam lamK hv hKeig hUK c
  have hclosed : Submodule.spectralSpanLE bK lamK η₀ =
      Submodule.spectralSpanLE bK lamK η₁ :=
    (hmap η₀).symm.trans ((congrArg
      (fun S : Submodule ℂ (EuclideanSpace ℂ σ) ↦
        S.map (u.toLinearEquiv : EuclideanSpace ℂ σ →ₗ[ℂ] F)) hcluster).trans (hmap η₁))
  have hKB (z : F) : ‖K z‖ ≤ ‖B‖ * ‖z‖ := by
    change ‖u ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) B) (u.symm z))‖ ≤ ‖B‖ * ‖z‖
    rw [u.norm_map, Matrix.cstar_norm_def]
    simpa only [u.symm.norm_map] using
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) B).le_opNorm (u.symm z)
  refine ⟨?_, ?_, hmap⟩
  · intro j
    by_cases hj : lamK j ≤ η₀
    · exact Or.inl hj
    · apply Or.inr
      by_contra hj'
      have hmem₁ : bK j ∈ Submodule.spectralSpanLE bK lamK η₁ :=
        Submodule.subset_span ⟨j, (lt_of_not_ge hj').le, rfl⟩
      have hmem₀ : bK j ∈ Submodule.spectralSpanLE bK lamK η₀ := by
        rw [hclosed]
        exact hmem₁
      have hcoord := (Submodule.mem_spectralSpanLE_iff bK lamK η₀ (bK j)).mp
        hmem₀ j (lt_of_not_ge hj)
      simp at hcoord
  · intro j
    have habs : |lamK j| ≤ ‖B‖ := by
      simpa only [hKeig j, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        bK.norm_eq_one j, mul_one]
        using hKB (bK j)
    exact (le_abs_self (lamK j)).trans (habs.trans hnorm)
end Matrix

open scoped BigOperators TensorProduct InnerProductSpace Matrix.Norms.L2Operator

namespace Matrix.IsHermitian

/-- Two distinct spectral values force the on-site dimension to be at
least two. Thus the explicit first and second distinct eigenvalues in
ALVV, arXiv:1602.08828v2, Assumption (DG), lines 273–280, supply the
dimension condition used by the polynomial-family estimates. This is
finite spectral algebra and imposes no additional physical hypothesis. -/
theorem two_le_local_dimension_of_two_spectral_values
    {L q : ℕ} {H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hH : H.IsHermitian) {mu nu : ℝ}
    (hmu : mu ∈ spectrum ℝ H) (hnu : nu ∈ spectrum ℝ H) (hne : mu ≠ nu) :
    2 ≤ q := by
  by_contra hq
  have hq1 : q ≤ 1 := by omega
  have : Subsingleton (Fin q) := Fin.subsingleton_iff_le_one.mpr hq1
  obtain ⟨i, hi⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hmu
  obtain ⟨j, hj⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hnu
  exact hne (hi.symm.trans
    ((congrArg hH.eigenvalues (Subsingleton.elim i j)).trans hj))
end Matrix.IsHermitian
end
