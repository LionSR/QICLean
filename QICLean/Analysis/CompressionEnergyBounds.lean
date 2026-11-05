/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GroundEnergyBounds
import QICLean.Analysis.RitzCompression

/-!
# Scalar lower bounds and actual compressed energies

Positive scalar lower bounds control eigenvalues of a matrix and its
actual orthogonal compressions. Comparing two such bounds also
identifies an attained energy with a canonical matrix minimum.
These finite-dimensional variational auxiliaries support regional
energy estimates in ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1631–1632, and its correctness proof at lines 1793–1807.
They do not construct a physical candidate or an energy-estimation algorithm.
-/

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- A positive scalar shift bounds every real eigenvalue with a
normalized eigenvector from below. Auxiliary to the regional variational
estimate in ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631–1632. -/
theorem le_eigenvalue_of_posSemidef_shift {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (a b : ℝ) (y : ι → ℂ) (hlo : (B - (a : ℂ) • 1).PosSemidef)
    (hy : B *ᵥ y = (b : ℂ) • y) (hyunit : star y ⬝ᵥ y = 1) : a ≤ b := by
  have hshift : (B - (a : ℂ) • 1) *ᵥ y = ((b - a : ℝ) : ℂ) • y := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, hy, Complex.ofReal_sub, sub_smul]
  exact sub_nonneg.mp (hlo.nonneg_of_normalized_eigenvector (b - a) y hshift hyunit)

/-- An attained lower energy of one matrix agrees with the actual
minimum of another when their positive scalar lower bounds compare in
both directions. The two matrices may have different finite index spaces.
This is an auxiliary for native regional energy estimates in ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631–1632. -/
theorem minEigenvalue_eq_of_attained_lower_bounds
    {σ m : Type*} [Fintype σ] [DecidableEq σ] [Fintype m] [DecidableEq m] [Nonempty m]
    (A : Matrix σ σ ℂ) (K : Matrix m m ℂ) (hK : K.IsHermitian)
    (e0 : ℝ) (x0 : σ → ℂ) (hx0 : star x0 ⬝ᵥ x0 = 1)
    (hAx0 : A *ᵥ x0 = (e0 : ℂ) • x0)
    (hKlow : (K - (e0 : ℂ) • 1).PosSemidef)
    (hAlow : (A - (minEigenvalue hK : ℂ) • 1).PosSemidef) : e0 = minEigenvalue hK := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := minEigenvalue_achieved hK
    let u : m → ℂ := ⇑(hK.eigenvectorBasis i)
    have huunit : star u ⬝ᵥ u = 1 := by
      have hh := hK.eigenvectorBasis.inner_eq_one i
      rw [EuclideanSpace.inner_eq_star_dotProduct] at hh
      simpa only [u, dotProduct_comm] using hh
    have hueigen : K *ᵥ u = (minEigenvalue hK : ℂ) • u := by
      change K *ᵥ ⇑(hK.eigenvectorBasis i) = (minEigenvalue hK : ℂ) • ⇑(hK.eigenvectorBasis i)
      rw [hK.mulVec_eigenvectorBasis, hi, Complex.coe_smul]
    exact le_eigenvalue_of_posSemidef_shift K e0 (minEigenvalue hK) u hKlow hueigen huunit
  · exact le_eigenvalue_of_posSemidef_shift A (minEigenvalue hK) e0 x0 hAlow hAx0 hx0

/-- Every actual compressed eigenvalue respects a positive scalar lower
bound for the original matrix. No spectral assumption on the candidate
space is required. Auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1631–1632. -/
theorem IsHermitian.orthogonalCompression_eigenvalue_ge
    {m : Type*} [Fintype m] [DecidableEq m] {K : Matrix m m ℂ} (hK : K.IsHermitian)
    (e : ℝ) (hlo : (K - (e : ℂ) • 1).PosSemidef)
    (S : Submodule ℂ (EuclideanSpace ℂ m)) {n : ℕ} (hn : Module.finrank ℂ S = n)
    (i : Fin n) :
    e ≤ (S.orthogonalCompression_isSymmetric
      (isSymmetric_toEuclideanLin_iff.mpr hK)).eigenvalues hn i := by
  let A := (toEuclideanCLM (𝕜 := ℂ) (n := m) K).toLinearMap
  let hS := S.orthogonalCompression_isSymmetric (isSymmetric_toEuclideanLin_iff.mpr hK)
  let lam := hS.eigenvalues hn i
  let u := hS.eigenvectorBasis hn i
  have huunit : ‖u‖ = 1 := (hS.eigenvectorBasis hn).norm_eq_one i
  have hueigen : S.orthogonalCompression A u = (lam : ℂ) • u :=
    hS.apply_eigenvectorBasis hn i
  have hinner : (inner ℂ (u : EuclideanSpace ℂ m)
      (toEuclideanCLM (𝕜 := ℂ) (n := m) K u)).re = lam := by
    have hh : inner ℂ u (S.orthogonalCompression A u) =
        inner ℂ (u : EuclideanSpace ℂ m) (toEuclideanCLM (𝕜 := ℂ) (n := m) K u) :=
      S.inner_orthogonalCompression A u u
    rw [← hh, hueigen]
    simp only [inner_smul_right, inner_self_eq_norm_sq_to_K, huunit]
    norm_num
  have hpos : (toEuclideanCLM (𝕜 := ℂ) (n := m) (K - (e : ℂ) • 1)).IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
      (isPositive_toEuclideanLin_iff.mpr hlo)
  have hlow := hpos.re_inner_nonneg_left (u : EuclideanSpace ℂ m)
  simp only [map_sub, map_smul, map_one, _root_.sub_apply, _root_.smul_apply,
    one_apply_eq_self, inner_sub_left, inner_smul_left, Complex.conj_ofReal,
    RCLike.re_to_complex, Complex.re_ofReal_mul] at hlow
  have hleft : (inner ℂ (toEuclideanCLM (𝕜 := ℂ) (n := m) K u)
      (u : EuclideanSpace ℂ m)).re = lam := by
    rw [← RCLike.re_to_complex, inner_re_symm, RCLike.re_to_complex]
    exact hinner
  have hself : (inner ℂ (u : EuclideanSpace ℂ m) (u : EuclideanSpace ℂ m)).re = 1 := by
    change RCLike.re (inner ℂ (u : EuclideanSpace ℂ m) (u : EuclideanSpace ℂ m)) = 1
    rw [inner_self_eq_norm_sq]
    change ‖u‖ ^ 2 = 1
    rw [huunit, one_pow]
  rw [hleft, hself] at hlow
  linarith only [hlow]

end Matrix
