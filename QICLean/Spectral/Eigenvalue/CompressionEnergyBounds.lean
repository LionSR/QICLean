/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Eigenvalue.GroundEnergyBounds
import QICLean.Spectral.Eigenvalue.RitzCompression
import QICLean.Analysis.TensorProduct.Weights
import QICLean.Analysis.Subspace.FamilyImage

/-!
# Scalar lower bounds and actual compressed energies

Positive scalar lower bounds control eigenvalues of a matrix and its
actual orthogonal compressions. Comparing two such bounds also
identifies an attained energy with a canonical matrix minimum.
These finite-dimensional variational auxiliaries support regional
energy estimates in ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1631–1632, and its correctness proof at lines 1793–1807.
They do not construct a physical candidate or an energy-estimation algorithm.

It also contains the following results.

* `Matrix.IsHermitian.exists_compression_min_between_of_tensor_energy`: two-sided intervals for
  actual compressed minima.
* `Submodule.exists_unit_re_inner_le_of_tensor_energy`,
  `Submodule.exists_compression_min_eigenvalue_le_of_tensor_energy`: a local energy bound from a
  tensor vector.
-/

section CompressionEnergyBounds

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

end CompressionEnergyBounds

section TensorEnergyMinimum

/-!
## A local energy bound from a tensor vector

A nonzero vector in `S ⊗ F` whose Rayleigh quotient for `A ⊗ I` is at most
`c` has a nonzero slice in `S` with Rayleigh quotient at most `c`.
Normalization gives an actual unit vector in `S`. This is a variational
auxiliary for regional energy estimation in ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and its correctness proof at lines
1793–1807; it does not construct an energy estimation algorithm.
-/

open scoped TensorProduct InnerProductSpace
open TensorProduct

namespace Submodule

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
private theorem innerSlice_mem_of_mem_tensorProd_top (S : Submodule ℂ E)
    {w : E ⊗[ℂ] F} (hw : w ∈ S.tensorProd (⊤ : Submodule ℂ F)) (v : F) :
    innerSlice v w ∈ S := by
  have hle : S.tensorProd (⊤ : Submodule ℂ F) ≤ S.comap (innerSlice v) := by
    apply tensorProd_le_iff.mpr
    intro x hx y _hy
    change innerSlice v (x ⊗ₜ[ℂ] y) ∈ S
    rw [innerSlice_tmul]
    exact S.smul_mem _ hx
  exact hle hw

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
private theorem inner_mapL_one_eq_sum_innerSlice {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ F) (A : E →L[ℂ] E) (w : E ⊗[ℂ] F) :
    inner ℂ (mapL A (1 : F →L[ℂ] F) w) w =
      ∑ j, inner ℂ (A (innerSlice (e j) w)) (innerSlice (e j) w) := by
  classical
  conv_lhs => rw [← sum_innerSlice_tmul e w]
  rw [map_sum, sum_inner]
  simp_rw [mapL_tmul, one_apply_eq_self, inner_sum, inner_tmul,
    orthonormal_iff_ite.mp e.orthonormal]
  simp

omit [FiniteDimensional ℂ E] in
/-- A nonzero tensor vector of energy at most `c` yields an actual unit
vector of the local subspace with energy at most `c`. No symmetry
hypothesis is needed for this real quadratic-form statement. This is a
variational auxiliary for regional energy estimation in ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631, and lines 1793–1807. -/
theorem exists_unit_re_inner_le_of_tensor_energy (S : Submodule ℂ E)
    (A : E →L[ℂ] E) {w : E ⊗[ℂ] F} (hw : w ∈ S.tensorProd (⊤ : Submodule ℂ F))
    (hwne : w ≠ 0) {c : ℝ}
    (henergy : (inner ℂ (mapL A (1 : F →L[ℂ] F) w) w).re ≤ c * ‖w‖ ^ 2) :
    ∃ u ∈ S, ‖u‖ = 1 ∧ (inner ℂ (A u) u).re ≤ c := by
  classical
  let e := stdOrthonormalBasis ℂ F
  let x := fun j => innerSlice (e j) w
  have hxmem (j) : x j ∈ S := innerSlice_mem_of_mem_tensorProd_top S hw _
  have hnorm : ‖w‖ ^ 2 = ∑ j, ‖x j‖ ^ 2 := by
    rw [← norm_sq_sum_tmul e x, sum_innerSlice_tmul]
  have hsum : ∑ j, (inner ℂ (A (x j)) (x j)).re ≤ ∑ j, c * ‖x j‖ ^ 2 := by
    simpa only [inner_mapL_one_eq_sum_innerSlice e A w, Complex.re_sum,
      hnorm, Finset.mul_sum] using henergy
  have hxne : ∃ j, x j ≠ 0 := by
    by_contra! hzero
    apply hwne
    rw [← sum_innerSlice_tmul e w]
    change ∑ j, x j ⊗ₜ[ℂ] e j = 0
    simp only [hzero, zero_tmul, Finset.sum_const_zero]
  have hgood : ∃ j, x j ≠ 0 ∧ (inner ℂ (A (x j)) (x j)).re ≤ c * ‖x j‖ ^ 2 := by
    by_contra! hbad
    have hle (j) : c * ‖x j‖ ^ 2 ≤ (inner ℂ (A (x j)) (x j)).re := by
      by_cases hj : x j = 0
      · simp [hj]
      · exact (hbad j hj).le
    obtain ⟨j, hj⟩ := hxne
    have hlt := Finset.sum_lt_sum (fun k _ => hle k)
      ⟨j, Finset.mem_univ j, hbad j hj⟩
    exact (not_lt_of_ge hsum) hlt
  obtain ⟨j, hj, hjenergy⟩ := hgood
  let u := (‖x j‖⁻¹ : ℂ) • x j
  have hu : ‖u‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) hj
  refine ⟨u, S.smul_mem _ (hxmem j), hu, ?_⟩
  have hray : A.rayleighQuotient (x j) ≤ c :=
    (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hj))).mpr hjenergy
  have hscale : (‖x j‖⁻¹ : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hj)
  have huray : A.rayleighQuotient u ≤ c := by
    rw [A.rayleigh_smul _ hscale]
    exact hray
  change (inner ℂ (A u) u).re / ‖u‖ ^ 2 ≤ c at huray
  simpa only [hu, one_pow, div_one] using huray

/-- The least ordered eigenvalue of the actual orthogonal compression
is at most the tensor Rayleigh bound. The dimension witness is derived
from the nonzero tensor vector, so zero-dimensional local or environmental
spaces require no additional hypotheses. This is a variational auxiliary
for regional energy estimation in ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and lines 1793–1807. -/
theorem exists_compression_min_eigenvalue_le_of_tensor_energy (S : Submodule ℂ E)
    (A : E →L[ℂ] E) (hA : A.toLinearMap.IsSymmetric)
    {w : E ⊗[ℂ] F} (hw : w ∈ S.tensorProd (⊤ : Submodule ℂ F)) (hwne : w ≠ 0)
    {c : ℝ}
    (henergy : (inner ℂ (mapL A (1 : F →L[ℂ] F) w) w).re ≤ c * ‖w‖ ^ 2) :
    ∃ (n : ℕ) (hn : Module.finrank ℂ S = n + 1),
      (S.orthogonalCompression_isSymmetric hA).eigenvalues hn (Fin.last n) ≤ c := by
  classical
  obtain ⟨u, huS, hu, henergyu⟩ := S.exists_unit_re_inner_le_of_tensor_energy A hw hwne henergy
  let uS : S := ⟨u, huS⟩
  have huSunit : ‖uS‖ = 1 := hu
  have huSne : uS ≠ 0 := by
    intro hzero
    have : u = 0 := congrArg Subtype.val hzero
    simp only [this, norm_zero, zero_ne_one] at hu
  have hdim : 1 ≤ Module.finrank ℂ S := by
    simpa only [finrank_span_singleton huSne] using (ℂ ∙ uS).finrank_le
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Module.finrank ℂ S ≠ 0)
  refine ⟨n, hn, ?_⟩
  apply (S.orthogonalCompression_isSymmetric hA).eigenvalue_le_of_trial_subspace
    hn (ℂ ∙ uS) c ?_ (Fin.last n) ?_
  · intro y hy
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp hy
    rw [inner_orthogonalCompression]
    change (inner ℂ (a • u) (A (a • u))).re ≤ c * ‖a • uS‖ ^ 2
    have hs : inner ℂ (A (a • u)) (a • u) = inner ℂ (a • u) (A (a • u)) :=
      hA (a • u) (a • u)
    rw [← hs]
    change A.reApplyInnerSelf (a • u) ≤ c * ‖a • uS‖ ^ 2
    rw [A.reApplyInnerSelf_smul]
    simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_complex,
      norm_smul, huSunit, mul_one, mul_comm] using
      mul_le_mul_of_nonneg_left henergyu (sq_nonneg ‖a‖)
  · rw [finrank_span_singleton huSne]
    simp

end Submodule

end TensorEnergyMinimum

section CompressionEnergyInterval

/-!
## Two-sided intervals for actual compressed minima

A positive scalar lower bound and a nonzero tensor Rayleigh bound determine
an interval containing the least ordered eigenvalue of the actual native
orthogonal compression. This combines the existing lower and upper
variational estimates without any extra nonempty-space hypothesis.
Supporting ALVV, arXiv:1602.08828v2, the energy-estimation argument,
lines 1793–1807.
-/

open scoped TensorProduct InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {σ F : Type*} [Fintype σ] [DecidableEq σ]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The actual compressed minimum lies between the supplied scalar lower
bound and the tensor Rayleigh upper bound. The nonzero tensor vector
constructs the compression dimension witness. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631, and lines 1793–1807. -/
theorem IsHermitian.exists_compression_min_between_of_tensor_energy
    {K : Matrix σ σ ℂ} (hK : K.IsHermitian)
    (S : Submodule ℂ (EuclideanSpace ℂ σ)) (lo hi : ℝ)
    (hlow : (K - (lo : ℂ) • 1).PosSemidef)
    {w : EuclideanSpace ℂ σ ⊗[ℂ] F}
    (hw : w ∈ S.tensorProd (⊤ : Submodule ℂ F)) (hwne : w ≠ 0)
    (henergy : (inner ℂ (TensorProduct.mapL
      (toEuclideanCLM (𝕜 := ℂ) (n := σ) K) (1 : F →L[ℂ] F) w) w).re ≤ hi * ‖w‖ ^ 2) :
    ∃ (n : ℕ) (hn : Module.finrank ℂ S = n + 1),
      lo ≤ (S.orthogonalCompression_isSymmetric
        (isSymmetric_toEuclideanLin_iff.mpr hK)).eigenvalues hn (Fin.last n) ∧
      (S.orthogonalCompression_isSymmetric
        (isSymmetric_toEuclideanLin_iff.mpr hK)).eigenvalues hn (Fin.last n) ≤ hi := by
  obtain ⟨n, hn, hupper⟩ := S.exists_compression_min_eigenvalue_le_of_tensor_energy
    (toEuclideanCLM (𝕜 := ℂ) (n := σ) K)
    (isSymmetric_toEuclideanLin_iff.mpr hK) hw hwne henergy
  exact ⟨n, hn, hK.orthogonalCompression_eigenvalue_ge lo hlow S hn (Fin.last n), hupper⟩

end Matrix

end CompressionEnergyInterval
