/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TensorProductWeights
import QICLean.Analysis.TensorFamilyImage
import QICLean.Analysis.RitzCompression

/-!
# A local energy bound from a tensor vector

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
