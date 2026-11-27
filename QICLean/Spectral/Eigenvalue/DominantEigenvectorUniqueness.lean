/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef

/-!
# Uniqueness of a density matrix eigenvector above one half

For a positive semidefinite matrix of trace one, an eigenvalue larger than one half has
multiplicity one. Thus any two unit eigenvectors with eigenvalues larger than one half have
the same eigenvalue and differ by a complex scalar of norm one. The quadratic form
on the orthogonal complement is bounded by the remaining trace.

This is an auxiliary spectral fact for the choice of the leading eigenvector in Landau,
Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`, lines 493–505.
It depends only on the density matrix, without a Hamiltonian or ground vector.

## Main results

* `Matrix.PosSemidef.exists_unit_eigenvector_max_eigenvalue`: A unit eigenvector for the largest
  eigenvalue of a density matrix.
-/

section DominantEigenvectorUniqueness

open scoped InnerProductSpace ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n]

/-- Two unit eigenvectors of a density matrix with eigenvalues larger than one half have
identical eigenvalues and differ by a unit complex phase. Auxiliary spectral uniqueness
for LVV13, `algo53.tex`, Lemma `l:leading`, lines 493–505. -/
theorem PosSemidef.eigenvalue_eq_and_exists_unit_smul_of_gt_half
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u v : EuclideanSpace ℂ n} {μ ν : ℝ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hvσ : σ *ᵥ WithLp.ofLp v = (ν : ℂ) • WithLp.ofLp v)
    (hμ : 1 / 2 < μ) (hν : 1 / 2 < ν) :
    μ = ν ∧ ∃ z : ℂ, ‖z‖ = 1 ∧ v = z • u := by
  classical
  let hS := hσ.isHermitian
  let b := hS.eigenvectorBasis
  let lam := hS.eigenvalues
  have hlam0 (i : n) : 0 ≤ lam i := hσ.eigenvalues_nonneg i
  have hlam1 : ∑ i, lam i = 1 := by
    have hh := congrArg Complex.re hS.trace_eq_sum_eigenvalues
    rw [htr, Complex.re_sum] at hh
    simpa [lam] using hh.symm
  have hunique {i j : n} (hi : 1 / 2 < lam i) (hj : 1 / 2 < lam j) : i = j := by
    by_contra hne
    have hpair : lam i + lam j ≤ ∑ k, lam k := by
      rw [← Finset.sum_pair (f := lam) hne]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun k _ _ ↦ hlam0 k
    linarith only [hpair, hlam1, hi, hj]
  have hcoeff (w : EuclideanSpace ℂ n) (α : ℝ)
      (hwσ : σ *ᵥ WithLp.ofLp w = (α : ℂ) • WithLp.ofLp w) (i : n) :
      (lam i : ℂ) * b.repr w i = (α : ℂ) * b.repr w i := by
    have hw : toEuclideanLin σ w = (α : ℂ) • w := by
      apply WithLp.ofLp_injective 2
      simpa only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using hwσ
    have hb : toEuclideanLin σ (b i) = (lam i : ℂ) • b i := by
      apply WithLp.ofLp_injective 2
      simp only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul]
      exact (hS.mulVec_eigenvectorBasis i).trans (Complex.coe_smul _ _).symm
    have hh := (isSymmetric_toEuclideanLin_iff.mpr hS) (b i) w
    rw [hb, hw, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      ← b.repr_apply_apply] at hh
    exact hh
  have hrepr (w : EuclideanSpace ℂ n) (α : ℝ) (hw : ‖w‖ = 1)
      (hwσ : σ *ᵥ WithLp.ofLp w = (α : ℂ) • WithLp.ofLp w) (hα : 1 / 2 < α) :
      ∃ (i : n) (z : ℂ), lam i = α ∧ ‖z‖ = 1 ∧ w = z • b i := by
    obtain ⟨i, hi⟩ : ∃ i, b.repr w i ≠ 0 := by
      by_contra! hz
      have hw0 : w = 0 := b.repr.injective (by ext j; simpa using hz j)
      rw [hw0, norm_zero] at hw
      norm_num at hw
    have hlam : lam i = α := by
      exact Complex.ofReal_injective (mul_right_cancel₀ hi (hcoeff w α hwσ i))
    have hz (j : n) (hji : j ≠ i) : b.repr w j = 0 := by
      by_contra hj
      have hlamj : lam j = α := by
        exact Complex.ofReal_injective (mul_right_cancel₀ hj (hcoeff w α hwσ j))
      exact hji (hunique (hlamj ▸ hα) (hlam ▸ hα))
    have hwrepr : w = b.repr w i • b i := by
      calc
        w = ∑ j, b.repr w j • b j := (b.sum_repr w).symm
        _ = b.repr w i • b i :=
          Finset.sum_eq_single i (fun j _ hji ↦ by rw [hz j hji, zero_smul])
            (fun hi ↦ (hi (Finset.mem_univ i)).elim)
    refine ⟨i, b.repr w i, hlam, ?_, hwrepr⟩
    have hh := congrArg norm hwrepr
    simpa only [hw, norm_smul, b.orthonormal.1 i, mul_one] using hh.symm
  obtain ⟨i, a, hi, ha, hua⟩ := hrepr u μ hu huσ hμ
  obtain ⟨j, d, hj, hd, hvd⟩ := hrepr v ν hv hvσ hν
  have hij : i = j := hunique (hi ▸ hμ) (hj ▸ hν)
  subst j
  have ha0 : a ≠ 0 := by
    intro hh
    simp only [hh, norm_zero, zero_ne_one] at ha
  refine ⟨hi.symm.trans hj, d / a, ?_, ?_⟩
  · rw [norm_div, hd, ha, div_one]
  · rw [hvd, hua, smul_smul, div_mul_cancel₀ _ ha0]

/-- For a trace-one positive matrix, an eigenvalue `μ > 1 / 2` leaves at most
`1 - μ` on the orthogonal complement of its unit eigenvector.  This is the
spectral separation used to certify a numerical leading eigenvector in LVV13,
`algo53.tex`, Lemma `l:leading`, lines 493--505. -/
theorem PosSemidef.re_inner_le_one_sub_eigenvalue_of_orthogonal
    [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    {u : EuclideanSpace ℂ n} {μ : ℝ} (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u)
    (hμ : 1 / 2 < μ) {w : EuclideanSpace ℂ n} (huw : ⟪u, w⟫_ℂ = 0) :
    (⟪w, toEuclideanLin σ w⟫_ℂ).re ≤ (1 - μ) * ‖w‖ ^ 2 := by
  classical
  let hS := hσ.isHermitian
  let b := hS.eigenvectorBasis
  let lam := hS.eigenvalues
  let L := toEuclideanLin σ
  have hsum : ∑ i, lam i = 1 := by
    have hh := congrArg Complex.re hS.trace_eq_sum_eigenvalues
    rw [htr, Complex.re_sum] at hh
    simpa [lam] using hh.symm
  have huL : L u = (μ : ℂ) • u := by
    apply WithLp.ofLp_injective 2
    simpa only [L, toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using huσ
  have hcoord (x : EuclideanSpace ℂ n) (i : n) :
      b.repr (L x) i = (lam i : ℂ) * b.repr x i := by
    calc
      b.repr (L x) i = ⟪b i, L x⟫_ℂ := b.repr_apply_apply (L x) i
      _ = ⟪L (b i), x⟫_ℂ :=
        ((isSymmetric_toEuclideanLin_iff.mpr hS) (b i) x).symm
      _ = (lam i : ℂ) * b.repr x i := by
        have hb : L (b i) = (lam i : ℂ) • b i := by
          apply WithLp.ofLp_injective 2
          simp only [L, toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul]
          exact (hS.mulVec_eigenvectorBasis i).trans (Complex.coe_smul _ _).symm
        rw [hb, inner_smul_left, Complex.conj_ofReal, ← b.repr_apply_apply]
  obtain ⟨j, hj⟩ : ∃ j, b.repr u j ≠ 0 := by
    by_contra! hz
    have hu0 : u = 0 := b.repr.injective (by ext i; simpa using hz i)
    rw [hu0, norm_zero] at hu
    norm_num at hu
  have hlamj : lam j = μ := by
    have hh := hcoord u j
    rw [huL, map_smul] at hh
    change (μ : ℂ) * b.repr u j = (lam j : ℂ) * b.repr u j at hh
    exact Complex.ofReal_injective (mul_right_cancel₀ hj hh.symm)
  have hbσ : σ *ᵥ WithLp.ofLp (b j) = (lam j : ℂ) • WithLp.ofLp (b j) :=
    (hS.mulVec_eigenvectorBasis j).trans (Complex.coe_smul _ _).symm
  obtain ⟨_, z, hz, hbphase⟩ :=
    hσ.eigenvalue_eq_and_exists_unit_smul_of_gt_half htr hu (b.orthonormal.1 j)
      huσ hbσ hμ (hlamj ▸ hμ)
  have hwj : b.repr w j = 0 := by
    rw [b.repr_apply_apply, hbphase, inner_smul_left, huw, mul_zero]
  have hlam (i : n) (hij : i ≠ j) : lam i ≤ 1 - μ := by
    have hpair : lam i + lam j ≤ ∑ k, lam k := by
      rw [← Finset.sum_pair (f := lam) hij]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun k _ _ ↦ hσ.eigenvalues_nonneg k
    rw [hsum, hlamj] at hpair
    linarith
  have hform : (⟪w, L w⟫_ℂ).re =
      ∑ i, lam i * Complex.normSq (b.repr w i) := by
    have hc : ⟪w, L w⟫_ℂ =
        ∑ i, (lam i : ℂ) * (Complex.normSq (b.repr w i) : ℂ) := by
      calc
        ⟪w, L w⟫_ℂ = ⟪b.repr w, b.repr (L w)⟫_ℂ :=
          (b.repr.inner_map_map w (L w)).symm
        _ = _ := by
          rw [EuclideanSpace.inner_eq_star_dotProduct]
          simp_rw [dotProduct, hcoord]
          simp [mul_assoc, Complex.mul_conj]
    have hh := congrArg Complex.re hc
    simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hh
  have hnorm : ∑ i, Complex.normSq (b.repr w i) = ‖w‖ ^ 2 := by
    rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
    simp_rw [Complex.normSq_eq_norm_sq]
  change (⟪w, L w⟫_ℂ).re ≤ (1 - μ) * ‖w‖ ^ 2
  rw [hform, ← hnorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hij : i = j
  · subst i
    rw [hwj, Complex.normSq_zero, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (hlam i hij) (Complex.normSq_nonneg _)

end Matrix

end DominantEigenvectorUniqueness

section DensityMaxEigenvector

/-!
## A unit eigenvector for the largest eigenvalue of a density matrix

A positive semidefinite matrix of trace one has a unit eigenvector with a positive eigenvalue
at least as large as every real eigenvalue. The first vector of the sorted orthonormal
eigenbasis gives a choice determined by the density matrix alone.

This is an auxiliary spectral selection fact for Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`, lines 493–505.
-/

open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n]

/-- A density matrix has a unit eigenvector for its largest eigenvalue, which is positive.
The maximum bounds every supplied real eigenvalue with a nonzero eigenvector.
Auxiliary spectral selection for LVV13, `algo53.tex`, Lemma `l:leading`, lines 493–505. -/
theorem PosSemidef.exists_unit_eigenvector_max_eigenvalue
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    ∃ (u : EuclideanSpace ℂ n) (μ₀ : ℝ), ‖u‖ = 1 ∧
      σ *ᵥ WithLp.ofLp u = (μ₀ : ℂ) • WithLp.ofLp u ∧ 0 < μ₀ ∧
      ∀ (μ : ℝ) (w : EuclideanSpace ℂ n), w ≠ 0 →
        σ *ᵥ WithLp.ofLp w = (μ : ℂ) • WithLp.ofLp w → μ ≤ μ₀ := by
  classical
  let hS := hσ.isHermitian
  have hsum : ∑ i, hS.eigenvalues i = 1 := by
    simpa [hS.trace_eq_sum_eigenvalues] using congrArg Complex.re htr
  obtain ⟨i, hi⟩ : ∃ i, 0 < hS.eigenvalues i := by
    have hpos : 0 < ∑ i, hS.eigenvalues i := by rw [hsum]; norm_num
    simpa only [Finset.mem_univ, true_and] using
      (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hσ.eigenvalues_nonneg i)).mp hpos
  have hdim : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let k : Fin (Fintype.card n) := ⟨0, hdim⟩
  let mu := hS.eigenvalues₀ k
  have hmax (j : Fin (Fintype.card n)) : hS.eigenvalues₀ j ≤ mu := by
    apply hS.eigenvalues₀_antitone
    change 0 ≤ j.val
    exact Nat.zero_le _
  have heig : hS.eigenvalues (e k) = mu := by
    change hS.eigenvalues₀ (e.symm (e k)) = hS.eigenvalues₀ k
    rw [e.symm_apply_apply]
  have hpos : 0 < mu := by
    have hh := hmax (e.symm i)
    change hS.eigenvalues i ≤ mu at hh
    exact hi.trans_le hh
  refine ⟨hS.eigenvectorBasis (e k), mu, hS.eigenvectorBasis.orthonormal.1 _, ?_, hpos, ?_⟩
  · rw [← heig]
    exact (hS.mulVec_eigenvectorBasis (e k)).trans (Complex.coe_smul _ _).symm
  intro μ w hw hwσ
  have hwlin : toEuclideanLin σ w = (μ : ℂ) • w := by
    apply WithLp.ofLp_injective 2
    simpa only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using hwσ
  have hev : Module.End.HasEigenvalue (toEuclideanLin σ) (μ : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hwlin, hw⟩
  obtain ⟨j, hj⟩ := (isSymmetric_toEuclideanLin_iff.mpr hS).exists_eigenvalues_eq
    finrank_euclideanSpace hev
  have heq : μ = hS.eigenvalues₀ j := Complex.ofReal_injective hj.symm
  rw [heq]
  exact hmax j

end Matrix

end DensityMaxEigenvector
