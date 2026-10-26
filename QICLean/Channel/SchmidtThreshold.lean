/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.SchmidtTrimming
import QICLean.Analysis.ShiftedDensityTruncation

/-!
# Trimming a bipartite vector at a threshold on its Schmidt coefficients

Arad, Landau, Vazirani and Vidick trim a viable subspace cut by cut (arXiv:1602.08828v2,
`local_alg_arxiv_v2.tex`, Definition `def:trimming`, lines 642–656). At each cut they keep the
left Schmidt vectors of a bipartite vector `ψ` whose Schmidt coefficient is at least `ξ`. With
coefficient matrix `C` and left marginal `ρ = C Cᴴ`, the squared Schmidt coefficients are the
eigenvalues of `ρ`, so the kept vectors span the range of the spectral projection
`P = spectralProjectionGE ρ ξ²` onto the eigenvalues of `ρ` in `[ξ², ∞)`.

This file proves the facts about one such projection that the proof of Lemma `lem:trimming`
(lines 660–697) uses.

* The discarded part `((1 - P) ⊗ 1) ψ` has left marginal `(1 - P) ρ ≤ ξ²`, so all its Schmidt
  coefficients are below `ξ`.
* A vector whose left marginal is at most `c` pairs with a vector `φ` of Schmidt rank at most
  `k` to at most `√(c k) ‖φ‖`. This is the inequality of lines 676–680, "the inner product of a
  vector with largest Schmidt coefficient at most `ξ` with another vector of Schmidt rank `1`",
  summed over the `k` Schmidt terms of `φ`.
* `P` has rank at most `‖ψ‖² / ξ²` (line 690).
* `(P ⊗ 1) ψ = (1 ⊗ Q) ψ` for an orthogonal projection `Q` on the second factor, so applying
  `P` does not increase the Schmidt rank across a cut to the right of the second factor
  (lines 690–692).

## Main results

* `Matrix.norm_inner_le_of_posSemidef_smul_one_sub_leftMarginal`: the pairing bound.
* `Matrix.PosSemidef.posSemidef_smul_one_sub_one_sub_spectralProjectionGE_mul`: below the
  threshold, `(1 - P) ρ ≤ b`.
* `Matrix.posSemidef_smul_one_sub_leftMarginal_leftApply_one_sub`: the discarded part of `ψ`
  has left marginal at most `b`.
* `Matrix.norm_inner_leftApply_one_sub_spectralProjectionGE_le`: the discarded part pairs with
  a vector of Schmidt rank at most `k` to at most `√(b k)` times its norm.
* `Matrix.mul_rank_spectralProjectionGE_leftMarginal_le`: `b · rank P ≤ ‖ψ‖²`.
* `Matrix.exists_leftApply_spectralProjectionGE_eq_rightApply`: `(P ⊗ 1) ψ = (1 ⊗ Q) ψ`.

## References

* I. Arad, Z. Landau, U. Vazirani, T. Vidick, *Rigorous RG algorithms and area laws for low
  energy eigenstates in 1D*, arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`: Definition
  `def:trimming`, lines 642–656; Lemma `lem:trimming` and its proof, lines 660–697.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- **Pairing with a vector of small Schmidt coefficients** (arXiv:1602.08828v2,
`local_alg_arxiv_v2.tex`, lines 676–680). If the left marginal of `φ` is at most `c`, that is
every Schmidt coefficient of `φ` is at most `√c`, and `ψ` has Schmidt rank at most `k`, then
`‖⟨φ, ψ⟩‖ ≤ √(c k) ‖ψ‖`. The support projection `R` of the left marginal of `ψ` has rank at most
`k` and fixes `ψ`, so `⟨φ, ψ⟩ = ⟨(R ⊗ 1) φ, ψ⟩` and `‖(R ⊗ 1) φ‖² = tr (R ρ_φ R) ≤ c tr R`. -/
theorem norm_inner_le_of_posSemidef_smul_one_sub_leftMarginal {c : ℝ} (hc : 0 ≤ c) {k : ℕ}
    {φ ψ : EuclideanSpace ℂ (m × n)} (hφ : ((c : ℂ) • 1 - leftMarginal φ).PosSemidef)
    (hψ : HasSchmidtRankLE k (WithLp.ofLp ψ)) :
    ‖inner ℂ φ ψ‖ ≤ √(c * k) * ‖ψ‖ := by
  classical
  set C := schmidtCoeffMatrix (WithLp.ofLp ψ) with hC
  set hCC := isHermitian_mul_conjTranspose_self C
  set R := hCC.supportProj with hR
  have hRh : R.IsHermitian := hCC.supportProj_isHermitian
  have hRi : R * R = R := hCC.supportProj_idem
  have hRC : R * C = C := supportProj_mul_conjTranspose_mul_self C
  have hψR : leftApply R ψ = ψ := by
    change toEuclid (R * C) = ψ
    rw [hRC]
    rfl
  have hswap : inner ℂ φ ψ = inner ℂ (leftApply R φ) ψ := by
    conv_lhs => rw [← hψR]
    rw [inner_eq_trace_schmidtCoeffMatrix, inner_eq_trace_schmidtCoeffMatrix,
      schmidtCoeffMatrix_ofLp_leftApply, schmidtCoeffMatrix_ofLp_leftApply, conjTranspose_mul,
      hRh.eq, Matrix.mul_assoc]
  -- `‖(R ⊗ 1) φ‖² = tr (R ρ_φ R) ≤ c tr R = c rank C ≤ c k`
  have hsq : ‖leftApply R φ‖ ^ 2 ≤ c * k := by
    rw [sq_norm_eq_trace_leftMarginal_re]
    have hlm : leftMarginal (leftApply R φ) = R * leftMarginal φ * Rᴴ := by
      simp only [leftMarginal, schmidtCoeffMatrix_ofLp_leftApply, conjTranspose_mul,
        Matrix.mul_assoc]
    have htr := (hφ.mul_mul_conjTranspose_same R).trace_nonneg
    have hcR : R * ((c : ℂ) • 1) * Rᴴ = (c : ℂ) • R := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hRh.eq, hRi]
    rw [Matrix.mul_sub, Matrix.sub_mul, hcR, trace_sub, trace_smul, ← hlm] at htr
    have htrR : R.trace = (C.rank : ℂ) := by
      rw [hR, hCC.supportProj_trace, rank_self_mul_conjTranspose]
    rw [htrR] at htr
    have hre := (Complex.nonneg_iff.mp htr).1
    simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, mul_zero, sub_zero] at hre
    have hk : (C.rank : ℝ) ≤ k := by exact_mod_cast hψ
    nlinarith
  calc ‖inner ℂ φ ψ‖ = ‖inner ℂ (leftApply R φ) ψ‖ := by rw [hswap]
    _ ≤ ‖leftApply R φ‖ * ‖ψ‖ := norm_inner_le_norm _ _
    _ ≤ √(c * k) * ‖ψ‖ := by
        gcongr
        exact Real.le_sqrt_of_sq_le hsq

/-- **Below the threshold.** For a positive semidefinite `A` and `b ≥ 0`, the part of `A` below
the closed threshold `b` is at most `b`: `(1 - P) A ≤ b` for `P = spectralProjectionGE A b`.
On an eigenvalue `t ≥ b` the left side vanishes, and on `t < b` it is `t < b`. -/
theorem PosSemidef.posSemidef_smul_one_sub_one_sub_spectralProjectionGE_mul
    {A : Matrix m m ℂ} (hA : A.PosSemidef) {b : ℝ} (hb : 0 ≤ b) :
    ((b : ℂ) • 1 - (1 - spectralProjectionGE A b) * A).PosSemidef := by
  have hcont : ContinuousOn (fun t : ℝ ↦ if b ≤ t then (1 : ℝ) else 0) (spectrum ℝ A) := by
    rw [continuousOn_iff_continuous_domRestrict]; fun_prop
  have hP : (1 - spectralProjectionGE A b) * A =
      cfc (fun t : ℝ ↦ (1 - if b ≤ t then 1 else 0) * t) A := by
    rw [cfc_mul _ _ A (by fun_prop) (by fun_prop), cfc_sub _ _ A (by fun_prop) hcont,
      cfc_const_one ℝ A, cfc_id' ℝ A]
    rfl
  have hb1 : (b : ℂ) • (1 : Matrix m m ℂ) = cfc (fun _ : ℝ ↦ b) A := by
    rw [cfc_const b A hA.isHermitian.isSelfAdjoint, Algebra.algebraMap_eq_smul_one,
      ← Complex.coe_smul]
  rw [hP, hb1, ← cfc_sub _ _ A (by fun_prop) (by fun_prop)]
  apply nonneg_iff_posSemidef.mp
  apply cfc_nonneg
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hA.nonneg ht
  split_ifs with hbt
  · simpa using hb
  · simp only [sub_zero, one_mul, sub_nonneg]
    exact (not_le.mp hbt).le

/-- The left marginal of `((1 - P) ⊗ 1) ψ`, for `P = spectralProjectionGE ρ b` and `ρ` the left
marginal of `ψ`, is at most `b`: all Schmidt coefficients of the discarded part are at most
`√b` (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Definition `def:trimming`, lines 642–656,
and the first step of the proof of Lemma `lem:trimming`, lines 666–668). -/
theorem posSemidef_smul_one_sub_leftMarginal_leftApply_one_sub
    (ψ : EuclideanSpace ℂ (m × n)) {b : ℝ} (hb : 0 ≤ b) :
    ((b : ℂ) • 1 -
      leftMarginal (leftApply (1 - spectralProjectionGE (leftMarginal ψ) b) ψ)).PosSemidef := by
  set ρ := leftMarginal ψ
  set P := spectralProjectionGE ρ b
  have hρ := posSemidef_leftMarginal ψ
  have hp := hρ.isHermitian.isStarProjection_spectralProjectionGE b
  have hPh : P.IsHermitian := hp.isSelfAdjoint.isHermitian
  have hPi : P * P = P := hp.isIdempotentElem.eq
  have hc : ρ * P = P * ρ := hρ.isHermitian.commute_spectralProjectionGE b
  have hlm : leftMarginal (leftApply (1 - P) ψ) = (1 - P) * ρ := by
    have h1 : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hPh.eq]
    have h2 : (1 - P) * (1 - P) = 1 - P := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
        Matrix.mul_one, hPi]
      abel
    have h3 : ρ * (1 - P) = (1 - P) * ρ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hc]
    calc leftMarginal (leftApply (1 - P) ψ) = (1 - P) * ρ * (1 - P)ᴴ := by
          simp only [ρ, leftMarginal, schmidtCoeffMatrix_ofLp_leftApply, conjTranspose_mul,
            Matrix.mul_assoc]
      _ = (1 - P) * ρ := by rw [h1, Matrix.mul_assoc, h3, ← Matrix.mul_assoc, h2]
  rw [hlm]
  exact hρ.posSemidef_smul_one_sub_one_sub_spectralProjectionGE_mul hb

/-- **The discarded part pairs weakly with vectors of small Schmidt rank**
(arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, proof of Lemma `lem:trimming`, lines 666–680).
For `P = spectralProjectionGE ρ b` with `ρ` the left marginal of `ψ`, and `φ` of Schmidt rank at
most `k`, `‖⟨((1 - P) ⊗ 1) ψ, φ⟩‖ ≤ √(b k) ‖φ‖`. With `b = ξ²` this is `ξ √k ‖φ‖`. -/
theorem norm_inner_leftApply_one_sub_spectralProjectionGE_le (ψ : EuclideanSpace ℂ (m × n))
    {b : ℝ} (hb : 0 ≤ b) {k : ℕ} {φ : EuclideanSpace ℂ (m × n)}
    (hφ : HasSchmidtRankLE k (WithLp.ofLp φ)) :
    ‖inner ℂ (leftApply (1 - spectralProjectionGE (leftMarginal ψ) b) ψ) φ‖ ≤
      √(b * k) * ‖φ‖ :=
  norm_inner_le_of_posSemidef_smul_one_sub_leftMarginal hb
    (posSemidef_smul_one_sub_leftMarginal_leftApply_one_sub ψ hb) hφ

/-- **Few coefficients above the threshold** (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`,
line 690). The projection onto the left Schmidt vectors with squared Schmidt coefficient at
least `b` has rank at most `‖ψ‖² / b`: `b · rank P ≤ ‖ψ‖²`. -/
theorem mul_rank_spectralProjectionGE_leftMarginal_le (ψ : EuclideanSpace ℂ (m × n)) (b : ℝ) :
    b * (spectralProjectionGE (leftMarginal ψ) b).rank ≤ ‖ψ‖ ^ 2 := by
  rw [sq_norm_eq_trace_leftMarginal_re]
  exact (posSemidef_leftMarginal ψ).mul_rank_spectralProjectionGE_le_trace b

/-- **The threshold projection acts on the second factor too** (arXiv:1602.08828v2,
`local_alg_arxiv_v2.tex`, lines 690–692). For `P = spectralProjectionGE ρ b` with `ρ` the left
marginal of `ψ`, there is an orthogonal projection `Q` on the second factor, of rank at most that
of `P`, with `(P ⊗ 1) ψ = (1 ⊗ Q) ψ`; so applying `P` does not increase the Schmidt rank across
any cut inside the second factor. -/
theorem exists_leftApply_spectralProjectionGE_eq_rightApply (ψ : EuclideanSpace ℂ (m × n))
    (b : ℝ) :
    ∃ Q : Matrix n n ℂ, Q.IsHermitian ∧ Q * Q = Q ∧
      Q.rank ≤ (spectralProjectionGE (leftMarginal ψ) b).rank ∧
      leftApply (spectralProjectionGE (leftMarginal ψ) b) ψ = rightApply Q ψ := by
  have hρ := posSemidef_leftMarginal ψ
  have hp := hρ.isHermitian.isStarProjection_spectralProjectionGE b
  obtain ⟨Q, hQh, hQi, hQr, hPQ⟩ := exists_mul_eq_mul_transpose_of_commute
    hp.isSelfAdjoint.isHermitian hp.isIdempotentElem.eq
    (hρ.isHermitian.commute_spectralProjectionGE b).symm
  exact ⟨Q, hQh, hQi, hQr, by rw [leftApply, rightApply, hPQ]⟩

end Matrix
