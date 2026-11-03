/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.StoppedHalving
import QICLean.Analysis.RandomRangeSubspaceDimension
import QICLean.Analysis.StoppedHalfSamplingIteration
import QICLean.Analysis.FiniteFamilyImageProjection
import QICLean.Analysis.ViableSubspaceSpectralProjector

/-!
# Unconditional dimensions of stopped half-sampling rounds

The actual quotient sample, fixed-family image and collective trim decrease
rank independently of whether a sample is viable. This supports the
resampling description in ALVV, arXiv:1602.08828v2, lines 749–755.
No target, gap, viability or sampling-success premise is used.
-/

open Module
open scoped Matrix.Norms.L2Operator

namespace Entropy

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  {n : V → ℕ} {d : ℕ}

private theorem matrix_rank_eq_finrank_range {σ τ : Type*}
    [Finite σ] [Fintype τ] [DecidableEq τ]
    (P : Matrix σ τ ℂ) :
    P.rank = finrank ℂ (Matrix.toEuclideanLin P).range := by
  classical
  let := Fintype.ofFinite σ
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact P.rank_eq_finrank_range_toLin
    (EuclideanSpace.basisFun σ ℂ).toBasis (EuclideanSpace.basisFun τ ℂ).toBasis

/-- The literal canonical collective trim cannot increase the rank of its
input range. This also holds at zero rank and for any real threshold.
Supporting ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem finrank_trimMatrixRange_le_rank (e : Fin d ≃ SiteConfig n)
    (cuts : ℕ → Finset V) (xi : ℝ) (k : ℕ)
    (P : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    finrank ℂ (trimMatrixRange e cuts xi k P) ≤ P.rank := by
  rw [trimMatrixRange_eq_of_orthonormalBasis e cuts xi k P
    (stdOrthonormalBasis ℂ (Matrix.toEuclideanLin P).range),
    trimSubspace_eq_map_of_orthonormalBasis, matrix_rank_eq_finrank_range]
  exact Submodule.finrank_map_le _ _

private theorem rank_projectionMatrix {σ : Type*} [Fintype σ] [DecidableEq σ]
    (S : Submodule ℂ (EuclideanSpace ℂ σ)) :
    ((Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm S.starProjection).rank =
      finrank ℂ S := by
  rw [matrix_rank_eq_finrank_range]
  change finrank ℂ ((Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ))
    ((Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm S.starProjection)).toLinearMap.range = _
  rw [StarAlgEquiv.apply_symm_apply, Submodule.range_starProjection]

private theorem rank_familySupportProj_mul_le_card_mul_rank
    (F : ι → Matrix (SiteConfig n) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.familySupportProj (fun i ↦ F i * Q)).rank ≤ Fintype.card ι * Q.rank := by
  classical
  rw [matrix_rank_eq_finrank_range, Matrix.range_toEuclideanLin_familySupportProj]
  calc
    _ ≤ ∑ i, finrank ℂ (Matrix.toEuclideanLin (F i * Q)).range :=
      Submodule.finrank_iSup_le_sum _
    _ ≤ ∑ _i : ι, Q.rank := Finset.sum_le_sum fun i _ ↦ by
      rw [← matrix_rank_eq_finrank_range]
      exact Matrix.rank_mul_le_right (F i) Q
    _ = Fintype.card ι * Q.rank := by simp

/-- The literal stopped round halves rank when active and retains the
input otherwise, for every seed. No viability premise is required.
Supporting ALVV, arXiv:1602.08828v2, the resampling description, lines 749–755. -/
theorem rank_canonicalHalfSampleTrimMatrix_le
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V)
    (xi : ℝ) (k D threshold : ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (hcard : Fintype.card ι ≤ D ^ 2)
    (P : Matrix (Fin d) (Fin d) ℂ) (U : Matrix.rankUnitaryProduct d) :
    (canonicalHalfSampleTrimMatrix e cuts xi k D threshold F P U).rank ≤
      if threshold ≤ P.rank then P.rank / 2 else P.rank := by
  classical
  by_cases hactive : threshold ≤ P.rank
  · let s := P.rank / (2 * D ^ 2)
    let sample := Matrix.randomRangeSubspace P s U
    let Q := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm sample.starProjection
    let Y := Matrix.familySupportProj (fun i ↦ F i * Q)
    have hsample : finrank ℂ sample = s := by
      change finrank ℂ (Matrix.randomRangeSubspace P s U) = s
      rw [Matrix.finrank_randomRangeSubspace, Nat.min_eq_left (Nat.div_le_self _ _)]
    have hY : Y.rank ≤ P.rank / 2 := by
      calc
        _ ≤ Fintype.card ι * Q.rank := rank_familySupportProj_mul_le_card_mul_rank F Q
        _ = Fintype.card ι * s := by rw [rank_projectionMatrix, hsample]
        _ ≤ D ^ 2 * s := Nat.mul_le_mul_right s hcard
        _ ≤ P.rank / 2 := by
          apply (Nat.le_div_iff_mul_le Nat.zero_lt_two).mpr
          have hh := Nat.div_mul_le_self P.rank (2 * D ^ 2)
          change s * (2 * D ^ 2) ≤ P.rank at hh
          nlinarith only [hh]
    simp only [canonicalHalfSampleTrimMatrix, ite_eq_left hactive]
    rw [Matrix.rank_reindex, rank_projectionMatrix]
    exact (finrank_trimMatrixRange_le_rank e cuts xi k Y).trans hY
  · simp only [canonicalHalfSampleTrimMatrix, ite_eq_right hactive, le_refl]

/-- In an active round the next matrix range, transported back to native
coordinates, is exactly the collective trim used by the step. No projection
premise on the input matrix is needed. Supporting ALVV,
arXiv:1602.08828v2, the resampling description, lines 749–755. -/
theorem map_range_canonicalHalfSampleTrimMatrix_of_active
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V)
    (xi : ℝ) (k D threshold : ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (U : Matrix.rankUnitaryProduct d)
    (hactive : threshold ≤ P.rank) :
    let S := trimMatrixRange e cuts xi k (Matrix.familySupportProj (fun i ↦ F i *
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
        (Matrix.randomRangeSubspace P (P.rank / (2 * D ^ 2)) U).starProjection))
    (Matrix.toEuclideanLin (canonicalHalfSampleTrimMatrix e cuts xi k D threshold F P U)).range.map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap = S := by
  intro S
  rw [canonicalHalfSampleTrimMatrix, ite_eq_left hactive]
  change (Matrix.toEuclideanLin
    (((Matrix.toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ)).symm S.starProjection).submatrix
      e e)).range.map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap = S
  rw [Matrix.map_range_toEuclideanLin_submatrix]
  change ((Matrix.toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ))
    ((Matrix.toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ)).symm
      S.starProjection)).toLinearMap.range = S
  rw [StarAlgEquiv.apply_symm_apply, Submodule.range_starProjection]

/-- A predetermined number of actual stopped rounds reduces rank below the
threshold, for every entire seed sequence. Auxiliary for ALVV,
arXiv:1602.08828v2, lines 749–755; no success event is assumed. -/
theorem rank_canonicalHalfSampleTrimIterate_lt
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V)
    (xi : ℝ) (k D threshold : ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (hcard : Fintype.card ι ≤ D ^ 2)
    (P : Matrix (Fin d) (Fin d) ℂ) (U : ℕ → Matrix.rankUnitaryProduct d)
    (rounds : ℕ) (hthreshold : 2 ≤ threshold) (hzero : P.rank ≤ 2 ^ rounds) :
    (canonicalHalfSampleTrimIterate e cuts xi k D threshold F P U rounds).rank < threshold := by
  apply Nat.lt_threshold_of_stopped_halving
    (fun i ↦ (canonicalHalfSampleTrimIterate e cuts xi k D threshold F P U i).rank)
    threshold rounds hthreshold hzero
  intro i _
  exact rank_canonicalHalfSampleTrimMatrix_le e cuts xi k D threshold F hcard _ _

/-- The chain ambient dimension yields a prescribed rank-stopping count.
This counts rounds only, not their computational cost. Supporting ALVV,
arXiv:1602.08828v2, the proof of `t:alg1`, lines 1783–1817. -/
theorem rank_canonicalHalfSampleTrimIterate_chain_lt
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V)
    (xi : ℝ) (k D threshold : ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (hcard : Fintype.card ι ≤ D ^ 2)
    (P : Matrix (Fin d) (Fin d) ℂ) (U : ℕ → Matrix.rankUnitaryProduct d)
    (q L : ℕ) (hthreshold : 2 ≤ threshold) (hzero : P.rank ≤ q ^ L) :
    (canonicalHalfSampleTrimIterate e cuts xi k D threshold F P U (q * L)).rank < threshold := by
  apply Nat.lt_threshold_of_stopped_halving_chain
    (fun i ↦ (canonicalHalfSampleTrimIterate e cuts xi k D threshold F P U i).rank)
    threshold q L hthreshold hzero
  intro i _
  exact rank_canonicalHalfSampleTrimMatrix_le e cuts xi k D threshold F hcard _ _

end Entropy
