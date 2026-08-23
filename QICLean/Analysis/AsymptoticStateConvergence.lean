/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Algebra.FrobeniusHilbert
import QICLean.Analysis.TraceNormAbs
import QICLean.Analysis.TraceNormContractionCoefficient
import QICLean.Channel.Peripheral.CesaroRecurrence
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Trace-norm convergence towards asymptotic states

This file formalizes the upper half of Wolf's comparison between trace-norm
convergence of states and Hilbert--Schmidt operator-norm convergence of a
positive trace-preserving map. It proves the exact algebraic identities used in
Equation (8.114), the norm estimates in Equations (8.115)--(8.116), and the
upper bound in Equation (8.112). The converse bound in Equation (8.113) remains
separate.

## References

Michael M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8,
Proposition "Convergence towards asymptotic states", Equations (8.112)--(8.117);
local source `Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1319--1364.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder

noncomputable section

namespace Matrix

variable {D : ℕ}

/-- The sum of the squared singular values of a matrix is its squared
Hilbert--Schmidt norm. -/
lemma sum_sq_singularValues_eq_frobenius_sq
    (A : Matrix (Fin D) (Fin D) ℂ) :
    (∑ i : Fin D, (Matrix.toEuclideanLin A).singularValues i ^ 2) = ‖A‖ ^ 2 := by
  rw [Finset.sum_congr rfl (fun i _ ↦
    LinearMap.sq_singularValues_fin (Matrix.toEuclideanLin A)
      finrank_euclideanSpace_fin i)]
  rw [← (Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues
    finrank_euclideanSpace_fin]
  rw [Matrix.adjoint_toEuclideanLin_comp_self]
  change ((LinearMap.trace ℂ _ (Matrix.toEuclideanLin (Aᴴ * A))).re) = _
  rw [show LinearMap.trace ℂ _ (Matrix.toEuclideanLin (Aᴴ * A)) =
      Matrix.trace (Aᴴ * A) by
    exact Matrix.trace_toLin_eq (Aᴴ * A) (EuclideanSpace.basisFun (Fin D) ℂ).toBasis]
  exact Matrix.trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq A

/-- Wolf's Schatten-norm comparison `‖A‖₁ ≤ √d ‖A‖₂` at the `p = 1`,
`q = 2` instance of Equation (8.7). -/
theorem traceNorm_le_sqrt_card_mul_frobenius
    (A : Matrix (Fin D) (Fin D) ℂ) :
    traceNorm A ≤ Real.sqrt D * ‖A‖ := by
  rw [traceNorm_eq_sum_fin]
  calc
    (∑ i : Fin D, (Matrix.toEuclideanLin A).singularValues i) =
        ∑ i : Fin D, (Matrix.toEuclideanLin A).singularValues i * 1 := by simp
    _ ≤ Real.sqrt (∑ i : Fin D, (Matrix.toEuclideanLin A).singularValues i ^ 2) *
        Real.sqrt (∑ _i : Fin D, (1 : ℝ) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ = Real.sqrt D * ‖A‖ := by
      rw [sum_sq_singularValues_eq_frobenius_sq]
      simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg A), mul_comm]

/-- Wolf's Hilbert--Schmidt `2 → 2` operator norm of a matrix
superoperator, transported through column vectorization. This is the same
operator norm as the largest-singular-value norm of its transfer matrix. -/
def hilbertSchmidtOperatorNorm
    (S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (frobeniusEuclideanMap S)‖

/-- The defining application bound for the Hilbert--Schmidt `2 → 2`
operator norm. -/
lemma frobenius_norm_apply_le_hilbertSchmidtOperatorNorm
    (S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    ‖S X‖ ≤ hilbertSchmidtOperatorNorm S * ‖X‖ := by
  have h := (LinearMap.toContinuousLinearMap (frobeniusEuclideanMap S)).le_opNorm
    (frobeniusEquivEuclidean (Fin D) (Fin D) X)
  simpa only [hilbertSchmidtOperatorNorm, frobeniusEuclideanMap_apply,
    LinearMap.coe_toContinuousLinearMap', LinearIsometryEquiv.norm_map] using h

/-- The Hilbert--Schmidt distance between orthogonal pure-state projectors is
`√2`, the equality used in Wolf Equation (8.116). -/
lemma frobenius_norm_pureStateProj_sub_eq_sqrt_two
    {ψ φ : Fin D → ℂ} (hψ : IsUnitVector ψ) (hφ : IsUnitVector φ)
    (horth : AreOrthogonal ψ φ) :
    ‖pureStateProj ψ - pureStateProj φ‖ = Real.sqrt 2 := by
  let P := pureStateProj ψ
  let Q := pureStateProj φ
  have hPH : P.IsHermitian := (pureStateProj_posSemidef ψ).isHermitian
  have hQH : Q.IsHermitian := (pureStateProj_posSemidef φ).isHermitian
  have hPP : P * P = P := by
    change vecMulVec ψ (fun p => star (ψ p)) * vecMulVec ψ (fun p => star (ψ p)) =
      vecMulVec ψ (fun p => star (ψ p))
    rw [Matrix.vecMulVec_mul_vecMulVec, hψ, one_smul]
  have hQQ : Q * Q = Q := by
    change vecMulVec φ (fun p => star (φ p)) * vecMulVec φ (fun p => star (φ p)) =
      vecMulVec φ (fun p => star (φ p))
    rw [Matrix.vecMulVec_mul_vecMulVec, hφ, one_smul]
  have hPQ : P * Q = 0 := by
    change vecMulVec ψ (fun p => star (ψ p)) * vecMulVec φ (fun p => star (φ p)) = 0
    rw [Matrix.vecMulVec_mul_vecMulVec, horth, zero_smul]
    ext
    simp [Matrix.vecMulVec_apply]
  have hQP : Q * P = 0 := by
    have hs := congrArg star hPQ
    simpa [star_mul, Matrix.star_eq_conjTranspose, hPH.eq, hQH.eq] using hs
  have hsq : ‖P - Q‖ ^ 2 = 2 := by
    rw [← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq]
    rw [(hPH.sub hQH).eq]
    simp only [sub_mul, mul_sub, hPP, hQQ, hPQ, hQP, sub_zero, zero_sub,
      sub_neg_eq_add]
    have hPtr : P.trace = 1 := by
      change (pureStateProj ψ).trace = 1
      rw [trace_pureStateProj, dotProduct_comm]
      exact hψ
    have hQtr : Q.trace = 1 := by
      change (pureStateProj φ).trace = 1
      rw [trace_pureStateProj, dotProduct_comm]
      exact hφ
    rw [trace_add, hPtr, hQtr]
    norm_num
  change ‖P - Q‖ = Real.sqrt 2
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [norm_nonneg (P - Q)]

/-- The orthogonal-pure-state supremum in Wolf Lemma 8.3 is bounded by the
Hilbert--Schmidt operator norm with the exact `√d √2` constant used in
Equations (8.115)--(8.116). -/
lemma sSup_orthogonalPureStateTraceNorms_le_hilbertSchmidtOperatorNorm
    (S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) :
    sSup (orthogonalPureStateTraceNorms S) ≤
      Real.sqrt D * hilbertSchmidtOperatorNorm S * Real.sqrt 2 := by
  by_cases hS : (orthogonalPureStateTraceNorms S).Nonempty
  · apply csSup_le hS
    rintro r ⟨ψ, φ, hψ, hφ, horth, rfl⟩
    calc
      traceNorm (S (pureStateProj ψ - pureStateProj φ)) ≤
          Real.sqrt D * ‖S (pureStateProj ψ - pureStateProj φ)‖ :=
        traceNorm_le_sqrt_card_mul_frobenius _
      _ ≤ Real.sqrt D *
          (hilbertSchmidtOperatorNorm S * ‖pureStateProj ψ - pureStateProj φ‖) :=
        mul_le_mul_of_nonneg_left
          (frobenius_norm_apply_le_hilbertSchmidtOperatorNorm S _) (Real.sqrt_nonneg _)
      _ = Real.sqrt D * hilbertSchmidtOperatorNorm S * Real.sqrt 2 := by
        rw [frobenius_norm_pureStateProj_sub_eq_sqrt_two hψ hφ horth]
        ring
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, Real.sSup_empty]
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (Real.sqrt_nonneg _)

private lemma half_sqrt_mul_sqrt_two (a h : ℝ) (ha : 0 ≤ a) :
    (1 / 2 : ℝ) * (Real.sqrt a * h * Real.sqrt 2) =
      Real.sqrt (a / 2) * h := by
  rw [Real.sqrt_div ha]
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsqrt2ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hsqrt2ne]
  rw [pow_two, hsqrt2]
  ring

/-- Wolf's `Δ_T(ρ) = ‖ρ - T_φ(ρ)‖₁`: trace-norm distance to the peripheral
spectral projection.

Source: Wolf, Equation (8.112), definition immediately before the displayed
bound; local source lines 1323--1328. -/
def traceNormAsymptoticDistance
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (ρ : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  traceNorm (ρ - T.peripheralProjection ρ)

/-- The peripheral projection commutes with every iterate of `T`.

This is the iterated form of the first identity on Wolf line 1337. -/
theorem peripheralProjection_comp_pow
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (n : ℕ) :
    T.peripheralProjection ∘ₗ (T ^ n) = (T ^ n) ∘ₗ T.peripheralProjection := by
  simpa only [Module.End.mul_eq_comp] using
    (T.commute_peripheralProjection.pow_right n).eq

/-- The phase-weighted peripheral map annihilates Wolf's non-peripheral
remainder `ρ - T_φ(ρ)`.

This is Wolf's identity `T_\varphi T_φ = T_\varphi` on source line 1337,
applied to the complement of the peripheral projection. -/
@[simp]
theorem peripheralWeightedProjection_apply_sub_peripheralProjection
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (ρ : Matrix (Fin D) (Fin D) ℂ) :
    T.peripheralWeightedProjection (ρ - T.peripheralProjection ρ) = 0 := by
  rw [Module.End.peripheralWeightedProjection, LinearMap.comp_apply, map_sub,
    T.peripheralProjection_apply_peripheralProjection, sub_self, map_zero]

/-- Every positive power of the phase-weighted peripheral map annihilates
Wolf's non-peripheral remainder. -/
@[simp]
theorem peripheralWeightedProjection_pow_apply_sub_peripheralProjection
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (ρ : Matrix (Fin D) (Fin D) ℂ) {n : ℕ} (hn : 0 < n) :
    (T.peripheralWeightedProjection ^ n) (ρ - T.peripheralProjection ρ) = 0 := by
  cases n with
  | zero => simp at hn
  | succ n =>
      rw [pow_succ, Module.End.mul_apply,
        peripheralWeightedProjection_apply_sub_peripheralProjection, map_zero]

/-- Wolf's numerator identity preceding Equation (8.114): for every positive
iterate, `Δ_T(Tⁿρ)` is the trace norm of `Tⁿ` applied to the non-peripheral
remainder.

Source: Wolf, local source lines 1336--1344. -/
theorem traceNormAsymptoticDistance_pow_eq
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (ρ : Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    traceNormAsymptoticDistance T ((T ^ n) ρ) =
      traceNorm ((T ^ n) (ρ - T.peripheralProjection ρ)) := by
  have hcomm : T.peripheralProjection ((T ^ n) ρ) =
      (T ^ n) (T.peripheralProjection ρ) := by
    simpa only [LinearMap.comp_apply] using congrArg
      (fun f : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) ↦ f ρ)
      (peripheralProjection_comp_pow T n)
  rw [traceNormAsymptoticDistance, hcomm, map_sub]

/-- Wolf's second numerator identity preceding Equation (8.114): for every
positive iterate, subtracting the corresponding power of the asymptotic
dynamics does not change its action on the non-peripheral remainder.

Source: Wolf, local source lines 1336--1344. -/
theorem traceNormAsymptoticDistance_pow_eq_sub_peripheralWeightedProjection_pow
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (ρ : Matrix (Fin D) (Fin D) ℂ) {n : ℕ} (hn : 0 < n) :
    traceNormAsymptoticDistance T ((T ^ n) ρ) =
      traceNorm (((T ^ n) - T.peripheralWeightedProjection ^ n)
        (ρ - T.peripheralProjection ρ)) := by
  rw [traceNormAsymptoticDistance_pow_eq, LinearMap.sub_apply,
    peripheralWeightedProjection_pow_apply_sub_peripheralProjection T ρ hn, sub_zero]

/-- **Wolf Proposition, Equation (8.112).** For a positive trace-preserving
map and a density matrix `ρ`, the distance of the positive iterate `Tⁿρ` from
the asymptotic subspace is bounded by the Hilbert--Schmidt `2 → 2` norm of
`Tⁿ - T_ϕⁿ`, with Wolf's exact `√(d/2)` constant.

The explicit hypothesis `0 < n` records Wolf's positive-natural convention:
with Lean's `0 ∈ ℕ`, the printed formula would be false at `n = 0` because
both zeroth powers in the superoperator difference are the identity.

Source: Wolf, Equations (8.112), (8.114)--(8.116); local source lines
1323--1353. -/
theorem traceNormAsymptoticDistance_pow_le_hilbertSchmidtOperatorNorm
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ ∈ densityMatrices D)
    {n : ℕ} (hn : 0 < n) :
    traceNormAsymptoticDistance T ((T ^ n) ρ) ≤
      Real.sqrt ((D : ℝ) / 2) *
        hilbertSchmidtOperatorNorm
          ((T ^ n) - T.peripheralWeightedProjection ^ n) *
        traceNormAsymptoticDistance T ρ := by
  let S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    (T ^ n) - T.peripheralWeightedProjection ^ n
  have hDpos : 0 < D := by
    simpa using Fintype.card_pos_iff.mpr
      (Matrix.nonempty_of_trace_eq_one ρ hρ.2)
  let : NeZero D := ⟨Nat.ne_of_gt hDpos⟩
  have hρφ : T.peripheralProjection ρ ∈ densityMatrices D :=
    ⟨hPos.peripheralProjection_isPositiveMap hTP ρ hρ.1,
      by rw [hPos.peripheralProjection_isTracePreservingMap hTP, hρ.2]⟩
  by_cases heq : ρ = T.peripheralProjection ρ
  · have hsub : ρ - T.peripheralProjection ρ = 0 := sub_eq_zero.mpr heq
    have hdist : traceNormAsymptoticDistance T ρ = 0 := by
      rw [traceNormAsymptoticDistance, hsub, traceNorm_zero]
    rw [hdist, mul_zero]
    rw [traceNormAsymptoticDistance_pow_eq_sub_peripheralWeightedProjection_pow T ρ hn,
      hsub, map_zero, traceNorm_zero]
  · have hden : 0 < traceNorm (ρ - T.peripheralProjection ρ) :=
      (traceNorm_pos_iff _).2 (sub_ne_zero.mpr heq)
    have hratio :=
      traceNorm_map_sub_div_traceNorm_le_half_sSup_orthogonal
        S hρ hρφ heq
    rw [← map_sub] at hratio
    have hsup :=
      sSup_orthogonalPureStateTraceNorms_le_hilbertSchmidtOperatorNorm S
    have hratio' :
        traceNorm (S (ρ - T.peripheralProjection ρ)) /
            traceNorm (ρ - T.peripheralProjection ρ) ≤
          (1 / 2 : ℝ) *
            (Real.sqrt D * hilbertSchmidtOperatorNorm S * Real.sqrt 2) :=
      hratio.trans (mul_le_mul_of_nonneg_left hsup (by norm_num))
    rw [half_sqrt_mul_sqrt_two (D : ℝ) (hilbertSchmidtOperatorNorm S)
      (Nat.cast_nonneg D)] at hratio'
    have hmul := (div_le_iff₀ hden).mp hratio'
    rw [traceNormAsymptoticDistance_pow_eq_sub_peripheralWeightedProjection_pow T ρ hn,
      traceNormAsymptoticDistance]
    simpa only [S] using hmul

end Matrix
