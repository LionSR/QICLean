/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.MatrixSqrt
import QICLean.Channel.FixedPoint.MaximalSupportBasic

/-!
# Maximum-rank stationary support for positive maps

This file transfers the source-general maximal-support stationary point to
every maximum-rank stationary density matrix.  No Kraus representation or
complete positivity is used.

The result is the support prerequisite in Wolf Corollary 6.7: for every
maximum-rank stationary density matrix `rho`, every fixed point is supported
on `supp(rho)`.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder MatrixOrder Topology
open Matrix

noncomputable section

namespace IsPositiveMap

variable {D : Nat}

local notation "Mat" => Matrix (Fin D) (Fin D) Complex

private theorem rank_stationaryProj {rho : Mat} (hrho : rho.PosSemidef) :
    (Kraus.stationaryProj hrho).rank = rho.rank := by
  have hrankRe :=
    (Kraus.isOrthogonalProjection_stationaryProj hrho).1.rank_eq_trace_re_of_idem
      (Kraus.isOrthogonalProjection_stationaryProj hrho).2
  have htrace : (Kraus.stationaryProj hrho).trace = (rho.rank : Complex) := by
    simpa [Kraus.stationaryProj] using hrho.supportProj_trace
  rw [htrace] at hrankRe
  exact_mod_cast hrankRe

private theorem trace_stationaryProj {rho : Mat} (hrho : rho.PosSemidef) :
    (Kraus.stationaryProj hrho).trace = (rho.rank : Complex) := by
  simpa [Kraus.stationaryProj] using hrho.supportProj_trace

/-- The support of every maximum-rank stationary density matrix carries the
entire fixed-point space of a positive trace-preserving map.

This is the exact `every maximum rank` support step used in Wolf Corollary
6.7.  The proof compares the chosen matrix with the canonical maximal-support
point through ranks of their support projections. -/
theorem maximalSupport_of_maximalRank
    {T : Mat →ₗ[Complex] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    {rho : Mat} (hrho : rho.PosSemidef) (hrhoFix : T rho = rho)
    (hrhoMax : ∀ sigma : Mat, sigma.PosSemidef → sigma.trace = 1 →
      T sigma = sigma → sigma.rank ≤ rho.rank) :
    ∀ X : Mat, T X = X →
      Kraus.stationaryProj hrho * X * Kraus.stationaryProj hrho = X := by
  classical
  let hbounded := hT.hasBoundedOrbits_of_tracePreserving hTP
  let rho0 := LinearMap.meanErgodicProjection
    (𝕜 := ℂ) (E := Matrix (Fin D) (Fin D) ℂ) T hbounded 1
  obtain ⟨hrho0, hrho0Fix, hmax⟩ :
      ∃ hrho0 : rho0.PosSemidef, T rho0 = rho0 ∧
        ∀ X : Mat, T X = X →
          Kraus.stationaryProj hrho0 * X * Kraus.stationaryProj hrho0 = X := by
    simpa only [rho0, hbounded] using hT.exists_maximalSupport_fixedPoint hTP
  set Q0 : Mat := Kraus.stationaryProj hrho0
  set P : Mat := Kraus.stationaryProj hrho
  have hQ0herm : Q0ᴴ = Q0 :=
    (Kraus.isOrthogonalProjection_stationaryProj hrho0).1.eq
  have hPherm : Pᴴ = P :=
    (Kraus.isOrthogonalProjection_stationaryProj hrho).1.eq
  have hQ0idem : Q0 * Q0 = Q0 :=
    (Kraus.isOrthogonalProjection_stationaryProj hrho0).2
  have hPidem : P * P = P :=
    (Kraus.isOrthogonalProjection_stationaryProj hrho).2
  rcases eq_or_ne rho0 0 with hrho0Zero | hrho0Ne
  · have hQ0zero : Q0 = 0 := by
      refine Matrix.ext_of_mulVec_single fun j ↦ ?_
      rw [show Q0 = Kraus.stationaryProj hrho0 from rfl, Matrix.zero_mulVec]
      exact hrho0.supportProj_mulVec_eq_zero_of_mulVec_eq_zero _ (by
        rw [hrho0Zero, Matrix.zero_mulVec])
    intro X hX
    have hXzero : X = 0 := by
      have h := hmax X hX
      rw [hQ0zero] at h
      simpa using h.symm
    rw [hXzero, Matrix.mul_zero, Matrix.zero_mul]
  · have hcNonneg : (0 : Complex) ≤ rho0.trace := hrho0.trace_nonneg
    have hcNe : rho0.trace ≠ 0 := by
      intro hzero
      have hSstar : (CFC.sqrt rho0)ᴴ = CFC.sqrt rho0 :=
        Matrix.conjTranspose_cfc_sqrt rho0
      have hSS : CFC.sqrt rho0 * CFC.sqrt rho0 = rho0 :=
        CFC.sqrt_mul_sqrt_self rho0 hrho0.nonneg
      have htrace : ((CFC.sqrt rho0)ᴴ * CFC.sqrt rho0).trace = 0 := by
        rw [hSstar, hSS]
        exact hzero
      have hsqrtZero : CFC.sqrt rho0 = 0 :=
        Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htrace
      exact hrho0Ne (by rw [← hSS, hsqrtZero, Matrix.mul_zero])
    have him : rho0.trace.im = 0 :=
      ((Complex.nonneg_iff.mp hcNonneg).2).symm
    have hreNonneg : 0 ≤ rho0.trace.re :=
      (Complex.nonneg_iff.mp hcNonneg).1
    have hreNe : rho0.trace.re ≠ 0 := by
      intro h
      exact hcNe (Complex.ext h him)
    have htraceReal : rho0.trace = ((rho0.trace.re : Real) : Complex) :=
      Complex.ext rfl (by simp [him])
    let c : Real := (rho0.trace.re)⁻¹
    have hcNonnegReal : 0 ≤ c := inv_nonneg.mpr hreNonneg
    have hcNeReal : c ≠ 0 := inv_ne_zero hreNe
    let sigma : Mat := ((c : Real) : Complex) • rho0
    have hsigmaPsd : sigma.PosSemidef := by
      have h := hrho0.conjTranspose_mul_mul_same
        (((Real.sqrt c : Real) : Complex) • (1 : Mat))
      have heq : (((Real.sqrt c : Real) : Complex) • (1 : Mat))ᴴ * rho0 *
          (((Real.sqrt c : Real) : Complex) • (1 : Mat)) = sigma := by
        rw [show sigma = ((c : Real) : Complex) • rho0 from rfl,
          Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
          smul_smul]
        congr 1
        rw [show star (((Real.sqrt c : Real) : Complex)) =
          ((Real.sqrt c : Real) : Complex) by simp]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hcNonnegReal]
      rw [← heq]
      exact h
    have hsigmaTrace : sigma.trace = 1 := by
      rw [show sigma = ((c : Real) : Complex) • rho0 from rfl,
        Matrix.trace_smul, htraceReal, smul_eq_mul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ hreNe, Complex.ofReal_one]
    have hsigmaFix : T sigma = sigma := by
      rw [show sigma = ((c : Real) : Complex) • rho0 from rfl,
        T.map_smul, hrho0Fix]
    have hsigmaRank : sigma.rank = rho0.rank := by
      rw [show sigma = ((c : Real) : Complex) • rho0 from rfl,
        Matrix.smul_eq_diagonal_mul]
      refine Matrix.rank_mul_eq_right_of_det_ne_zero _ _ ?_
      rw [Matrix.det_diagonal, Finset.prod_const]
      exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hcNeReal)
    have hrankLower : rho0.rank ≤ rho.rank :=
      hsigmaRank ▸ hrhoMax sigma hsigmaPsd hsigmaTrace hsigmaFix
    have hQ0rhoQ0 : Q0 * rho * Q0 = rho := hmax rho hrhoFix
    have hrankUpper : rho.rank ≤ rho0.rank := by
      calc
        rho.rank = (Q0 * rho * Q0).rank := by rw [hQ0rhoQ0]
        _ ≤ (Q0 * rho).rank := Matrix.rank_mul_le_left _ _
        _ ≤ Q0.rank := Matrix.rank_mul_le_left _ _
        _ = rho0.rank := rank_stationaryProj hrho0
    have hrankEq : rho.rank = rho0.rank :=
      le_antisymm hrankUpper hrankLower
    have hrhoQ0 : rho * Q0 = rho := by
      conv_lhs => rw [← hQ0rhoQ0]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hQ0idem, ← Matrix.mul_assoc]
      exact hQ0rhoQ0
    have hPQ0 : P * Q0 = P := by
      have hsub : P * (1 - Q0) = 0 := by
        refine Matrix.ext_of_mulVec_single fun j ↦ ?_
        rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
        refine hrho.supportProj_mulVec_eq_zero_of_mulVec_eq_zero _ ?_
        rw [Matrix.mulVec_mulVec,
          show rho * (1 - Q0) = 0 by
            rw [Matrix.mul_sub, Matrix.mul_one, hrhoQ0, sub_self],
          Matrix.zero_mulVec]
      rw [Matrix.mul_sub, Matrix.mul_one] at hsub
      exact (sub_eq_zero.mp hsub).symm
    have hQ0P : Q0 * P = P := by
      have h := congrArg Matrix.conjTranspose hPQ0
      rwa [Matrix.conjTranspose_mul, hQ0herm, hPherm] at h
    have hR : (Q0 - P) * (Q0 - P) = Q0 - P := by
      rw [mul_sub (Q0 - P) Q0 P, sub_mul Q0 P Q0,
        sub_mul Q0 P P, hQ0idem, hPQ0, hQ0P, hPidem]
      abel
    have hRstar : (Q0 - P)ᴴ = Q0 - P := by
      rw [Matrix.conjTranspose_sub, hQ0herm, hPherm]
    have hRtrace : ((Q0 - P)ᴴ * (Q0 - P)).trace = 0 := by
      rw [hRstar, hR, Matrix.trace_sub,
        show Q0 = Kraus.stationaryProj hrho0 from rfl,
        show P = Kraus.stationaryProj hrho from rfl,
        trace_stationaryProj hrho0, trace_stationaryProj hrho,
        hrankEq, sub_self]
    have hPeq : P = Q0 := by
      have h := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hRtrace
      exact (sub_eq_zero.mp h).symm
    intro X hX
    rw [hPeq]
    exact hmax X hX

end IsPositiveMap
