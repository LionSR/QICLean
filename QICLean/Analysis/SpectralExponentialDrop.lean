/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ShiftedDensityTruncation
import QICLean.Analysis.OrthogonalResolution
import QICLean.Algebra.MatrixAux

/-!
# Dropping a nonnegative spectral term from a commuting exponential

For commuting Hermitian matrices G and H and a nonnegative real a, let
J be the closed nonnegative spectral projection of G. Then
`J * exp (a • (H - G)) * J ≤ exp (a • H)`. A positive semidefinite trace
weight supported on J consequently has a smaller exponential moment for
H - G than for H. These inequalities use nonnegativity only on the
retained spectral subspace; no full-space positivity of G is required.

These are auxiliary finite-dimensional facts for the rough component
estimate in OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 553–555. The actual physical
label operator, its compatible spectral projection, the component's support
and both merge moments are separate mathematical inputs to that estimate.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.Operator
namespace Matrix
variable {n I : Type*} [Fintype n] [DecidableEq n] [Fintype I] [DecidableEq I]

private theorem exp_smul_hom_real {P : I → Matrix n n ℂ}
    (hP : IsOrthogonalResolution P) (a : ℝ) (x : I → ℝ) :
    NormedSpace.exp ((a : ℂ) • hP.hom (fun i => (x i : ℂ))) =
      hP.hom (fun i => (Real.exp (a * x i) : ℂ)) := by
  rw [← map_smul, hP.exp_hom]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_exp]

/-- Spectral compression drops the nonnegative part of a commuting exponent.
Auxiliary to OpenAI area-law Section 7, lines 553–555. -/
theorem spectralProjectionGE_exp_smul_sub_le {G H : Matrix n n ℂ}
    (hG : G.IsHermitian) (hH : H.IsHermitian) (hGH : Commute G H)
    {a : ℝ} (ha : 0 ≤ a) :
    spectralProjectionGE G 0 * NormedSpace.exp ((a : ℂ) • (H - G)) *
      spectralProjectionGE G 0 ≤ NormedSpace.exp ((a : ℂ) • H) := by
  classical
  have hc (g : hG.eigenvalueSet) (h : hH.eigenvalueSet) :
      Commute (hG.spectralProj g) (hH.spectralProj h) :=
    (hH.commute_spectralProj (hG.commute_spectralProj hGH g).symm h).symm
  let R := hG.isOrthogonalResolution_spectralProj.prod
    hH.isOrthogonalResolution_spectralProj hc
  have hE (p : hG.eigenvalueSet × hH.eigenvalueSet) :
      (hG.spectralProj p.1 * hH.spectralProj p.2).IsHermitian :=
    ((hG.isHermitian_spectralProj p.1).commute_iff
      (hH.isHermitian_spectralProj p.2)).mp (hc p.1 p.2)
  have hmG : R.hom (fun p => ((p.1 : ℝ) : ℂ)) = G :=
    (hG.isOrthogonalResolution_spectralProj.prod_hom_fst
      hH.isOrthogonalResolution_spectralProj R _).trans hG.eq_hom.symm
  have hmH : R.hom (fun p => ((p.2 : ℝ) : ℂ)) = H :=
    (hG.isOrthogonalResolution_spectralProj.prod_hom_snd
      hH.isOrthogonalResolution_spectralProj R _).trans hH.eq_hom.symm
  have hmJ : R.hom (fun p => ((if 0 ≤ (p.1 : ℝ) then 1 else 0 : ℝ) : ℂ)) =
      spectralProjectionGE G 0 :=
    (hG.isOrthogonalResolution_spectralProj.prod_hom_fst
      hH.isOrthogonalResolution_spectralProj R _).trans
        (hG.spectralProjectionGE_eq_cfc 0 |>.trans
          (hG.cfc_eq_hom (fun t => if 0 ≤ t then 1 else 0))).symm
  have hmHG : R.hom (fun p => (((p.2 : ℝ) - (p.1 : ℝ) : ℝ) : ℂ)) = H - G := by
    calc
      _ = R.hom (fun p => ((p.2 : ℝ) : ℂ)) -
          R.hom (fun p => ((p.1 : ℝ) : ℂ)) := by
        rw [← map_sub]
        congr 1
        funext p
        simp only [Pi.sub_apply, Complex.ofReal_sub]
      _ = _ := by rw [hmG, hmH]
  have hExpHG : NormedSpace.exp ((a : ℂ) • (H - G)) =
      R.hom (fun p => (Real.exp (a * ((p.2 : ℝ) - (p.1 : ℝ))) : ℂ)) :=
    (congrArg (fun M => NormedSpace.exp ((a : ℂ) • M)) hmHG).symm.trans
      (exp_smul_hom_real R a _)
  have hExpH : NormedSpace.exp ((a : ℂ) • H) =
      R.hom (fun p => (Real.exp (a * (p.2 : ℝ)) : ℂ)) :=
    (congrArg (fun M => NormedSpace.exp ((a : ℂ) • M)) hmH).symm.trans
      (exp_smul_hom_real R a _)
  rw [← hmJ, hExpHG, hExpH, ← map_mul, ← map_mul, Matrix.le_iff, ← map_sub]
  have hfun : ((fun p : hG.eigenvalueSet × hH.eigenvalueSet =>
        (Real.exp (a * (p.2 : ℝ)) : ℂ)) -
      (fun p => ((if 0 ≤ (p.1 : ℝ) then 1 else 0 : ℝ) : ℂ)) *
        (fun p => (Real.exp (a * ((p.2 : ℝ) - (p.1 : ℝ))) : ℂ)) *
          (fun p => ((if 0 ≤ (p.1 : ℝ) then 1 else 0 : ℝ) : ℂ))) =
      fun p => ((Real.exp (a * (p.2 : ℝ)) -
        if 0 ≤ (p.1 : ℝ) then Real.exp (a * ((p.2 : ℝ) - (p.1 : ℝ))) else 0 : ℝ) : ℂ) := by
    funext p
    by_cases hg : 0 ≤ (p.1 : ℝ) <;> simp [hg]
  rw [hfun]
  refine R.posSemidef_hom hE fun p => ?_
  split_ifs with hg
  · exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ha hg]))
  · simpa only [sub_zero] using (Real.exp_pos _).le

/-- A supported positive trace weight may drop the nonnegative spectral term.
Auxiliary to OpenAI area-law Section 7, lines 553–555. -/
theorem PosSemidef.re_trace_mul_exp_smul_sub_le_of_spectralProjectionGE_mul
    {ρ G H : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hG : G.IsHermitian) (hH : H.IsHermitian) (hGH : Commute G H)
    {a : ℝ} (ha : 0 ≤ a) (hsupport : spectralProjectionGE G 0 * ρ = ρ) :
    (ρ * NormedSpace.exp ((a : ℂ) • (H - G))).trace.re ≤
      (ρ * NormedSpace.exp ((a : ℂ) • H)).trace.re := by
  have hJ : (spectralProjectionGE G 0)ᴴ = spectralProjectionGE G 0 :=
    (hG.isStarProjection_spectralProjectionGE 0).isSelfAdjoint.star_eq
  have hρJ : ρ * spectralProjectionGE G 0 = ρ := by
    simpa only [conjTranspose_mul, hρ.isHermitian.eq, hJ] using
      congrArg Matrix.conjTranspose hsupport
  have htrace : (ρ * (spectralProjectionGE G 0 *
      NormedSpace.exp ((a : ℂ) • (H - G)) * spectralProjectionGE G 0)).trace =
      (ρ * NormedSpace.exp ((a : ℂ) • (H - G))).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hρJ, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, hsupport]
  have hpos := spectralProjectionGE_exp_smul_sub_le hG hH hGH ha
  rw [Matrix.le_iff] at hpos
  have ht := hρ.trace_mul_nonneg hpos
  have ht' := (Complex.nonneg_iff.mp ht).1
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, htrace] at ht'
  exact sub_nonneg.mp ht'
end Matrix
