/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Projection.ShiftedDensityTruncation
import QICLean.Analysis.FunctionalCalculus.OrthogonalResolution
import QICLean.Algebra.Matrix.MatrixAux
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

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

section

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

end

/-!
Moved from TNLean at commit `2417e0a2e4d8a1dc2db0a14e0c9cae4ca735829e`.
`TNLean/MPS/AreaLaw/Spectral/SpectralTail.lean` and `GroundStateTail.lean`. The statements and
proofs are retained.
-/

section

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real scalar exponentials expressed in the functional calculus of their
Hermitian generator. Auxiliary to AKLV, Lemma 6.6(2). -/
theorem IsHermitian.exp_real_smul_eq_cfc {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • B) = cfc (fun x : ℝ ↦ Real.exp (s * x)) B := by
  rw [Complex.coe_smul, ← CFC.real_exp_eq_normedSpace_exp
    ((IsSelfAdjoint.all s).smul hB.isSelfAdjoint),
    ← cfc_comp_const_mul s Real.exp B Real.continuous_exp.continuousOn
      hB.isSelfAdjoint]

/-- The inverse exponential suppresses the high-energy subspace.
Auxiliary to AKLV, arXiv:1301.1162v1, Lemmas 6.6 and 6.7. -/
theorem IsHermitian.norm_highProjection_mul_exp_neg_le {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (s t : ℝ) (hs : 0 ≤ s) :
    ‖spectralProjectionGE B t * NormedSpace.exp (-((s : ℂ) • B))‖ ≤
      Real.exp (-s * t) := by
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ B) :=
    B.finite_real_spectrum.continuousOn f
  rw [show -((s : ℂ) • B) = ((-s : ℝ) : ℂ) • B by simp,
    hB.exp_real_smul_eq_cfc, spectralProjectionGE,
    ← _root_.cfc_mul _ _ B (hcont _) (hcont _)]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x _
  by_cases htx : t ≤ x
  · simp only [ite_eq_left htx, one_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left htx (neg_nonpos.mpr hs))
  · simp only [ite_eq_right htx, zero_mul, norm_zero]
    exact (Real.exp_pos _).le

/-- The exponential on the strict low-energy subspace is bounded by the
exponential of the threshold. Auxiliary to AKLV, Lemma 6.7. -/
theorem IsHermitian.norm_exp_mul_lowProjection_le {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (s c : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((s : ℂ) • B) * (1 - spectralProjectionGE B c)‖ ≤
      Real.exp (s * c) := by
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ B) :=
    B.finite_real_spectrum.continuousOn f
  rw [hB.exp_real_smul_eq_cfc, spectralProjectionGE,
    ← cfc_one ℝ B hB.isSelfAdjoint, ← cfc_sub _ _ B (hcont _) (hcont _),
    ← _root_.cfc_mul _ _ B (hcont _) (hcont _)]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x _
  by_cases hcx : c ≤ x
  · simp only [ite_eq_left hcx, Pi.one_apply, sub_self, mul_zero, norm_zero]
    exact (Real.exp_pos _).le
  · simp only [ite_eq_right hcx, Pi.one_apply, sub_zero, mul_one, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_not_ge hcx) hs)

/-- Imaginary time separates the high and low spectral subspaces, with no
dimension factor. The conjugated observable is left explicit. This is the
spectral step of AKLV, arXiv:1301.1162v1, Lemma 6.6(2). -/
theorem IsHermitian.norm_spectral_offDiagonal_le_exp_conjugation
    {B : Matrix n n ℂ} (hB : B.IsHermitian) (O : Matrix n n ℂ)
    (t u s : ℝ) (hs : 0 ≤ s) :
    ‖spectralProjectionGE B t * O * (1 - spectralProjectionGE B u)‖ ≤
      Real.exp (-s * (t - u)) *
        ‖NormedSpace.exp ((s : ℂ) • B) * O *
          NormedSpace.exp (-((s : ℂ) • B))‖ := by
  let Q := spectralProjectionGE B t
  let P := 1 - spectralProjectionGE B u
  let E := NormedSpace.exp ((s : ℂ) • B)
  let F := NormedSpace.exp (-((s : ℂ) • B))
  have hQF : ‖Q * F‖ ≤ Real.exp (-s * t) :=
    hB.norm_highProjection_mul_exp_neg_le s t hs
  have hEP : ‖E * P‖ ≤ Real.exp (s * u) :=
    hB.norm_exp_mul_lowProjection_le s u hs
  have hFE : F * E = 1 := by
    simpa only [neg_add_cancel, NormedSpace.exp_zero] using
      (Matrix.exp_add_of_commute (-((s : ℂ) • B)) ((s : ℂ) • B)
        ((Commute.refl ((s : ℂ) • B)).neg_left)).symm
  have hfac : Q * O * P = (Q * F) * (E * O * F) * (E * P) := by
    simp only [mul_assoc, ← mul_assoc F E, hFE, one_mul]
  rw [hfac]
  calc
    _ ≤ (‖Q * F‖ * ‖E * O * F‖) * ‖E * P‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (Real.exp (-s * t) * ‖E * O * F‖) * Real.exp (s * u) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hQF (norm_nonneg _)) hEP
        (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    _ = _ := by rw [mul_right_comm, ← Real.exp_add]; congr 2; ring

/-- Scalar matrices have no block between separated energy windows.
Auxiliary to AKLV, arXiv:1301.1162v1, Lemma 6.6(2). -/
theorem IsHermitian.spectralProjectionGE_mul_one_sub_eq_zero
    {B : Matrix n n ℂ} (hB : B.IsHermitian) {u t : ℝ} (hut : u ≤ t) :
    spectralProjectionGE B t * (1 - spectralProjectionGE B u) = 0 := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ B) :=
    B.finite_real_spectrum.continuousOn f
  rw [spectralProjectionGE, spectralProjectionGE, ← cfc_one ℝ B hB.isSelfAdjoint,
    ← cfc_sub _ _ B (hc _) (hc _), ← _root_.cfc_mul _ _ B (hc _) (hc _)]
  rw [← cfc_zero ℝ B]
  apply cfc_congr
  intro x _
  by_cases htx : t ≤ x
  · simp [htx, hut.trans htx]
  · simp [htx]

/-- Adding the disconnected Hamiltonian does not change the off-diagonal
block between separated energy windows. AKLV, arXiv:1301.1162v1,
Lemma 6.6(2), the equality preceding its exponential estimate. -/
theorem IsHermitian.spectral_offDiagonal_add_eq {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (A : Matrix n n ℂ) {u t : ℝ} (hut : u ≤ t) :
    spectralProjectionGE B t * (B + A) * (1 - spectralProjectionGE B u) =
      spectralProjectionGE B t * A * (1 - spectralProjectionGE B u) := by
  have hc : Commute B (1 - spectralProjectionGE B u) :=
    (Commute.one_right B).sub_right (hB.commute_spectralProjectionGE u)
  have hz : spectralProjectionGE B t * B * (1 - spectralProjectionGE B u) = 0 := by
    rw [mul_assoc, hc.eq, ← mul_assoc,
      hB.spectralProjectionGE_mul_one_sub_eq_zero hut, zero_mul]
  rw [mul_add, add_mul, hz, zero_add]

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The high spectral projection is controlled by the energy norm.
This is the spectral-inverse estimate used in the exponential-moment
proof of AKLV, arXiv:1301.1162v1, Lemma 6.7. -/
theorem IsHermitian.norm_highProjection_apply_le {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (c : ℝ) (hc : 0 < c) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (spectralProjectionGE B c) x‖ ≤
      c⁻¹ * ‖toEuclideanCLM (n := n) (𝕜 := ℂ) B x‖ := by
  let R := cfc (fun z : ℝ ↦ if c ≤ z then z⁻¹ else 0) B
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ B) :=
    B.finite_real_spectrum.continuousOn f
  have hRB : R * B = spectralProjectionGE B c := by
    conv_lhs => rhs; rw [← cfc_id' ℝ B hB.isSelfAdjoint]
    change cfc (fun z : ℝ ↦ if c ≤ z then z⁻¹ else 0) B *
      cfc (fun z : ℝ ↦ z) B = _
    rw [← _root_.cfc_mul _ _ B (hcont _) (hcont _), spectralProjectionGE]
    apply cfc_congr
    intro z _
    by_cases hcz : c ≤ z
    · simp [hcz, ne_of_gt (hc.trans_le hcz)]
    · simp [hcz]
  have hR : ‖R‖ ≤ c⁻¹ := by
    apply norm_cfc_le (inv_nonneg.mpr hc.le)
    intro z _
    by_cases hcz : c ≤ z
    · simp only [ite_eq_left hcz, norm_inv, Real.norm_eq_abs,
        abs_of_pos (hc.trans_le hcz)]
      exact inv_anti₀ hc hcz
    · simp only [ite_eq_right hcz, norm_zero]
      exact inv_nonneg.mpr hc.le
  rw [← hRB, map_mul]
  exact ((toEuclideanCLM (n := n) (𝕜 := ℂ) R).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hR (norm_nonneg _))

/-- A short imaginary-time bound on the perturbation controls every
eigenvector's exponential moment. This is an auxiliary estimate for the
truncation lemma of AKLV, arXiv:1301.1162v1, Lemma 6.7; the chain-local
conjugation estimate is established independently in `SpectralTail`.
No bound on the norm of the complementary Hamiltonian is used. -/
theorem IsHermitian.norm_exp_apply_eigenvector_le {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n)
    (e s c C : ℝ) (hs : 0 ≤ s) (hc : 0 < c)
    (he : toEuclideanCLM (n := n) (𝕜 := ℂ) (B + A) x = (e : ℂ) • x)
    (hC : ‖NormedSpace.exp ((s : ℂ) • B) * A *
      NormedSpace.exp (-((s : ℂ) • B))‖ ≤ C)
    (hsmall : |e| + C ≤ c / 2) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (NormedSpace.exp ((s : ℂ) • B)) x‖ ≤
      2 * Real.exp (s * c) * ‖x‖ := by
  let W := NormedSpace.exp ((s : ℂ) • B)
  let V := NormedSpace.exp (-((s : ℂ) • B))
  let D := W * A * V
  let Q := spectralProjectionGE B c
  let ι := toEuclideanCLM (n := n) (𝕜 := ℂ)
  let y := ι W x
  have hVW : V * W = 1 := by
    simpa only [neg_add_cancel, NormedSpace.exp_zero] using
      (Matrix.exp_add_of_commute (-((s : ℂ) • B)) ((s : ℂ) • B)
        ((Commute.refl ((s : ℂ) • B)).neg_left)).symm
  have hBW : Commute B W := ((Commute.refl B).smul_right (s : ℂ)).exp_right
  have hWQ : Commute W Q := by
    rw [show W = cfc (fun z : ℝ ↦ Real.exp (s * z)) B from hB.exp_real_smul_eq_cfc s]
    exact cfc_commute_cfc _ _ B
  have he' : ι B x = (e : ℂ) • x - ι A x := by
    have h := he
    rw [map_add, _root_.add_apply] at h
    exact eq_sub_of_add_eq h
  have hBy : ι B y = (e : ℂ) • y - ι D y := by
    have hcancel : D * W = W * A := by
      dsimp [D]
      rw [mul_assoc, mul_assoc, hVW, mul_one]
    change ι B (ι W x) = _
    rw [← mul_apply_eq_comp, ← map_mul, hBW.eq, map_mul,
      mul_apply_eq_comp, he', map_sub, map_smul]
    change (e : ℂ) • y - ι W (ι A x) = (e : ℂ) • y - ι D (ι W x)
    conv_rhs => rhs; rw [← mul_apply_eq_comp, ← map_mul, hcancel, map_mul,
      mul_apply_eq_comp]
  have henergy : ‖ι B y‖ ≤ (c / 2) * ‖y‖ := by
    rw [hBy]
    calc
      _ ≤ ‖(e : ℂ) • y‖ + ‖ι D y‖ := norm_sub_le _ _
      _ ≤ |e| * ‖y‖ + C * ‖y‖ := by
        apply add_le_add
        · simp [norm_smul, Real.norm_eq_abs]
        · exact ((ι D).le_opNorm y).trans
            (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
      _ ≤ (c / 2) * ‖y‖ := by nlinarith [norm_nonneg y]
  have hhigh : ‖ι Q y‖ ≤ (1 / 2 : ℝ) * ‖y‖ := by
    calc
      _ ≤ c⁻¹ * ‖ι B y‖ := hB.norm_highProjection_apply_le c hc y
      _ ≤ c⁻¹ * ((c / 2) * ‖y‖) :=
        mul_le_mul_of_nonneg_left henergy (inv_nonneg.mpr hc.le)
      _ = _ := by field_simp
  have hlow : ‖ι (1 - Q) y‖ ≤ Real.exp (s * c) * ‖x‖ := by
    have hcomm : (1 - Q) * W = W * (1 - Q) :=
      ((Commute.one_left W).sub_left hWQ.symm).eq
    change ‖ι (1 - Q) (ι W x)‖ ≤ _
    rw [← mul_apply_eq_comp, ← map_mul, hcomm]
    exact ((ι (W * (1 - Q))).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hB.norm_exp_mul_lowProjection_le s c hs)
        (norm_nonneg _))
  have hsplit : y = ι (1 - Q) y + ι Q y := by
    rw [← _root_.add_apply, ← map_add, sub_add_cancel, map_one,
      one_apply_eq_self]
  have htriangle : ‖y‖ ≤ ‖ι (1 - Q) y‖ + ‖ι Q y‖ := by
    conv_lhs => rw [hsplit]
    exact norm_add_le _ _
  change ‖y‖ ≤ _
  linarith

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exponential energy tails follow from the actual imaginary-time
perturbation estimate. Auxiliary to AKLV, arXiv:1301.1162v1, Lemma 6.7.
The conclusion applies to every eigenvector, without normalization. -/
theorem IsHermitian.norm_highProjection_eigenvector_le_exp {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n)
    (e s c C t : ℝ) (hs : 0 ≤ s) (hc : 0 < c)
    (he : toEuclideanCLM (n := n) (𝕜 := ℂ) (B + A) x = (e : ℂ) • x)
    (hC : ‖NormedSpace.exp ((s : ℂ) • B) * A *
      NormedSpace.exp (-((s : ℂ) • B))‖ ≤ C)
    (hsmall : |e| + C ≤ c / 2) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (spectralProjectionGE B t) x‖ ≤
      2 * Real.exp (-s * (t - c)) * ‖x‖ := by
  let W := NormedSpace.exp ((s : ℂ) • B)
  let V := NormedSpace.exp (-((s : ℂ) • B))
  let ι := toEuclideanCLM (n := n) (𝕜 := ℂ)
  have hVW : V * W = 1 := by
    simpa only [neg_add_cancel, NormedSpace.exp_zero] using
      (Matrix.exp_add_of_commute (-((s : ℂ) • B)) ((s : ℂ) • B)
        ((Commute.refl ((s : ℂ) • B)).neg_left)).symm
  have hfactor : ι (spectralProjectionGE B t) x =
      ι (spectralProjectionGE B t * V) (ι W x) := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_assoc, hVW, mul_one]
  rw [hfactor]
  calc
    _ ≤ ‖ι (spectralProjectionGE B t * V)‖ * ‖ι W x‖ :=
      (ι (spectralProjectionGE B t * V)).le_opNorm _
    _ ≤ Real.exp (-s * t) * (2 * Real.exp (s * c) * ‖x‖) :=
      mul_le_mul (hB.norm_highProjection_mul_exp_neg_le s t hs)
        (hB.norm_exp_apply_eigenvector_le A x e s c C hs hc he hC hsmall)
        (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      rw [show -s * (t - c) = -s * t + s * c by ring, Real.exp_add]
      ring

end Matrix

end
