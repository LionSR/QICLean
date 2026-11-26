/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import QICLean.Analysis.FunctionalCalculus.MatrixPolar
import QICLean.Analysis.FunctionalCalculus.MatrixPolarUniqueness
import QICLean.Analysis.Projection.PosSemidefSupport

/-!
# Continuous separated spectral corners

A fixed spectral cutoff separated from the spectra of a Hermitian matrix
family selects a continuous orthogonal projection. Operators commuting with
the original matrices preserve these projection ranges.

This is an auxiliary finite-dimensional construction in the context of
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Appendix C, lines 2653–2717.
Spectral separation and density continuity are supplied explicitly; their
derivation from a physical gap and canonical MPS data remains open, as
recorded in `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.

Moved from TNLean, `TNLean/MPS/Symmetry/ContinuousFamily/ContinuousSpectralCorner.lean`,
`TNLean/MPS/Symmetry/ContinuousFamily/ContinuousProjectionFrame.lean`,
`TNLean/MPS/Symmetry/ContinuousFamily/LocalSpectralSupport.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

section

open scoped Matrix Matrix.Norms.L2Operator Topology

namespace Matrix

/-- A continuous ramp which selects the high spectral component outside
the interval between two cutoffs. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
noncomputable def spectralCornerRamp (a b x : ℝ) : ℝ := min 1 (max 0 ((x - a) / (b - a)))

/-- Continuity of the cutoff ramp. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
theorem continuous_spectralCornerRamp (a b : ℝ) : Continuous (spectralCornerRamp a b) :=
  continuous_const.min (continuous_const.max ((continuous_id.sub continuous_const).div_const _))

/-- The cutoff ramp vanishes below its lower cutoff. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem spectralCornerRamp_eq_zero_of_le {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    spectralCornerRamp a b x = 0 := by
  have hratio : (x - a) / (b - a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_nonneg.mpr hab.le)
  simp only [spectralCornerRamp, max_eq_left hratio, min_eq_right zero_le_one]

/-- The cutoff ramp equals one above its upper cutoff. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem spectralCornerRamp_eq_one_of_le {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    spectralCornerRamp a b x = 1 := by
  have hratio : 1 ≤ (x - a) / (b - a) :=
    (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  simp only [spectralCornerRamp, max_eq_right (zero_le_one.trans hratio), min_eq_left hratio]

/-- The spectral corner selected by a separated pair of cutoffs.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
noncomputable def spectralCorner {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ := cfc (spectralCornerRamp a b) A

/-- Real functional calculus makes the cutoff corner Hermitian. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem isHermitian_spectralCorner {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (A : Matrix n n ℂ) :
    (spectralCorner a b A).IsHermitian :=
  IsSelfAdjoint.cfc (R := ℝ) (f := spectralCornerRamp a b)

/-- Spectral separation makes the cutoff corner idempotent. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem spectralCorner_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {a b : ℝ} (hab : a < b) (A : Matrix n n ℂ)
    (hgap : ∀ x ∈ spectrum ℝ A, x ≤ a ∨ b ≤ x) :
    spectralCorner a b A * spectralCorner a b A = spectralCorner a b A := by
  rw [spectralCorner, ← cfc_mul _ _ A (continuous_spectralCornerRamp a b).continuousOn
    (continuous_spectralCornerRamp a b).continuousOn]
  apply cfc_congr
  intro x hx
  change spectralCornerRamp a b x * spectralCornerRamp a b x = spectralCornerRamp a b x
  rcases hgap x hx with hlow | hhigh
  · rw [spectralCornerRamp_eq_zero_of_le hab hlow, zero_mul]
  · rw [spectralCornerRamp_eq_one_of_le hab hhigh, one_mul]

/-- A continuous Hermitian family has a continuous cutoff corner.
Spectral separation is needed for idempotence, rather than continuity of
the ramp functional calculus. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
theorem continuous_spectralCorner_family
    {T n : Type*} [TopologicalSpace T] [Fintype n] [DecidableEq n]
    (a b : ℝ) (A : T → Matrix n n ℂ) (hA : Continuous A)
    (hHerm : ∀ t, (A t).IsHermitian) : Continuous fun t => spectralCorner a b (A t) :=
  Continuous.cfc_of_mem_nhdsSet (spectralCornerRamp a b) (s := Set.univ)
    (by simp) hA hHerm (continuous_spectralCornerRamp a b).continuousOn

/-- Under spectral separation the ramp calculus equals the high-spectrum
indicator calculus. Thus the continuous corner is precisely the projection
onto spectral values at or above the upper cutoff. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem spectralCorner_eq_cfc_highIndicator
    {n : Type*} [Fintype n] [DecidableEq n]
    {a b : ℝ} (hab : a < b) (A : Matrix n n ℂ)
    (hgap : ∀ x ∈ spectrum ℝ A, x ≤ a ∨ b ≤ x) :
    spectralCorner a b A = cfc (fun x : ℝ => if b ≤ x then 1 else 0) A := by
  rw [spectralCorner]
  apply cfc_congr
  intro x hx
  change spectralCornerRamp a b x = if b ≤ x then 1 else 0
  rcases hgap x hx with hlow | hhigh
  · rw [spectralCornerRamp_eq_zero_of_le hab hlow, ite_eq_right (by linarith)]
  · rw [spectralCornerRamp_eq_one_of_le hab hhigh, ite_eq_left hhigh]

/-- An operator commuting with the original density also commutes with
the separated spectral corner. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
theorem commute_spectralCorner_of_commute
    {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (U A : Matrix n n ℂ) (hComm : Commute U A) :
    Commute U (spectralCorner a b A) :=
  (hComm.symm.cfc_real (spectralCornerRamp a b)).symm

/-- A unitary symmetry commuting with a density preserves its cutoff
corner under conjugation. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
theorem unitary_conj_spectralCorner_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (U A : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ)
    (hComm : Commute U A) : U * spectralCorner a b A * Uᴴ = spectralCorner a b A := by
  have hUU : U * Uᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hU
  rw [(commute_spectralCorner_of_commute a b U A hComm).eq, Matrix.mul_assoc,
    hUU, Matrix.mul_one]

/-- The rank of a continuous orthogonal projection family is locally
constant, since rank equals its continuous real trace. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem isLocallyConstant_rank_of_continuous_projection_family
    {T n : Type*} [TopologicalSpace T] [Fintype n]
    (P : T → Matrix n n ℂ) (hP : Continuous P)
    (hHerm : ∀ t, (P t).IsHermitian) (hid : ∀ t, P t * P t = P t) :
    IsLocallyConstant fun t => (P t).rank := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro t₀
  have hc := Complex.continuous_re.comp hP.matrix_trace
  have hnear : ∀ᶠ t in 𝓝 t₀, |(P t).trace.re - (P t₀).trace.re| < 1 :=
    ((hc.continuousAt.sub continuousAt_const).abs).eventually
      (Iio_mem_nhds (by simp))
  filter_upwards [hnear] with t ht
  rw [← (hHerm t).rank_eq_trace_re_of_idem (hid t),
    ← (hHerm t₀).rank_eq_trace_re_of_idem (hid t₀)] at ht
  have hlt : (P t).rank < (P t₀).rank + 1 := by
    exact_mod_cast (show ((P t).rank : ℝ) < (P t₀).rank + 1 by
      linarith [(abs_lt.mp ht).2])
  have hgt : (P t₀).rank < (P t).rank + 1 := by
    exact_mod_cast (show ((P t₀).rank : ℝ) < (P t).rank + 1 by
      linarith [(abs_lt.mp ht).1])
  omega

/-- A separated spectral corner has locally constant rank, even when the
rank of the underlying Hermitian density changes. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem isLocallyConstant_rank_spectralCorner_family
    {T n : Type*} [TopologicalSpace T] [Fintype n] [DecidableEq n]
    {a b : ℝ} (hab : a < b) (A : T → Matrix n n ℂ) (hA : Continuous A)
    (hHerm : ∀ t, (A t).IsHermitian)
    (hgap : ∀ t, ∀ x ∈ spectrum ℝ (A t), x ≤ a ∨ b ≤ x) :
    IsLocallyConstant fun t => (spectralCorner a b (A t)).rank :=
  isLocallyConstant_rank_of_continuous_projection_family
    (fun t => spectralCorner a b (A t)) (continuous_spectralCorner_family a b A hA hHerm)
    (fun t => isHermitian_spectralCorner a b (A t))
    (fun t => spectralCorner_mul_self hab _ (hgap t))

end Matrix

end

section

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology

namespace Matrix

/-- The positive polar factor of a continuous rectangular matrix family is
continuous. Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem continuous_polarPos_family
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq n]
    (M : T → Matrix m n ℂ) (hM : Continuous M) :
    Continuous fun t => polarPos (M t) := by
  classical
  have hGram : Continuous fun t => (M t)ᴴ * M t := hM.matrix_conjTranspose.matrix_mul hM
  have hsqrt : Continuous fun t => cfc Real.sqrt ((M t)ᴴ * M t) :=
    Continuous.cfc_of_mem_nhdsSet Real.sqrt (s := Set.univ) (by simp) hGram
      (fun t => isHermitian_conjTranspose_mul_self (M t)) Real.continuous_sqrt.continuousOn
  convert hsqrt using 1
  funext t
  rw [polarPos, CFC.sqrt_eq_real_sqrt _ (posSemidef_conjTranspose_mul_self (M t)).nonneg,
    cfcₙ_eq_cfc]

/-- On an injective rectangular matrix the polar isometry is obtained by
inverting its positive factor. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
theorem polarIso_eq_mul_inv_polarPos_of_injective
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) (hM : Function.Injective M.mulVec) :
    polarIso M = M * (polarPos M)⁻¹ := by
  classical
  have hunit := (posDef_polarPos_of_injective M hM).isUnit
  calc
    polarIso M = polarIso M * (polarPos M * (polarPos M)⁻¹) := by
      rw [mul_nonsing_inv (A := polarPos M)
        ((polarPos M).isUnit_iff_isUnit_det.mp hunit), Matrix.mul_one]
    _ = M * (polarPos M)⁻¹ := by rw [← Matrix.mul_assoc, polarIso_mul_polarPos]

/-- Polar isometries vary continuously in a continuous family of injective
rectangular matrices. Source context: arXiv:1010.3732, Appendix C,
lines 2653–2717. -/
theorem continuous_polarIso_family_of_injective
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq n]
    (M : T → Matrix m n ℂ) (hM : Continuous M)
    (hInj : ∀ t, Function.Injective (M t).mulVec) :
    Continuous fun t => polarIso (M t) := by
  classical
  have hPos := continuous_polarPos_family M hM
  have hInv : Continuous fun t => Ring.inverse (polarPos (M t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hAt : ContinuousAt Ring.inverse (polarPos (M t)) := by
      obtain ⟨u, hu⟩ := (posDef_polarPos_of_injective (M t) (hInj t)).isUnit
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    exact hAt.comp' (f := fun t => polarPos (M t)) hPos.continuousAt
  have h := hM.matrix_mul hInv
  simpa only [polarIso_eq_mul_inv_polarPos_of_injective _ (hInj _),
    nonsing_inv_eq_ringInverse] using h

/-- The projected base frame has invertible Gram matrix near the base
parameter. Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem exists_open_projected_frame_injective
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq n]
    (P : T → Matrix m m ℂ) (hP : Continuous P) (t₀ : T)
    (J₀ : Matrix m n ℂ) (hJ₀ : J₀.IsIsometry) (hbase : P t₀ = J₀ * J₀ᴴ) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ∀ t ∈ S, Function.Injective (P t * J₀).mulVec := by
  classical
  let M := fun t => P t * J₀
  have hM : Continuous M := hP.matrix_mul continuous_const
  have hGram : Continuous fun t => (M t)ᴴ * M t := hM.matrix_conjTranspose.matrix_mul hM
  have hJ : J₀ᴴ * J₀ = 1 := hJ₀
  have hMbase : M t₀ = J₀ := by
    simp only [M, hbase, Matrix.mul_assoc, hJ, Matrix.mul_one]
  let S := {t | IsUnit ((M t)ᴴ * M t)}
  refine ⟨S, Units.isOpen.preimage hGram, ?_, ?_⟩
  · change IsUnit ((M t₀)ᴴ * M t₀)
    rw [hMbase, hJ]
    exact isUnit_one
  · intro t ht a b hab
    apply (mulVec_injective_iff_isUnit.mpr ht)
    simpa only [mulVec_mulVec] using congrArg ((M t)ᴴ *ᵥ ·) hab

/-- The polar frame selected by projecting a base frame is continuous and
isometric locally, and lies in the prescribed projection range. Source
context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem exists_local_continuous_isometric_projected_frame
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq n]
    (P : T → Matrix m m ℂ) (hP : Continuous P) (hid : ∀ t, P t * P t = P t)
    (t₀ : T) (J₀ : Matrix m n ℂ) (hJ₀ : J₀.IsIsometry) (hbase : P t₀ = J₀ * J₀ᴴ) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => polarIso (P t * J₀)) S ∧
      ∀ t ∈ S, (polarIso (P t * J₀)).IsIsometry ∧
        P t * polarIso (P t * J₀) = polarIso (P t * J₀) := by
  classical
  obtain ⟨S, hS, ht₀, hInj⟩ := exists_open_projected_frame_injective P hP t₀ J₀ hJ₀ hbase
  refine ⟨S, hS, ht₀, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_polarIso_family_of_injective (fun t : S => P t * J₀)
      ((hP.comp continuous_subtype_val).matrix_mul continuous_const)
      (fun t => hInj t t.property)
  · intro t ht
    refine ⟨isIsometry_polarIso_of_injective _ (hInj t ht), ?_⟩
    obtain ⟨R, hR⟩ := exists_polarIso_eq_mul (P t * J₀)
    rw [hR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hid t]

/-- An isometric frame contained in a projection range exhausts that range
when their ranks agree. Source context: arXiv:1010.3732, Appendix C,
lines 2653–2717. -/
theorem range_eq_of_isometric_frame_of_rank_eq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (P : Matrix m m ℂ) (J : Matrix m n ℂ) (hJ : J.IsIsometry)
    (hPJ : P * J = J) (hrank : P.rank = Fintype.card n) :
    LinearMap.range J.mulVecLin = LinearMap.range P.mulVecLin := by
  classical
  have hle : LinearMap.range J.mulVecLin ≤ LinearMap.range P.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨J *ᵥ v, ?_⟩
    change P *ᵥ (J *ᵥ v) = J *ᵥ v
    rw [mulVec_mulVec, hPJ]
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hJrank := J.rank_eq_finrank_range_toLin (Pi.basisFun ℂ m) (Pi.basisFun ℂ n)
  have hPrank := P.rank_eq_finrank_range_toLin (Pi.basisFun ℂ m) (Pi.basisFun ℂ m)
  rw [toLin_eq_toLin', toLin'_apply'] at hJrank hPrank
  rw [← hJrank, ← hPrank, hJ.rank_eq_card J, hrank]

/-- A Hermitian projection is recovered from any full isometric frame in
its range. Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem frame_mul_conjTranspose_eq_of_rank_eq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (P : Matrix m m ℂ) (hP : P.IsHermitian) (J : Matrix m n ℂ) (hJ : J.IsIsometry)
    (hPJ : P * J = J) (hrank : P.rank = Fintype.card n) : J * Jᴴ = P := by
  classical
  obtain ⟨R, hR⟩ := exists_mul_eq_of_range_le
    (range_eq_of_isometric_frame_of_rank_eq P J hJ hPJ hrank).ge
  have hAdj : Jᴴ * P = Jᴴ := by
    simpa only [conjTranspose_mul, hP.eq] using congrArg conjTranspose hPJ
  have hJR : J * Jᴴ * P = P := by
    rw [← hR, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ, hJ, Matrix.one_mul]
  simpa only [Matrix.mul_assoc, hAdj] using hJR

/-- A continuous fixed-rank orthogonal projection family admits continuous
isometric frames locally near a prescribed base frame. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem exists_local_continuous_projection_frame
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq n]
    (P : T → Matrix m m ℂ) (hP : Continuous P)
    (hHerm : ∀ t, (P t).IsHermitian) (hid : ∀ t, P t * P t = P t)
    (hrank : ∀ t, (P t).rank = Fintype.card n)
    (t₀ : T) (J₀ : Matrix m n ℂ) (hJ₀ : J₀.IsIsometry) (hbase : P t₀ = J₀ * J₀ᴴ) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => polarIso (P t * J₀)) S ∧
      ∀ t ∈ S, (polarIso (P t * J₀)).IsIsometry ∧
        polarIso (P t * J₀) * (polarIso (P t * J₀))ᴴ = P t := by
  classical
  obtain ⟨S, hS, ht₀, hcont, hFrame⟩ :=
    exists_local_continuous_isometric_projected_frame P hP hid t₀ J₀ hJ₀ hbase
  refine ⟨S, hS, ht₀, hcont, ?_⟩
  intro t ht
  obtain ⟨hIso, hContained⟩ := hFrame t ht
  exact ⟨hIso, frame_mul_conjTranspose_eq_of_rank_eq (P t) (hHerm t)
    (polarIso (P t * J₀)) hIso hContained (hrank t)⟩

end Matrix

end

section

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

set_option linter.mathlibStandardSet true

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder Topology

open Filter Set

namespace Matrix

/-- A strict gap in the real spectrum persists locally with weak endpoints,
by upper hemicontinuity of the finite-dimensional spectrum. -/
theorem eventually_spectral_separation_of_continuousAt
    {T n : Type*} [TopologicalSpace T] [Fintype n] [DecidableEq n]
    (A : T → Matrix n n ℂ) {t₀ : T} (hA : ContinuousAt A t₀)
    {a b : ℝ} (hgap : ∀ x ∈ spectrum ℝ (A t₀), x < a ∨ b < x) :
    ∀ᶠ t in 𝓝 t₀, ∀ x ∈ spectrum ℝ (A t), x ≤ a ∨ b ≤ x := by
  have hnear := ((upperHemicontinuous_spectrum ℝ (Matrix n n ℂ)).upperHemicontinuousAt
    (A t₀)).comp hA |>.forall_isOpen (Iio a ∪ Ioi b)
      (isOpen_Iio.union isOpen_Ioi) hgap
  filter_upwards [hnear] with t ht x hx
  exact (ht hx).imp le_of_lt le_of_lt

/-- The finite real spectrum admits positive cutoffs below every positive
spectral value. -/
theorem exists_positive_spectral_cutoffs {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ x ∈ spectrum ℝ B, x ≤ 0 ∨ b < x := by
  have hclosed : IsClosed (spectrum ℝ B \ {0}) :=
    B.finite_real_spectrum.sdiff.isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hclosed.compl_mem_nhds (x := (0 : ℝ)) (by simp))
  refine ⟨ε / 3, 2 * ε / 3, by positivity, by linarith, ?_⟩
  intro x hx
  by_contra h
  have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
    grind [Metric.mem_ball, Real.dist_eq, abs_lt]
  exact hball hxball ⟨hx, by grind⟩

/-- A cutoff below all positive spectral values recovers the support
projection of a positive semidefinite matrix. -/
theorem spectralCorner_eq_supportProj_of_nonzero_spectrum_separation
    {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℂ} (hB : B.PosSemidef) {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hgap : ∀ x ∈ spectrum ℝ B, x ≤ 0 ∨ b ≤ x) :
    spectralCorner a b B = hB.supportProj := by
  rw [spectralCorner, hB.isHermitian.cfc_eq, IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, PosSemidef.supportProj, IsHermitian.supportProj]
  congr 2
  apply congrArg diagonal
  funext i
  have he := hgap _ (hB.isHermitian.eigenvalues_mem_spectrum_real i)
  have he0 := hB.eigenvalues_nonneg i
  rcases he with hlow | hhigh
  · simp only [Function.comp_apply, le_antisymm hlow he0,
      spectralCornerRamp_eq_zero_of_le hab ha.le, RCLike.ofReal_zero,
      ne_eq, not_true_eq_false, ite_false]
  · have hne : hB.isHermitian.eigenvalues i ≠ 0 :=
      ne_of_gt ((ha.trans hab).trans_le hhigh)
    simp only [Function.comp_apply, spectralCornerRamp_eq_one_of_le hab hhigh,
      RCLike.ofReal_one]
    change (1 : ℂ) = if hB.isHermitian.eigenvalues i ≠ 0 then 1 else 0
    exact (ite_eq_left hne).symm

/-- A continuous Hermitian family admits a spectral projection of constant
rank locally, whose base value is the support of the base matrix.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem exists_open_constantRank_spectralCorner
    {T n : Type*} [TopologicalSpace T] [Fintype n] [DecidableEq n]
    (A : T → Matrix n n ℂ) (hA : Continuous A)
    (hHerm : ∀ t, (A t).IsHermitian) (t₀ : T) (hbase : (A t₀).PosSemidef) :
    ∃ a b : ℝ, ∃ S : Set T, 0 < a ∧ a < b ∧ IsOpen S ∧ t₀ ∈ S ∧
      spectralCorner a b (A t₀) = hbase.supportProj ∧
      ∀ t ∈ S, spectralCorner a b (A t) * spectralCorner a b (A t) =
        spectralCorner a b (A t) ∧
        (spectralCorner a b (A t)).rank = (spectralCorner a b (A t₀)).rank := by
  obtain ⟨a, b, ha, hab, hgap₀⟩ := exists_positive_spectral_cutoffs (A t₀)
  have hnear := eventually_spectral_separation_of_continuousAt A hA.continuousAt
    (fun x hx => (hgap₀ x hx).imp (fun h => h.trans_lt ha) id)
  obtain ⟨S, hSgap, hS, ht₀⟩ := mem_nhds_iff.mp hnear
  have hlocal := isLocallyConstant_rank_spectralCorner_family hab
    (fun t : S => A t) (hA.comp continuous_subtype_val)
    (fun t => hHerm t) (fun t => hSgap t.property)
  let R : Set S := {t | (spectralCorner a b (A t)).rank =
    (spectralCorner a b (A t₀)).rank}
  refine ⟨a, b, Subtype.val '' R, ha, hab,
    hS.isOpenMap_subtype_val R (hlocal.isOpen_fiber _),
    ⟨⟨t₀, ht₀⟩, rfl, rfl⟩,
    spectralCorner_eq_supportProj_of_nonzero_spectrum_separation hbase ha hab
      (fun x hx => (hgap₀ x hx).imp id le_of_lt), ?_⟩
  rintro t ⟨s, hs, rfl⟩
  exact ⟨spectralCorner_mul_self hab _ (hSgap s.property), hs⟩

/-- A prescribed isometric frame of the base support extends continuously
to frames of a separated spectral corner on an open neighborhood. The polar
construction preserves the base frame exactly.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem exists_local_continuous_spectral_frame
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : T → Matrix m m ℂ) (hA : Continuous A)
    (hHerm : ∀ t, (A t).IsHermitian) (t₀ : T) (hbase : (A t₀).PosSemidef)
    (J₀ : Matrix m n ℂ) (hJ₀ : J₀.IsIsometry)
    (hsupport : hbase.supportProj = J₀ * J₀ᴴ) :
    ∃ a b : ℝ, ∃ S : Set T, 0 < a ∧ a < b ∧ IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => polarIso (spectralCorner a b (A t) * J₀)) S ∧
      polarIso (spectralCorner a b (A t₀) * J₀) = J₀ ∧
      ∀ t ∈ S, (polarIso (spectralCorner a b (A t) * J₀)).IsIsometry ∧
        polarIso (spectralCorner a b (A t) * J₀) *
          (polarIso (spectralCorner a b (A t) * J₀))ᴴ = spectralCorner a b (A t) := by
  obtain ⟨a, b, S, ha, hab, hS, ht₀, hP₀, hP⟩ :=
    exists_open_constantRank_spectralCorner A hA hHerm t₀ hbase
  have hrank₀ : (spectralCorner a b (A t₀)).rank = Fintype.card n := by
    simpa only [hP₀, hsupport, rank_self_mul_conjTranspose] using hJ₀.rank_eq_card J₀
  obtain ⟨R, hR, ht₀R, hcont, hFrame⟩ :=
    exists_local_continuous_projection_frame
      (fun t : S => spectralCorner a b (A t))
      ((continuous_spectralCorner_family a b A hA hHerm).comp continuous_subtype_val)
      (fun t => isHermitian_spectralCorner a b (A t))
      (fun t => (hP t t.property).1)
      (fun t => (hP t t.property).2.trans hrank₀)
      ⟨t₀, ht₀⟩ J₀ hJ₀ (hP₀.trans hsupport)
  refine ⟨a, b, Subtype.val '' R, ha, hab,
    hS.isOpenMap_subtype_val R hR, ⟨⟨t₀, ht₀⟩, ht₀R, rfl⟩, ?_, ?_, ?_⟩
  · exact Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr hcont
  · refine polarIso_eq_of_eq_mul (Q := (1 : Matrix n n ℂ)) (E := 1) ?_
      PosSemidef.one hJ₀ isHermitian_one (one_mul _) rfl
    simp only [hP₀, hsupport, Matrix.mul_assoc,
      show J₀ᴴ * J₀ = 1 from hJ₀, Matrix.mul_one]
  · rintro t ⟨s, hs, rfl⟩
    exact hFrame s hs

/-- A positive spectral cutoff is contained in the support of a positive
semidefinite matrix. Spectral separation is not required for this inclusion.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem supportProj_mul_spectralCorner
    {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    hσ.supportProj * spectralCorner a b σ = spectralCorner a b σ := by
  rw [spectralCorner, hσ.isHermitian.cfc_eq, IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, PosSemidef.supportProj, IsHermitian.supportProj]
  have hU : star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
      (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    mem_unitaryGroup_iff'.mp hσ.isHermitian.eigenvectorUnitary.property
  simp only [Matrix.mul_assoc,
    ← Matrix.mul_assoc (star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ))
      (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ), hU, Matrix.one_mul]
  have hdiag :
      (diagonal fun i => if hσ.isHermitian.eigenvalues i ≠ 0 then (1 : ℂ) else 0) *
        diagonal (RCLike.ofReal ∘ spectralCornerRamp a b ∘ hσ.isHermitian.eigenvalues) =
      diagonal (RCLike.ofReal ∘ spectralCornerRamp a b ∘ hσ.isHermitian.eigenvalues) := by
    rw [diagonal_mul_diagonal]
    apply congrArg diagonal
    funext i
    by_cases he : hσ.isHermitian.eigenvalues i = 0
    · simp only [Function.comp_apply, he, spectralCornerRamp_eq_zero_of_le hab ha.le,
        RCLike.ofReal_zero, mul_zero]
    · simp only [ite_eq_left he, one_mul]
  simpa only [Matrix.mul_assoc] using congrArg
    (fun M => (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * M *
      star (hσ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) hdiag

end Matrix

end
