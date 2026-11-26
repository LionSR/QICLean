/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import QICLean.Analysis.FunctionalCalculus.MatrixPolar
import QICLean.Analysis.FunctionalCalculus.MatrixPolarUniqueness

/-!
# Left polar decomposition on the physical support

For a physical tensor map \(P\), the left polar decomposition is
\(P=QW\), with \(Q=(PP^\dagger)^{1/2}\) on its physical support and
\(WW^\dagger\) the projection onto that support. Extending \(Q\) by the
identity on the orthogonal complement makes it positive definite on the
whole physical space, without changing \(QW=P\). This permits the affine
positive deformation in the original physical space.

Source: arXiv:1010.3732, eq. (1d-iso:polardec), lines 575--594.

Moved from TNLean, `TNLean/MPS/ParentHamiltonian/Deformation/LeftPolar.lean`,
`TNLean/MPS/ParentHamiltonian/Deformation/IsometricDeformationCovariance.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

section

open scoped Matrix MatrixOrder ComplexOrder

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The positive polar factor extended by the identity on its kernel.
Source: arXiv:1010.3732, eq. (1d-iso:polardec), with the identity extension
from the retained physical space to its orthogonal complement. -/
noncomputable def polarPosExtension (M : Matrix ι κ ℂ) : Matrix κ κ ℂ :=
  polarPos M + (1 - polarSupport M)

omit [DecidableEq ι] in
/-- Extending the positive polar factor by the identity on its kernel gives
a positive-definite matrix. Source: arXiv:1010.3732, lines 579--584. -/
theorem posDef_polarPosExtension (M : Matrix ι κ ℂ) : (polarPosExtension M).PosDef := by
  have hE : IsStarProjection (polarSupport M) :=
    ⟨polarSupport_mul_polarSupport M, isHermitian_polarSupport M⟩
  have hQ : (polarPosExtension M).PosSemidef :=
    (posSemidef_polarPos M).add (nonneg_iff_posSemidef.mp hE.one_sub.nonneg)
  refine hQ.posDef_iff_mulVec_injective.2
    (LinearMap.ker_eq_bot.1 ((LinearMap.ker_eq_bot'
      (f := (polarPosExtension M).mulVecLin)).2 ?_))
  intro x hx
  change polarPosExtension M *ᵥ x = 0 at hx
  have hEQ : polarSupport M * polarPosExtension M = polarPos M := by
    simp [polarPosExtension, Matrix.mul_add, Matrix.mul_sub,
      polarSupport_mul_polarPos, polarSupport_mul_polarSupport]
  have hPx : polarPos M *ᵥ x = 0 := by
    simpa only [← mulVec_mulVec, hx, mulVec_zero] using
      congrArg (fun T : Matrix κ κ ℂ => T *ᵥ x) hEQ.symm
  obtain ⟨R, hR⟩ := exists_polarPos_mul_eq_polarSupport M
  have hR' : Rᴴ * polarPos M = polarSupport M := by
    simpa only [conjTranspose_mul, (posSemidef_polarPos M).isHermitian.eq,
      (isHermitian_polarSupport M).eq] using congrArg conjTranspose hR
  have hEx : polarSupport M *ᵥ x = 0 := by
    simpa only [← mulVec_mulVec, hPx, mulVec_zero] using
      congrArg (fun T : Matrix κ κ ℂ => T *ᵥ x) hR'.symm
  simpa only [polarPosExtension, add_mulVec, sub_mulVec, one_mulVec,
    hPx, hEx, sub_zero, zero_add] using hx

/-- The positive left polar factor, extended by the identity outside the
physical support. Source: arXiv:1010.3732, eq. (1d-iso:polardec). -/
noncomputable def leftPolarPos (M : Matrix ι κ ℂ) : Matrix ι ι ℂ :=
  polarPosExtension Mᴴ

/-- The partial isometry in the left polar decomposition.
Source: arXiv:1010.3732, eq. (1d-iso:polardec). -/
noncomputable def leftPolarIso (M : Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  (polarIso Mᴴ)ᴴ

omit [DecidableEq κ] in
/-- The left positive factor is positive definite on the whole physical
space. Source: arXiv:1010.3732, lines 579--584, with identity extension
outside the retained physical space. -/
theorem posDef_leftPolarPos (M : Matrix ι κ ℂ) : (leftPolarPos M).PosDef :=
  posDef_polarPosExtension Mᴴ

omit [DecidableEq κ] in
/-- The left partial isometry has the physical support as its final
projection. Source: arXiv:1010.3732, lines 579--584; on the retained
physical space this is \(WW^\dagger=I\). -/
theorem leftPolarIso_mul_conjTranspose (M : Matrix ι κ ℂ) :
    leftPolarIso M * (leftPolarIso M)ᴴ = polarSupport Mᴴ := by
  simpa only [leftPolarIso, conjTranspose_conjTranspose] using
    conjTranspose_polarIso_mul_polarIso Mᴴ

omit [DecidableEq κ] in
/-- The identity extension of the positive factor leaves the left polar
factorization unchanged. Source: arXiv:1010.3732, eq. (1d-iso:polardec). -/
theorem leftPolarPos_mul_leftPolarIso (M : Matrix ι κ ℂ) :
    leftPolarPos M * leftPolarIso M = M := by
  have hVE : polarIso Mᴴ * polarSupport Mᴴ = polarIso Mᴴ :=
    mul_eq_self_of_conjTranspose_mul_self_eq
      (conjTranspose_polarIso_mul_polarIso Mᴴ)
      (isHermitian_polarSupport Mᴴ) (polarSupport_mul_polarSupport Mᴴ)
  have hEV : polarSupport Mᴴ * (polarIso Mᴴ)ᴴ = (polarIso Mᴴ)ᴴ := by
    simpa only [conjTranspose_mul, (isHermitian_polarSupport Mᴴ).eq] using
      congrArg conjTranspose hVE
  simpa only [leftPolarPos, polarPosExtension, leftPolarIso, Matrix.add_mul,
    Matrix.sub_mul, Matrix.one_mul, hEV, sub_self, add_zero, conjTranspose_mul,
    (posSemidef_polarPos Mᴴ).isHermitian.eq, conjTranspose_conjTranspose] using
      congrArg conjTranspose (polarIso_mul_polarPos Mᴴ)

omit [DecidableEq κ] in
/-- The final projection of the left polar factor projects onto the range
of the original physical map. Source: arXiv:1010.3732, lines 579--584. -/
theorem range_leftPolarIso_finalProjection (M : Matrix ι κ ℂ) :
    LinearMap.range (polarSupport Mᴴ).mulVecLin = LinearMap.range M.mulVecLin := by
  have hP : M * polarIso Mᴴ = polarPos Mᴴ := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose,
      (posSemidef_polarPos Mᴴ).isHermitian.eq] using
        congrArg conjTranspose (conjTranspose_polarIso_mul_self Mᴴ)
  obtain ⟨R, hR⟩ := exists_polarPos_mul_eq_polarSupport Mᴴ
  have hEM : polarSupport Mᴴ * M = M := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose,
      (isHermitian_polarSupport Mᴴ).eq] using
        congrArg conjTranspose (mul_polarSupport Mᴴ)
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine ⟨polarIso Mᴴ *ᵥ (R *ᵥ x), ?_⟩
    simp only [mulVecLin_apply, mulVec_mulVec, ← Matrix.mul_assoc, hP, hR]
  · rintro _ ⟨x, rfl⟩
    exact ⟨M *ᵥ x, by simp only [mulVecLin_apply, mulVec_mulVec, hEM]⟩

end Matrix

end

section

open scoped Matrix MatrixOrder ComplexOrder

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A unitary physical--virtual intertwining relation makes the physical
Gram matrix commute with the physical action. Source: arXiv:1010.3732,
lines 658--671. -/
theorem commute_mul_conjTranspose_of_unitary_covariance
    (P : Matrix ι κ ℂ) (U : Matrix ι ι ℂ) (X : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hX : X ∈ unitaryGroup κ ℂ)
    (hCov : U * P = P * X) : Commute U (P * Pᴴ) := by
  have hAdj := congrArg conjTranspose hCov
  simp only [conjTranspose_mul] at hAdj
  have hXX : X * Xᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hX
  have hConj : U * (P * Pᴴ) * Uᴴ = P * Pᴴ := by
    calc
      U * (P * Pᴴ) * Uᴴ = (U * P) * (Pᴴ * Uᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = (P * X) * (Xᴴ * Pᴴ) := by rw [hCov, hAdj]
      _ = P * Pᴴ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc X Xᴴ Pᴴ,
          hXX, Matrix.one_mul]
  have hUU : Uᴴ * U = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hU
  calc
    U * (P * Pᴴ) = (U * (P * Pᴴ) * Uᴴ) * U := by
      rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
    _ = (P * Pᴴ) * U := by rw [hConj]

/-- The physical support projection commutes with the physical unitary in
an exact unitary covariance. Source: arXiv:1010.3732, lines 645--676;
this also justifies extending the polar factor by the identity off support. -/
theorem commute_leftPolarSupport_of_unitary_covariance
    (P : Matrix ι κ ℂ) (U : Matrix ι ι ℂ) (X : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hX : X ∈ unitaryGroup κ ℂ)
    (hCov : U * P = P * X) : Commute U (polarSupport Pᴴ) := by
  have hGram := commute_mul_conjTranspose_of_unitary_covariance P U X hU hX hCov
  unfold polarSupport
  simp only [conjTranspose_conjTranspose]
  exact (hGram.symm.cfc_real _).symm

/-- The positive left polar factor commutes with a unitary physical action
intertwined with a virtual unitary. The assertion includes the identity
extension outside the physical support. Source: arXiv:1010.3732,
lines 658--676. -/
theorem commute_leftPolarPos_of_unitary_covariance
    (P : Matrix ι κ ℂ) (U : Matrix ι ι ℂ) (X : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hX : X ∈ unitaryGroup κ ℂ)
    (hCov : U * P = P * X) : Commute U (leftPolarPos P) := by
  have hGram := commute_mul_conjTranspose_of_unitary_covariance P U X hU hX hCov
  have hPos : Commute U (polarPos Pᴴ) := by
    simpa only [polarPos, CFC.sqrt, conjTranspose_conjTranspose] using
      (hGram.symm.cfcₙ_nnreal NNReal.sqrt).symm
  exact hPos.add_right ((Commute.one_right U).sub_right
    (commute_leftPolarSupport_of_unitary_covariance P U X hU hX hCov))

/-- The left partial isometry has the same physical--virtual covariance
as the original matrix. Source: arXiv:1010.3732, lines 658--676. -/
theorem leftPolarIso_covariance_of_unitary_covariance
    (P : Matrix ι κ ℂ) (U : Matrix ι ι ℂ) (X : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hX : X ∈ unitaryGroup κ ℂ)
    (hCov : U * P = P * X) : U * leftPolarIso P = leftPolarIso P * X := by
  let := (posDef_leftPolarPos P).isUnit.invertible
  apply mul_right_injective_of_invertible (leftPolarPos P)
  have hComm := commute_leftPolarPos_of_unitary_covariance P U X hU hX hCov
  calc
    leftPolarPos P * (U * leftPolarIso P) = U * (leftPolarPos P * leftPolarIso P) := by
      rw [← Matrix.mul_assoc, ← hComm.eq, Matrix.mul_assoc]
    _ = U * P := by rw [leftPolarPos_mul_leftPolarIso]
    _ = P * X := hCov
    _ = (leftPolarPos P * leftPolarIso P) * X :=
      congrArg (· * X) (leftPolarPos_mul_leftPolarIso P).symm
    _ = leftPolarPos P * (leftPolarIso P * X) := Matrix.mul_assoc _ _ _

end Matrix

end
