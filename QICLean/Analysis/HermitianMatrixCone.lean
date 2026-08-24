/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.FrobeniusHilbert
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.Subspace

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace RealInnerProductSpace
  Matrix.Norms.Frobenius

namespace SemidefiniteProgram

/-!
# The positive-semidefinite cone of Hermitian matrices

This file equips Hermitian matrices with Wolf's real trace pairing and realizes the
positive-semidefinite matrices as a self-dual proper cone.  Its interior is the
positive-definite locus, including when the index type is empty.
-/

variable (n : Type*) [Fintype n]

noncomputable def matrixRealLinearEquiv :
    EuclideanSpace ℂ (n × n) ≃ₗ[ℝ] Matrix n n ℂ :=
  (Matrix.frobeniusEquivEuclidean n n).symm.toLinearEquiv.restrictScalars ℝ

noncomputable def hermitianSubmodule : Submodule ℝ (EuclideanSpace ℂ (n × n)) where
  carrier := {x | (matrixRealLinearEquiv n x).IsHermitian}
  zero_mem' := by simp [matrixRealLinearEquiv]
  add_mem' hx hy := by
    change (matrixRealLinearEquiv n (_ + _)).IsHermitian
    rw [map_add]
    exact hx.add hy
  smul_mem' r x hx := by
    change (matrixRealLinearEquiv n (_ • _)).IsHermitian
    rw [map_smul]
    exact hx.smul (IsSelfAdjoint.all r)

abbrev HermitianMatrix := hermitianSubmodule n

namespace HermitianMatrix

noncomputable instance : CompleteSpace (HermitianMatrix n) :=
  FiniteDimensional.complete ℝ (HermitianMatrix n)

noncomputable def toMatrix (A : HermitianMatrix n) : Matrix n n ℂ :=
  matrixRealLinearEquiv n A.1

theorem toMatrix_isHermitian (A : HermitianMatrix n) : (toMatrix n A).IsHermitian := A.2

noncomputable def ofMatrix (A : Matrix n n ℂ) (hA : A.IsHermitian) : HermitianMatrix n :=
  ⟨Matrix.frobeniusEquivEuclidean n n A, by
    change ((Matrix.frobeniusEquivEuclidean n n).symm
      (Matrix.frobeniusEquivEuclidean n n A)).IsHermitian
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact hA⟩

@[simp] theorem toMatrix_ofMatrix (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    toMatrix n (ofMatrix n A hA) = A := by
  change (Matrix.frobeniusEquivEuclidean n n).symm
    (Matrix.frobeniusEquivEuclidean n n A) = A
  exact LinearIsometryEquiv.symm_apply_apply _ _

@[simp] theorem toMatrix_zero : toMatrix n (0 : HermitianMatrix n) = 0 := by
  simp [toMatrix, matrixRealLinearEquiv]

@[simp] theorem toMatrix_add (A B : HermitianMatrix n) :
    toMatrix n (A + B) = toMatrix n A + toMatrix n B := by
  simp [toMatrix, matrixRealLinearEquiv]

@[simp] theorem toMatrix_sub (A B : HermitianMatrix n) :
    toMatrix n (A - B) = toMatrix n A - toMatrix n B := by
  simp [toMatrix, matrixRealLinearEquiv]

@[simp] theorem toMatrix_smul (r : ℝ) (A : HermitianMatrix n) :
    toMatrix n (r • A) = (r : ℂ) • toMatrix n A := by
  simp [toMatrix, matrixRealLinearEquiv]

private theorem continuous_toMatrix : Continuous (toMatrix n) := by
  exact (Matrix.frobeniusEquivEuclidean n n).symm.continuous.comp continuous_subtype_val

private theorem real_inner_eq_complex_re
    (x y : EuclideanSpace ℂ (n × n)) :
    inner ℝ x y = (inner ℂ x y).re := by
  simp [PiLp.inner_apply, RCLike.inner_apply, Complex.inner]

/-- The real Frobenius inner product on Hermitian matrices is Wolf's real trace pairing. -/
theorem inner_eq_re_trace_mul (A B : HermitianMatrix n) :
    inner ℝ A B = (Matrix.trace (toMatrix n A * toMatrix n B)).re := by
  change inner ℝ (A : EuclideanSpace ℂ (n × n))
      (B : EuclideanSpace ℂ (n × n)) = _
  rw [real_inner_eq_complex_re]
  have hA : Matrix.frobeniusEquivEuclidean n n (toMatrix n A) = A := by
    exact LinearIsometryEquiv.apply_symm_apply _ _
  have hB : Matrix.frobeniusEquivEuclidean n n (toMatrix n B) = B := by
    exact LinearIsometryEquiv.apply_symm_apply _ _
  rw [← hA, ← hB, Matrix.inner_frobeniusEquivEuclidean,
    (toMatrix_isHermitian n A).eq]

/-- The trace of a product of Hermitian matrices is real and equals the real Frobenius pairing. -/
theorem trace_mul_eq_ofReal_inner (A B : HermitianMatrix n) :
    Matrix.trace (toMatrix n A * toMatrix n B) = (inner ℝ A B : ℂ) := by
  apply Complex.ext
  · exact (inner_eq_re_trace_mul n A B).symm
  · rw [Complex.ofReal_im]
    apply (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
    rw [isSelfAdjoint_iff, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      (toMatrix_isHermitian n A).eq, (toMatrix_isHermitian n B).eq, Matrix.trace_mul_comm]

noncomputable def psdCone : ProperCone ℝ (HermitianMatrix n) where
  carrier := {A | (toMatrix n A).PosSemidef}
  zero_mem' := by
    change (toMatrix n (0 : HermitianMatrix n)).PosSemidef
    rw [toMatrix_zero]
    exact Matrix.PosSemidef.zero
  add_mem' hA hB := by simpa using hA.add hB
  smul_mem' := by
    intro r A hA
    change (toMatrix n ((r : ℝ) • A)).PosSemidef
    rw [toMatrix_smul]
    exact hA.smul (a := (r : ℝ)) r.2
  isClosed' := Matrix.posSemidef_is_closed.preimage (continuous_toMatrix n)

@[simp] theorem mem_psdCone_iff (A : HermitianMatrix n) :
    A ∈ psdCone n ↔ (toMatrix n A).PosSemidef := Iff.rfl

/-- The positive-semidefinite cone of Hermitian matrices is self-dual for the real Frobenius
inner product. -/
theorem mem_innerDual_psdCone_iff (A : HermitianMatrix n) :
    A ∈ ProperCone.innerDual (psdCone n : Set (HermitianMatrix n)) ↔ A ∈ psdCone n := by
  constructor
  · intro hA
    apply Matrix.PosSemidef.of_forall_trace_mul_nonneg (toMatrix_isHermitian n A)
    intro B hB
    let B' : HermitianMatrix n := ofMatrix n B hB.isHermitian
    have hinner : 0 ≤ inner ℝ B' A := ProperCone.mem_innerDual.mp hA hB
    have hre : 0 ≤ (Matrix.trace (toMatrix n A * B)).re := by
      rw [inner_eq_re_trace_mul, toMatrix_ofMatrix, Matrix.trace_mul_comm] at hinner
      exact hinner
    have hself : IsSelfAdjoint (Matrix.trace (toMatrix n A * B)) := by
      rw [isSelfAdjoint_iff, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
        (toMatrix_isHermitian n A).eq, hB.isHermitian.eq, Matrix.trace_mul_comm]
    exact (Complex.re_nonneg_iff_nonneg hself).mp hre
  · intro hA
    apply ProperCone.mem_innerDual.mpr
    intro B hB
    rw [inner_eq_re_trace_mul]
    exact (Complex.nonneg_iff.mp (hB.trace_mul_nonneg hA)).1

theorem innerDual_psdCone :
    ProperCone.innerDual (psdCone n : Set (HermitianMatrix n)) = psdCone n := by
  ext A
  exact mem_innerDual_psdCone_iff n A

/-- Positive definiteness is strict positivity of the trace pairing against every nonzero
positive-semidefinite Hermitian matrix. -/
theorem posDef_iff_forall_inner_pos (A : HermitianMatrix n) :
    (toMatrix n A).PosDef ↔
      ∀ B : HermitianMatrix n, B ∈ psdCone n → B ≠ 0 → 0 < inner ℝ B A := by
  constructor
  · intro hA B hB hBne
    rw [inner_eq_re_trace_mul]
    have hnonneg := hB.trace_mul_nonneg hA.posSemidef
    have htrace_ne : Matrix.trace (toMatrix n B * toMatrix n A) ≠ 0 := by
      intro htrace
      apply hBne
      apply Subtype.ext
      apply (matrixRealLinearEquiv n).injective
      change toMatrix n B = toMatrix n (0 : HermitianMatrix n)
      rw [toMatrix_zero]
      apply Matrix.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero hB hA
      rw [Matrix.trace_mul_comm]
      exact htrace
    have hre_nonneg : 0 ≤ (Matrix.trace (toMatrix n B * toMatrix n A)).re :=
      (Complex.nonneg_iff.mp hnonneg).1
    exact lt_of_le_of_ne hre_nonneg fun hre_eq ↦ htrace_ne <|
      Complex.ext hre_eq.symm (by simpa using (Complex.nonneg_iff.mp hnonneg).2.symm)
  · intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (toMatrix_isHermitian n A)
    intro x hx
    let P : Matrix n n ℂ := Matrix.vecMulVec x (star x)
    have hP : P.PosSemidef := Matrix.posSemidef_vecMulVec_self_star x
    let P' : HermitianMatrix n := ofMatrix n P hP.isHermitian
    have hPne : P' ≠ 0 := by
      intro hzero
      have hmatrix' := congrArg (toMatrix n) hzero
      have hmatrix : P = 0 := by
        simpa [P', toMatrix_ofMatrix, toMatrix_zero] using hmatrix'
      exact (Matrix.vecMulVec_ne_zero hx (star_ne_zero.mpr hx)) hmatrix
    have hpos := h P' hP hPne
    rw [inner_eq_re_trace_mul, toMatrix_ofMatrix] at hpos
    have hre : 0 < (star x ⬝ᵥ (toMatrix n A).mulVec x).re := by
      rw [Matrix.trace_mul_comm] at hpos
      change 0 < (Matrix.trace
        (toMatrix n A * Matrix.vecMulVec x (star x))).re at hpos
      rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] at hpos
      exact hpos
    rw [Complex.pos_iff]
    exact ⟨hre, (toMatrix_isHermitian n A).im_star_dotProduct_mulVec_self x |>.symm⟩

private theorem forall_inner_pos_of_mem_interior {A : HermitianMatrix n}
    (hA : A ∈ interior (psdCone n : Set (HermitianMatrix n))) :
    ∀ B : HermitianMatrix n, B ∈ psdCone n → B ≠ 0 → 0 < inner ℝ B A := by
  intro B hB hBne
  have hAcone : A ∈ psdCone n := interior_subset hA
  have hnonneg : 0 ≤ inner ℝ B A :=
    by simpa [real_inner_comm] using
      ProperCone.mem_innerDual.mp ((mem_innerDual_psdCone_iff n B).mpr hB) hAcone
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hA)
  by_contra hnot
  have hzero : inner ℝ B A = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hBnorm : 0 < ‖B‖ := norm_pos_iff.mpr hBne
  let δ : ℝ := ε / (2 * ‖B‖)
  have hδ : 0 < δ := div_pos hε (mul_pos two_pos hBnorm)
  let A' : HermitianMatrix n := A - δ • B
  have hdist : dist A' A < ε := by
    rw [dist_eq_norm]
    rw [show A' - A = (-δ) • B by dsimp [A']; module]
    rw [norm_smul, Real.norm_eq_abs, abs_of_neg (neg_lt_zero.mpr hδ), neg_neg]
    have hδnorm : δ * ‖B‖ = ε / 2 := by
      dsimp [δ]
      field_simp [hBnorm.ne']
      exact div_self hBnorm.ne'
    rw [hδnorm]
    linarith
  have hA' : A' ∈ psdCone n := hball (Metric.mem_ball.mpr hdist)
  have hinner_nonneg : 0 ≤ inner ℝ B A' :=
    by simpa [real_inner_comm] using
      ProperCone.mem_innerDual.mp ((mem_innerDual_psdCone_iff n B).mpr hB) hA'
  have hinner_neg : inner ℝ B A' < 0 := by
    rw [show A' = A - δ • B by rfl, inner_sub_right, real_inner_smul_right,
      hzero, zero_sub]
    exact neg_lt_zero.mpr (mul_pos hδ (real_inner_self_pos.mpr hBne))
  exact (not_le_of_gt hinner_neg) hinner_nonneg

private theorem mem_interior_of_forall_inner_pos [Nonempty n] {A : HermitianMatrix n}
    (hA : ∀ B : HermitianMatrix n, B ∈ psdCone n → B ≠ 0 → 0 < inner ℝ B A) :
    A ∈ interior (psdCone n : Set (HermitianMatrix n)) := by
  classical
  let S : Set (HermitianMatrix n) :=
    Metric.sphere 0 1 ∩ (psdCone n : Set (HermitianMatrix n))
  let f : HermitianMatrix n → ℝ := fun B ↦ inner ℝ B A
  let I' : HermitianMatrix n := ofMatrix n (1 : Matrix n n ℂ) Matrix.isHermitian_one
  have hI' : I' ∈ psdCone n := by
    change (toMatrix n I').PosSemidef
    simpa [I'] using (Matrix.PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef)
  have hI'ne : I' ≠ 0 := by
    intro hzero
    have hmatrix := congrArg (toMatrix n) hzero
    have : (1 : Matrix n n ℂ) = 0 := by
      simp only [I', toMatrix_ofMatrix, toMatrix_zero] at hmatrix
      exact hmatrix
    exact one_ne_zero this
  have hI'norm : 0 < ‖I'‖ := norm_pos_iff.mpr hI'ne
  let U : HermitianMatrix n := ‖I'‖⁻¹ • I'
  have hUmem : U ∈ S := by
    constructor
    · rw [Metric.mem_sphere, dist_zero_right]
      change ‖‖I'‖⁻¹ • I'‖ = 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hI'norm.le)]
      exact inv_mul_cancel₀ hI'norm.ne'
    · exact (psdCone n).smul_mem hI' (inv_nonneg.mpr hI'norm.le)
  let _ : ProperSpace (HermitianMatrix n) := FiniteDimensional.proper ℝ _
  have hScompact : IsCompact S :=
    (isCompact_sphere (0 : HermitianMatrix n) 1).inter_right (psdCone n).isClosed
  have hfcontinuous : Continuous f := by fun_prop
  obtain ⟨B₀, hB₀S, hB₀min⟩ :=
    hScompact.exists_isMinOn ⟨U, hUmem⟩ hfcontinuous.continuousOn
  let c : ℝ := f B₀
  have hB₀ne : B₀ ≠ 0 := by
    intro hzero
    have := hB₀S.1
    simp [hzero] at this
  have hc : 0 < c := hA B₀ hB₀S.2 hB₀ne
  apply mem_interior_iff_mem_nhds.mpr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨c, hc, ?_⟩
  intro X hX
  apply (mem_innerDual_psdCone_iff n X).mp
  apply ProperCone.mem_innerDual.mpr
  intro B hB
  by_cases hBzero : B = 0
  · simp [hBzero]
  have hBnorm : 0 < ‖B‖ := norm_pos_iff.mpr hBzero
  let B' : HermitianMatrix n := ‖B‖⁻¹ • B
  have hB'S : B' ∈ S := by
    constructor
    · rw [Metric.mem_sphere, dist_zero_right]
      change ‖‖B‖⁻¹ • B‖ = 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hBnorm.le)]
      exact inv_mul_cancel₀ hBnorm.ne'
    · exact (psdCone n).smul_mem hB (inv_nonneg.mpr hBnorm.le)
  have hc_le : c ≤ inner ℝ B' A := hB₀min hB'S
  have hdistXA : ‖X - A‖ < c := by
    simpa [Metric.mem_ball, dist_eq_norm] using hX
  have hperturb : -(c : ℝ) < inner ℝ B' (X - A) := by
    have habs := abs_real_inner_le_norm B' (X - A)
    have hB'norm : ‖B'‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hB'S.1
    rw [hB'norm, one_mul] at habs
    exact lt_of_lt_of_le (neg_lt_neg hdistXA) (neg_le_of_abs_le habs)
  have hB'X : 0 < inner ℝ B' X := by
    rw [show X = A + (X - A) by abel, inner_add_right]
    linarith
  have hscale : inner ℝ B X = ‖B‖ * inner ℝ B' X := by
    change inner ℝ B X = ‖B‖ * inner ℝ (‖B‖⁻¹ • B) X
    rw [real_inner_smul_left]
    field_simp
  rw [hscale]
  exact (mul_pos hBnorm hB'X).le

private theorem interior_psdCone_eq_posDef_of_nonempty [Nonempty n] :
    interior (psdCone n : Set (HermitianMatrix n)) =
      {A | (toMatrix n A).PosDef} := by
  ext A
  rw [Set.mem_ofPred_eq, posDef_iff_forall_inner_pos]
  exact ⟨forall_inner_pos_of_mem_interior n, mem_interior_of_forall_inner_pos n⟩

private theorem interior_psdCone_eq_posDef_of_isEmpty [IsEmpty n] :
    interior (psdCone n : Set (HermitianMatrix n)) =
      {A | (toMatrix n A).PosDef} := by
  ext A
  constructor
  · intro _hA
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (toMatrix_isHermitian n A)
    intro x hx
    exact False.elim (hx (Subsingleton.elim x 0))
  · intro _hA
    have hcone : (psdCone n : Set (HermitianMatrix n)) = Set.univ := by
      ext B
      constructor
      · intro _
        exact Set.mem_univ B
      · intro _
        have hzero : toMatrix n B = 0 := Subsingleton.elim _ _
        change (toMatrix n B).PosSemidef
        rw [hzero]
        exact Matrix.PosSemidef.zero
    rw [hcone]
    simp

/-- The interior of the positive-semidefinite cone is exactly the positive-definite locus,
including the zero-dimensional Hermitian matrix space. -/
theorem interior_psdCone_eq_posDef :
    interior (psdCone n : Set (HermitianMatrix n)) =
      {A | (toMatrix n A).PosDef} := by
  rcases isEmpty_or_nonempty n with hn | hn
  · let _ := hn
    exact interior_psdCone_eq_posDef_of_isEmpty n
  · let _ := hn
    exact interior_psdCone_eq_posDef_of_nonempty n

theorem mem_interior_psdCone_iff_posDef (A : HermitianMatrix n) :
    A ∈ interior (psdCone n : Set (HermitianMatrix n)) ↔ (toMatrix n A).PosDef := by
  rw [interior_psdCone_eq_posDef]
  rfl

end HermitianMatrix
end SemidefiniteProgram
