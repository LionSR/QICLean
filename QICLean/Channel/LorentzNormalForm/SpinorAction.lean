/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.SpinCover.Basic
import QICLean.Channel.LorentzNormalForm.Basic
import QICLean.Channel.LorentzNormalForm.QubitNormalForm
import Mathlib.Algebra.Star.Module
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The spinor action on qubit Pauli coordinates

This module formalizes the four-dimensional action in Wolf, Equations (2.41)--(2.43).
For `X ∈ SL(2,ℂ)`, the action is the Hermitian congruence
`M ↦ X * M * Xᴴ`.  In the real Pauli coordinates of a Hermitian qubit matrix,
this action preserves the Minkowski determinant form.

This is not `SpinCover.pauliConjAd`: that existing construction is the
three-dimensional adjoint action `M ↦ U * M * U⁻¹` on the traceless Pauli
matrices.  The two constructions agree on the spatial block only when the
conjugating matrix is unitary.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Equations (2.41)--(2.44)]
* `Notes/WolfNoteTexSource/ch02_representations.tex`, lines 1037--1081
-/

open scoped Matrix MatrixGroups BigOperators ComplexOrder
open Matrix Finset

noncomputable section

namespace Wolf

/-! ### Pauli coordinates and the Minkowski determinant form -/

/-- The real four-dimensional coordinate space used in Wolf, Equation (2.41). -/
abbrev MinkowskiSpace := Fin 4 → ℝ

@[simp] theorem pauliMatrices_zero : pauliMatrices 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The spatial Pauli matrices in the four-coordinate convention agree with
the three Pauli matrices in `SpinCover`. -/
@[simp] theorem pauliMatrices_succ (i : Fin 3) :
    pauliMatrices i.succ = SpinCover.pauli i := by
  fin_cases i <;> rfl

/-- Each of the four Pauli matrices is Hermitian. -/
theorem pauliMatrices_isHermitian (i : Fin 4) : (pauliMatrices i).IsHermitian := by
  fin_cases i <;>
    (rw [Matrix.IsHermitian]
     ext a b
     fin_cases a <;> fin_cases b <;>
       simp [pauliMatrices, Matrix.conjTranspose_apply, Complex.conj_I])

/-- The trace pairing of the four Pauli matrices is
`tr(σᵢ σⱼ) = 2 δᵢⱼ`. -/
theorem trace_pauliMatrices_mul_pauliMatrices (i j : Fin 4) :
    Matrix.trace (pauliMatrices i * pauliMatrices j) = if i = j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliMatrices, Matrix.trace_fin_two, Matrix.mul_apply]

/-- The Hermitian qubit matrix with real Pauli coordinates `x`, namely
`M(x) = ∑ᵢ xᵢ σᵢ` in Wolf, lines 1040--1043. -/
def pauliMatrixOfMinkowski (x : MinkowskiSpace) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i : Fin 4, (x i : ℂ) • pauliMatrices i

/-- A matrix assembled from real Pauli coordinates is Hermitian. -/
theorem pauliMatrixOfMinkowski_isHermitian (x : MinkowskiSpace) :
    (pauliMatrixOfMinkowski x).IsHermitian := by
  apply isSelfAdjoint_sum
  intro i _
  exact (pauliMatrices_isHermitian i).smul (by simp [isSelfAdjoint_iff])

/-- The Minkowski quadratic form
`x₀² - x₁² - x₂² - x₃²` in Wolf, lines 1041--1044. -/
def minkowskiQuadratic (x : MinkowskiSpace) : ℝ :=
  x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2

/-- The Minkowski bilinear form with signature `(1, 3)` used in Wolf,
Equation (2.42). -/
def minkowskiBilinear (x y : MinkowskiSpace) : ℝ :=
  x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

/-- The diagonal matrix `η = diag(1, -1, -1, -1)` in Wolf,
Equation (2.42). -/
def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  diagonal fun i ↦ if i = 0 then 1 else -1

theorem minkowskiQuadratic_eq_bilinear_self (x : MinkowskiSpace) :
    minkowskiQuadratic x = minkowskiBilinear x x := by
  simp [minkowskiQuadratic, minkowskiBilinear, pow_two]

/-- The coordinate formula for the bilinear form in terms of `η`. -/
theorem minkowskiBilinear_eq_dotProduct_metric_mulVec (x y : MinkowskiSpace) :
    minkowskiBilinear x y = dotProduct x (minkowskiMetric *ᵥ y) := by
  simp [minkowskiBilinear, minkowskiMetric, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]
  ring

/-- Polarization of the Minkowski determinant form. -/
theorem minkowskiBilinear_polarization (x y : MinkowskiSpace) :
    2 * minkowskiBilinear x y =
      minkowskiQuadratic (x + y) - minkowskiQuadratic x - minkowskiQuadratic y := by
  simp only [minkowskiBilinear, minkowskiQuadratic, Pi.add_apply]
  ring

@[simp] theorem minkowskiMetric_mul_self :
    minkowskiMetric * minkowskiMetric = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [minkowskiMetric, Matrix.mul_apply, Matrix.diagonal_apply,
      Fin.sum_univ_four]

/-- The determinant of a Hermitian qubit matrix is its Minkowski quadratic
form, as stated immediately before Wolf, Equation (2.41). -/
theorem det_pauliMatrixOfMinkowski (x : MinkowskiSpace) :
    Matrix.det (pauliMatrixOfMinkowski x) = (minkowskiQuadratic x : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [pauliMatrixOfMinkowski, Fin.sum_univ_four, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, pauliMatrices, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one]
  ring_nf
  rw [Complex.I_sq]
  simp [minkowskiQuadratic]
  ring

/-- The trace of `M(x)` is twice its time coordinate. -/
theorem trace_pauliMatrixOfMinkowski (x : MinkowskiSpace) :
    Matrix.trace (pauliMatrixOfMinkowski x) = (2 * x 0 : ℝ) := by
  simp [pauliMatrixOfMinkowski, pauliMatrices,
    Matrix.trace_fin_two, Fin.sum_univ_four]
  ring

/-- The closed future Lorentz cone in Pauli coordinates. -/
def InFutureCone (x : MinkowskiSpace) : Prop :=
  0 ≤ x 0 ∧ 0 ≤ minkowskiQuadratic x

/-- Under the Pauli-coordinate identification, the positive-semidefinite cone
of Hermitian qubit matrices is the closed future Lorentz cone. -/
theorem posSemidef_pauliMatrixOfMinkowski_iff (x : MinkowskiSpace) :
    (pauliMatrixOfMinkowski x).PosSemidef ↔ InFutureCone x := by
  let hM := pauliMatrixOfMinkowski_isHermitian x
  constructor
  · intro hPSD
    constructor
    · have htrace := Complex.nonneg_iff.mp hPSD.trace_nonneg |>.1
      rw [trace_pauliMatrixOfMinkowski] at htrace
      simpa using htrace
    · have hdet := Complex.nonneg_iff.mp hPSD.det_nonneg |>.1
      rw [det_pauliMatrixOfMinkowski] at hdet
      simpa using hdet
  · rintro ⟨hx₀, hq⟩
    rw [hM.posSemidef_iff_eigenvalues_nonneg]
    have hsum : hM.eigenvalues 0 + hM.eigenvalues 1 = 2 * x 0 := by
      have h := congrArg Complex.re hM.trace_eq_sum_eigenvalues
      rw [trace_pauliMatrixOfMinkowski] at h
      simpa [Fin.sum_univ_two] using h.symm
    have hprod : hM.eigenvalues 0 * hM.eigenvalues 1 = minkowskiQuadratic x := by
      have h := congrArg Complex.re hM.det_eq_prod_eigenvalues
      rw [det_pauliMatrixOfMinkowski] at h
      simpa [Fin.prod_univ_two] using h.symm
    intro i
    fin_cases i
    · by_contra hneg
      have h₀neg : hM.eigenvalues 0 < 0 := lt_of_not_ge hneg
      have h₁nonpos : hM.eigenvalues 1 ≤ 0 := by
        by_contra h₁
        have h₁pos : 0 < hM.eigenvalues 1 := lt_of_not_ge h₁
        nlinarith
      nlinarith
    · by_contra hneg
      have h₁neg : hM.eigenvalues 1 < 0 := lt_of_not_ge hneg
      have h₀nonpos : hM.eigenvalues 0 ≤ 0 := by
        by_contra h₀
        have h₀pos : 0 < hM.eigenvalues 0 := lt_of_not_ge h₀
        nlinarith
      nlinarith

/-- The real vector space of Hermitian qubit matrices. -/
abbrev HermitianQubitMatrix := selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)

/-- The trace pairing of two Hermitian matrices is real. -/
theorem trace_mul_eq_ofReal_re_of_isHermitian
    {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (((A * B).trace).re : ℂ) = (A * B).trace := by
  rw [← Complex.conj_eq_iff_re, starRingEnd_apply,
    ← Matrix.trace_conjTranspose,
    Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]

/-- The `i`-th real Pauli coordinate
`xᵢ = (1/2) tr(σᵢ M)` of a Hermitian qubit matrix. -/
def pauliMinkowskiCoordinate (M : HermitianQubitMatrix) (i : Fin 4) : ℝ :=
  (Matrix.trace (pauliMatrices i * (M : Matrix (Fin 2) (Fin 2) ℂ))).re / 2

/-- Pauli coordinates recover the coefficient of a real Pauli sum. -/
@[simp] theorem pauliMinkowskiCoordinate_pauliMatrixOfMinkowski
    (x : MinkowskiSpace) (i : Fin 4) :
    pauliMinkowskiCoordinate ⟨pauliMatrixOfMinkowski x,
      pauliMatrixOfMinkowski_isHermitian x⟩ i = x i := by
  simp only [pauliMinkowskiCoordinate, pauliMatrixOfMinkowski, Matrix.mul_sum,
    Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    trace_pauliMatrices_mul_pauliMatrices]
  simp

/-- For a Hermitian matrix, embedding a real Pauli coordinate into `ℂ`
recovers its trace-pairing coefficient. -/
theorem coe_pauliMinkowskiCoordinate (M : HermitianQubitMatrix) (i : Fin 4) :
    (pauliMinkowskiCoordinate M i : ℂ) =
      Matrix.trace (pauliMatrices i * (M : Matrix (Fin 2) (Fin 2) ℂ)) / 2 := by
  rw [pauliMinkowskiCoordinate, Complex.ofReal_div]
  rw [trace_mul_eq_ofReal_re_of_isHermitian (pauliMatrices_isHermitian i) M.property]
  norm_num

/-- Reassembling the real Pauli coordinates of a Hermitian qubit matrix
recovers that matrix. -/
theorem pauliMatrixOfMinkowski_pauliMinkowskiCoordinate
    (M : HermitianQubitMatrix) :
    pauliMatrixOfMinkowski (pauliMinkowskiCoordinate M) = M := by
  rw [pauliMatrixOfMinkowski, Fin.sum_univ_succ]
  simp_rw [coe_pauliMinkowskiCoordinate]
  rw [pauliMatrices_zero, Matrix.one_mul]
  simp_rw [pauliMatrices_succ]
  simpa using
    (SpinCover.pauli_expansion (M : Matrix (Fin 2) (Fin 2) ℂ)).symm

/-- Assembly of a Hermitian qubit matrix from its real Pauli coordinates,
as a real linear map. -/
noncomputable def pauliMatrixOfMinkowskiLinearMap :
    MinkowskiSpace →ₗ[ℝ] HermitianQubitMatrix where
  toFun x := ⟨pauliMatrixOfMinkowski x, pauliMatrixOfMinkowski_isHermitian x⟩
  map_add' x y := by
    apply Subtype.ext
    simp [pauliMatrixOfMinkowski, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    apply Subtype.ext
    change pauliMatrixOfMinkowski (c • x) = c • pauliMatrixOfMinkowski x
    simp only [pauliMatrixOfMinkowski, Pi.smul_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ext a b
    simp [Matrix.smul_apply, smul_eq_mul]
    ring

/-- Extraction of the real Pauli coordinates of a Hermitian qubit matrix,
as a real linear map. -/
noncomputable def pauliMinkowskiCoordinateLinearMap :
    HermitianQubitMatrix →ₗ[ℝ] MinkowskiSpace where
  toFun M := pauliMinkowskiCoordinate M
  map_add' M N := by
    ext i
    change
      (Matrix.trace (pauliMatrices i *
        ((M : Matrix (Fin 2) (Fin 2) ℂ) +
          (N : Matrix (Fin 2) (Fin 2) ℂ)))).re / 2 =
      pauliMinkowskiCoordinate M i + pauliMinkowskiCoordinate N i
    rw [Matrix.mul_add, Matrix.trace_add]
    simp [pauliMinkowskiCoordinate]
    ring
  map_smul' c M := by
    ext i
    change
      (Matrix.trace (pauliMatrices i *
        (c • (M : Matrix (Fin 2) (Fin 2) ℂ)))).re / 2 =
      c • pauliMinkowskiCoordinate M i
    rw [Matrix.mul_smul, Matrix.trace_smul]
    simp [pauliMinkowskiCoordinate, Complex.mul_re]
    ring

/-- The real-linear Pauli-coordinate equivalence
`M₂†(ℂ) ≃ ℝ⁴` used before Wolf, Equation (2.41). -/
noncomputable def pauliMinkowskiEquiv :
    MinkowskiSpace ≃ₗ[ℝ] HermitianQubitMatrix :=
  LinearEquiv.ofLinearMap pauliMatrixOfMinkowskiLinearMap
    pauliMinkowskiCoordinateLinearMap
    (by
      apply LinearMap.ext
      intro M
      apply Subtype.ext
      change pauliMatrixOfMinkowski (pauliMinkowskiCoordinate M) = M
      exact pauliMatrixOfMinkowski_pauliMinkowskiCoordinate M)
    (by
      apply LinearMap.ext
      intro x
      funext i
      change pauliMinkowskiCoordinate
        ⟨pauliMatrixOfMinkowski x, pauliMatrixOfMinkowski_isHermitian x⟩ i = x i
      exact pauliMinkowskiCoordinate_pauliMatrixOfMinkowski x i)

@[simp] theorem pauliMinkowskiEquiv_apply (x : MinkowskiSpace) :
    ((pauliMinkowskiEquiv x : HermitianQubitMatrix) :
      Matrix (Fin 2) (Fin 2) ℂ) = pauliMatrixOfMinkowski x := rfl

@[simp] theorem pauliMinkowskiEquiv_symm_apply (M : HermitianQubitMatrix) :
    pauliMinkowskiEquiv.symm M = pauliMinkowskiCoordinate M := rfl

/-! ### Hermitian congruence and the spinor action -/

private abbrev sl2InvMatrix (X : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (X⁻¹ : SL(2, ℂ)).1

/-- Congruence by `X ∈ SL(2,ℂ)` as a real-linear equivalence of Hermitian
qubit matrices. This is Wolf, Equation (2.41), and is distinct from the
three-dimensional adjoint action `SpinCover.pauliConjAd`. -/
noncomputable def sl2CongruenceLinearEquiv (X : SL(2, ℂ)) :
    HermitianQubitMatrix ≃ₗ[ℝ] HermitianQubitMatrix where
  toFun M := ⟨(X : Matrix (Fin 2) (Fin 2) ℂ) * M * X.1ᴴ,
    Matrix.isHermitian_mul_mul_conjTranspose X.1 M.property⟩
  invFun M := ⟨sl2InvMatrix X * M * (sl2InvMatrix X)ᴴ,
    Matrix.isHermitian_mul_mul_conjTranspose (sl2InvMatrix X) M.property⟩
  left_inv M := by
    apply Subtype.ext
    have hBA : sl2InvMatrix X * X.1 = 1 := by
      rw [sl2InvMatrix, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul,
        Matrix.SpecialLinearGroup.det_coe, one_smul]
    have hAhBh : X.1ᴴ * (sl2InvMatrix X)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hBA, Matrix.conjTranspose_one]
    change sl2InvMatrix X *
      ((X : Matrix (Fin 2) (Fin 2) ℂ) * M * X.1ᴴ) * (sl2InvMatrix X)ᴴ = M
    calc
      sl2InvMatrix X *
          ((X : Matrix (Fin 2) (Fin 2) ℂ) * M * X.1ᴴ) * (sl2InvMatrix X)ᴴ =
          (sl2InvMatrix X * X.1) * M *
            (X.1ᴴ * (sl2InvMatrix X)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hBA, hAhBh, Matrix.one_mul, Matrix.mul_one]
  right_inv M := by
    apply Subtype.ext
    have hAB : X.1 * sl2InvMatrix X = 1 := by
      rw [sl2InvMatrix, Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_adjugate,
        Matrix.SpecialLinearGroup.det_coe, one_smul]
    have hBhAh : (sl2InvMatrix X)ᴴ * X.1ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hAB, Matrix.conjTranspose_one]
    change (X : Matrix (Fin 2) (Fin 2) ℂ) *
      (sl2InvMatrix X * M * (sl2InvMatrix X)ᴴ) * X.1ᴴ = M
    calc
      (X : Matrix (Fin 2) (Fin 2) ℂ) *
          (sl2InvMatrix X * M * (sl2InvMatrix X)ᴴ) * X.1ᴴ =
          (X.1 * sl2InvMatrix X) * M *
            ((sl2InvMatrix X)ᴴ * X.1ᴴ) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hAB, hBhAh, Matrix.one_mul, Matrix.mul_one]
  map_add' M N := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by
    apply Subtype.ext
    simp

/-- The real-linear action on Minkowski coordinates induced by the Hermitian
congruence in Wolf, Equation (2.41). -/
noncomputable def spinorLinearEquiv (X : SL(2, ℂ)) :
    MinkowskiSpace ≃ₗ[ℝ] MinkowskiSpace :=
  (pauliMinkowskiEquiv.trans (sl2CongruenceLinearEquiv X)).trans
    pauliMinkowskiEquiv.symm

/-- The `4 × 4` real spinor matrix of `X ∈ SL(2,ℂ)` in the Pauli basis. -/
noncomputable def spinorMatrix (X : SL(2, ℂ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix' (spinorLinearEquiv X).toLinearMap

/-- The spinor matrix acts on coordinate columns by the induced real-linear
equivalence. -/
@[simp] theorem spinorMatrix_mulVec (X : SL(2, ℂ)) (x : MinkowskiSpace) :
    spinorMatrix X *ᵥ x = spinorLinearEquiv X x := by
  exact LinearMap.toMatrix'_mulVec _ _

/-- Covariance of Pauli coordinates under the Hermitian congruence
`M ↦ X M X†` of Wolf, Equation (2.41). -/
theorem pauliMatrixOfMinkowski_spinorMatrix_mulVec
    (X : SL(2, ℂ)) (x : MinkowskiSpace) :
    pauliMatrixOfMinkowski (spinorMatrix X *ᵥ x) =
      X.1 * pauliMatrixOfMinkowski x * X.1ᴴ := by
  rw [spinorMatrix_mulVec]
  change pauliMatrixOfMinkowski
    (pauliMinkowskiCoordinate
      ⟨X.1 * pauliMatrixOfMinkowski x * X.1ᴴ,
        Matrix.isHermitian_mul_mul_conjTranspose X.1
          (pauliMatrixOfMinkowski_isHermitian x)⟩) = _
  exact pauliMatrixOfMinkowski_pauliMinkowskiCoordinate _

/-- A standard coordinate vector assembles to the corresponding Pauli
matrix. -/
@[simp] theorem pauliMatrixOfMinkowski_single (j : Fin 4) :
    pauliMatrixOfMinkowski (Pi.single j 1) = pauliMatrices j := by
  simp [pauliMatrixOfMinkowski, Pi.single_apply]

/-- Trace formula for the spinor matrix entries:
`L(X)ᵢⱼ = (1/2) tr(σᵢ X σⱼ X†)`. The trace is real, so the
real part only records the codomain of `L(X)`. -/
theorem spinorMatrix_apply (X : SL(2, ℂ)) (i j : Fin 4) :
    spinorMatrix X i j =
      (Matrix.trace (pauliMatrices i *
        (X.1 * pauliMatrices j * X.1ᴴ))).re / 2 := by
  rw [spinorMatrix, LinearMap.toMatrix'_apply]
  change pauliMinkowskiCoordinate
    ⟨X.1 * pauliMatrixOfMinkowski (Pi.single j 1) * X.1ᴴ,
      Matrix.isHermitian_mul_mul_conjTranspose X.1
        (pauliMatrixOfMinkowski_isHermitian (Pi.single j 1))⟩ i = _
  simp only [pauliMinkowskiCoordinate, pauliMatrixOfMinkowski_single]

/-- The time-time entry is one half of the squared Frobenius norm of `X`. -/
theorem spinorMatrix_zero_zero (X : SL(2, ℂ)) :
    spinorMatrix X 0 0 =
      (Complex.normSq (X.1 0 0) + Complex.normSq (X.1 0 1) +
        Complex.normSq (X.1 1 0) + Complex.normSq (X.1 1 1)) / 2 := by
  rw [spinorMatrix_apply]
  norm_num [pauliMatrices, Matrix.trace_fin_two, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.vecMul_eq_sum, Fin.sum_univ_two,
    Complex.normSq_apply]
  ring

/-- The spinor action is time-orientation preserving: `L₀₀ > 0`, as in
Wolf, Equation (2.42). -/
theorem spinorMatrix_zero_zero_pos (X : SL(2, ℂ)) :
    0 < spinorMatrix X 0 0 := by
  rw [spinorMatrix_zero_zero]
  have hentry : X.1 0 0 ≠ 0 ∨ X.1 0 1 ≠ 0 ∨ X.1 1 0 ≠ 0 ∨ X.1 1 1 ≠ 0 := by
    by_contra h
    push Not at h
    rcases h with ⟨h₀₀, h₀₁, h₁₀, h₁₁⟩
    have hdet := X.2
    rw [Matrix.det_fin_two, h₀₀, h₀₁, h₁₀, h₁₁] at hdet
    norm_num at hdet
  rcases hentry with h | h | h | h
  all_goals
    nlinarith [Complex.normSq_pos.mpr h,
      Complex.normSq_nonneg (X.1 0 0), Complex.normSq_nonneg (X.1 0 1),
      Complex.normSq_nonneg (X.1 1 0), Complex.normSq_nonneg (X.1 1 1)]

/-- The spinor action preserves the Minkowski determinant form. This is the
linear-isometry assertion following Wolf, Equation (2.41). -/
theorem spinorMatrix_preserves_minkowskiQuadratic
    (X : SL(2, ℂ)) (x : MinkowskiSpace) :
    minkowskiQuadratic (spinorMatrix X *ᵥ x) = minkowskiQuadratic x := by
  apply Complex.ofReal_injective
  rw [← det_pauliMatrixOfMinkowski, ← det_pauliMatrixOfMinkowski,
    pauliMatrixOfMinkowski_spinorMatrix_mulVec, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose, Matrix.SpecialLinearGroup.det_coe]
  norm_num

/-- The spinor action preserves the polarized Minkowski bilinear form. -/
theorem spinorMatrix_preserves_minkowskiBilinear
    (X : SL(2, ℂ)) (x y : MinkowskiSpace) :
    minkowskiBilinear (spinorMatrix X *ᵥ x) (spinorMatrix X *ᵥ y) =
      minkowskiBilinear x y := by
  have hpolar := minkowskiBilinear_polarization
    (spinorMatrix X *ᵥ x) (spinorMatrix X *ᵥ y)
  rw [← Matrix.mulVec_add] at hpolar
  rw [spinorMatrix_preserves_minkowskiQuadratic,
    spinorMatrix_preserves_minkowskiQuadratic,
    spinorMatrix_preserves_minkowskiQuadratic] at hpolar
  nlinarith [minkowskiBilinear_polarization x y]

/-- The column-action form of Lorentz metric preservation. -/
theorem spinorMatrix_transpose_mul_metric_mul (X : SL(2, ℂ)) :
    (spinorMatrix X)ᵀ * minkowskiMetric * spinorMatrix X = minkowskiMetric := by
  ext i j
  have h := spinorMatrix_preserves_minkowskiBilinear X
    (Pi.single i 1) (Pi.single j 1)
  fin_cases i <;> fin_cases j <;>
    simp [minkowskiBilinear, minkowskiMetric, Matrix.mul_apply, Matrix.mulVec,
      Matrix.diagonal_apply, Fin.sum_univ_four] at h ⊢ <;>
    linarith

/-- The spinor action preserves the closed future Lorentz cone. Equivalently,
Hermitian positive semidefiniteness is preserved by `M ↦ X M X†`. -/
theorem spinorMatrix_mem_futureCone_iff (X : SL(2, ℂ)) (x : MinkowskiSpace) :
    InFutureCone (spinorMatrix X *ᵥ x) ↔ InFutureCone x := by
  rw [← posSemidef_pauliMatrixOfMinkowski_iff,
    pauliMatrixOfMinkowski_spinorMatrix_mulVec,
    ← posSemidef_pauliMatrixOfMinkowski_iff]
  have hX : IsUnit X.1 := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.SpecialLinearGroup.det_coe]
    exact isUnit_one
  simpa only [star_eq_conjTranspose] using
    (hX.posSemidef_star_right_conjugate_iff
      (x := pauliMatrixOfMinkowski x))

/-- The coordinate action respects multiplication in `SL(2,ℂ)`. -/
theorem spinorLinearEquiv_mul_apply (X Y : SL(2, ℂ)) (x : MinkowskiSpace) :
    spinorLinearEquiv (X * Y) x =
      spinorLinearEquiv X (spinorLinearEquiv Y x) := by
  apply pauliMinkowskiEquiv.injective
  apply Subtype.ext
  change pauliMatrixOfMinkowski (spinorLinearEquiv (X * Y) x) =
    pauliMatrixOfMinkowski (spinorLinearEquiv X (spinorLinearEquiv Y x))
  rw [← spinorMatrix_mulVec, pauliMatrixOfMinkowski_spinorMatrix_mulVec,
    ← spinorMatrix_mulVec X,
    pauliMatrixOfMinkowski_spinorMatrix_mulVec,
    ← spinorMatrix_mulVec Y,
    pauliMatrixOfMinkowski_spinorMatrix_mulVec]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

/-- The spinor matrix is multiplicative. -/
theorem spinorMatrix_mul (X Y : SL(2, ℂ)) :
    spinorMatrix (X * Y) = spinorMatrix X * spinorMatrix Y := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [← Matrix.mulVec_mulVec, spinorMatrix_mulVec, spinorMatrix_mulVec,
    spinorMatrix_mulVec]
  exact spinorLinearEquiv_mul_apply X Y x

/-- The identity element of `SL(2,ℂ)` induces the identity Lorentz
matrix. -/
@[simp] theorem spinorMatrix_one :
    spinorMatrix (1 : SL(2, ℂ)) = 1 := by
  ext i j
  rw [spinorMatrix_apply]
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.conjTranspose_one,
    Matrix.mul_one, Matrix.one_mul, trace_pauliMatrices_mul_pauliMatrices,
    Matrix.one_apply]
  split <;> norm_num

/-- The spinor action as a representation by real-linear equivalences. -/
noncomputable def spinorLinearEquivMap :
    SL(2, ℂ) →* (MinkowskiSpace ≃ₗ[ℝ] MinkowskiSpace) where
  toFun := spinorLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro x
    have h := spinorMatrix_mulVec (1 : SL(2, ℂ)) x
    rw [spinorMatrix_one, Matrix.one_mulVec] at h
    exact h.symm
  map_mul' X Y := by
    apply LinearEquiv.ext
    intro x
    simpa using spinorLinearEquiv_mul_apply X Y x

/-- The spinor matrix has determinant one, as required in Wolf,
Equation (2.42).

The determinant character has abelian codomain, whereas `SL(2,ℂ)` is
perfect; hence this character is trivial. This algebraic argument proves the
determinant condition only. It does not assert that the spinor map is
surjective or a double cover. -/
theorem spinorMatrix_det (X : SL(2, ℂ)) :
    Matrix.det (spinorMatrix X) = 1 := by
  let detCharacter : SL(2, ℂ) →* ℝˣ :=
    LinearEquiv.det.comp spinorLinearEquivMap
  have hperfect : commutator SL(2, ℂ) = ⊤ :=
    Matrix.SL2.commutator_eq_top (a := (2 : ℂ)) (by norm_num) (by norm_num)
  have hmem : X ∈ commutator SL(2, ℂ) := by
    rw [hperfect]
    exact Subgroup.mem_top X
  have hdetCharacter : detCharacter X = 1 :=
    MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker detCharacter hmem)
  rw [spinorMatrix, LinearMap.det_toMatrix']
  have hval := congrArg Units.val hdetCharacter
  simpa [detCharacter, spinorLinearEquivMap] using hval

/-- The two matrices `X` and `-X` have the same Hermitian congruence action,
as observed after Wolf, Equation (2.42). This is not the converse assertion
that these are the only two points in every fibre. -/
@[simp] theorem spinorMatrix_neg (X : SL(2, ℂ)) :
    spinorMatrix (-X) = spinorMatrix X := by
  ext i j
  simp [spinorMatrix_apply, Matrix.SpecialLinearGroup.coe_neg]

/-- Metric preservation in the row-action convention printed in Wolf,
Equation (2.42): `L η Lᵀ = η`. -/
theorem spinorMatrix_mul_metric_mul_transpose (X : SL(2, ℂ)) :
    spinorMatrix X * minkowskiMetric * (spinorMatrix X)ᵀ = minkowskiMetric := by
  let A := spinorMatrix X
  let B := spinorMatrix X⁻¹
  have hAB : A * B = 1 := by
    change spinorMatrix X * spinorMatrix X⁻¹ = 1
    rw [← spinorMatrix_mul]
    simp
  have hmetric : Aᵀ * minkowskiMetric * A = minkowskiMetric :=
    spinorMatrix_transpose_mul_metric_mul X
  have htranspose_metric : Aᵀ * minkowskiMetric = minkowskiMetric * B := by
    calc
      Aᵀ * minkowskiMetric = (Aᵀ * minkowskiMetric) * 1 := by rw [Matrix.mul_one]
      _ = (Aᵀ * minkowskiMetric) * (A * B) := by rw [hAB]
      _ = (Aᵀ * minkowskiMetric * A) * B := by
        simp only [Matrix.mul_assoc]
      _ = minkowskiMetric * B := by rw [hmetric]
  have htranspose : Aᵀ = minkowskiMetric * B * minkowskiMetric := by
    calc
      Aᵀ = Aᵀ * 1 := by rw [Matrix.mul_one]
      _ = Aᵀ * (minkowskiMetric * minkowskiMetric) := by
        rw [minkowskiMetric_mul_self]
      _ = (Aᵀ * minkowskiMetric) * minkowskiMetric := by
        simp only [Matrix.mul_assoc]
      _ = minkowskiMetric * B * minkowskiMetric := by rw [htranspose_metric]
  change A * minkowskiMetric * Aᵀ = minkowskiMetric
  rw [htranspose]
  calc
    A * minkowskiMetric * (minkowskiMetric * B * minkowskiMetric) =
        A * (minkowskiMetric * minkowskiMetric) * B * minkowskiMetric := by
      simp only [Matrix.mul_assoc]
    _ = A * B * minkowskiMetric := by rw [minkowskiMetric_mul_self, Matrix.mul_one]
    _ = minkowskiMetric := by rw [hAB, Matrix.one_mul]

/-- The three defining conditions of the special orthochronous Lorentz group
printed in Wolf, Equation (2.42). -/
def IsSpecialOrthochronousLorentz (L : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  Matrix.det L = 1 ∧
    L * minkowskiMetric * Lᵀ = minkowskiMetric ∧
    0 < L 0 0

/-- Every matrix produced by Hermitian congruence with `X ∈ SL(2,ℂ)` lies in
the special orthochronous Lorentz group of Wolf, Equation (2.42). -/
theorem spinorMatrix_isSpecialOrthochronousLorentz (X : SL(2, ℂ)) :
    IsSpecialOrthochronousLorentz (spinorMatrix X) :=
  ⟨spinorMatrix_det X, spinorMatrix_mul_metric_mul_transpose X,
    spinorMatrix_zero_zero_pos X⟩

/-! ### The filtered Pauli transfer matrix -/

private abbrev QubitMap :=
  Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ

/-- The Pauli-basis transfer matrix `T̂` used in Wolf, Equation (2.43). -/
noncomputable def pauliTransferMatrix (T : QubitMap) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j ↦ pauliTransferEntry T i j

/-- The complex scalar extension of the real spinor matrix. -/
def spinorMatrixComplex (X : SL(2, ℂ)) : Matrix (Fin 4) (Fin 4) ℂ :=
  (spinorMatrix X).map Complex.ofReal

/-- The real part of the Pauli transfer matrix. For a
Hermiticity-preserving map this is the transfer matrix itself, regarded over
`ℝ`. -/
noncomputable def pauliTransferMatrixReal (T : QubitMap) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j ↦ (pauliTransferEntry T i j).re

/-- The four-Pauli expansion of an arbitrary complex qubit matrix. -/
theorem pauli_expansion_four (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = ∑ i : Fin 4,
      (Matrix.trace (pauliMatrices i * M) / 2) • pauliMatrices i := by
  rw [Fin.sum_univ_succ]
  simp only [pauliMatrices_zero, Matrix.one_mul, pauliMatrices_succ]
  simpa [div_eq_mul_inv] using SpinCover.pauli_expansion M

/-- Complex coercion of the real spinor entry, without the redundant real
part in the trace formula. -/
theorem coe_spinorMatrix_apply (X : SL(2, ℂ)) (i j : Fin 4) :
    (spinorMatrix X i j : ℂ) =
      Matrix.trace (pauliMatrices i *
        (X.1 * pauliMatrices j * X.1ᴴ)) / 2 := by
  rw [spinorMatrix_apply, Complex.ofReal_div]
  rw [trace_mul_eq_ofReal_re_of_isHermitian (pauliMatrices_isHermitian i)
    (Matrix.isHermitian_mul_mul_conjTranspose X.1
      (pauliMatrices_isHermitian j))]
  norm_num

/-- Congruence of a single Pauli matrix expands in the Pauli basis with the
corresponding column of the spinor matrix. -/
theorem sl2Congruence_pauli (X : SL(2, ℂ)) (j : Fin 4) :
    X.1 * pauliMatrices j * X.1ᴴ =
      ∑ i : Fin 4, (spinorMatrix X i j : ℂ) • pauliMatrices i := by
  rw [← pauliMatrixOfMinkowski_single,
    ← pauliMatrixOfMinkowski_spinorMatrix_mulVec X (Pi.single j 1),
    pauliMatrixOfMinkowski]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Left filtering acts on a Pauli transfer entry by the corresponding row
of the spinor matrix. This is the left bounded slice of Wolf,
Equation (2.43). -/
theorem pauliTransferEntry_unitaryConj_comp
    (X : SL(2, ℂ)) (T : QubitMap) (i j : Fin 4) :
    pauliTransferEntry ((unitaryConjLM X.1).comp T) i j =
      ∑ k : Fin 4,
        (spinorMatrix X i k : ℂ) * pauliTransferEntry T k j := by
  rw [pauliTransferEntry, LinearMap.comp_apply, unitaryConjLM_apply,
    pauli_expansion_four (T (pauliMatrices j))]
  simp only [Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coe_spinorMatrix_apply]
  simp only [pauliTransferEntry]
  ring

/-- Right filtering acts on a Pauli transfer entry by the corresponding
column of the spinor matrix. This is the right bounded slice of Wolf,
Equation (2.43). -/
theorem pauliTransferEntry_comp_unitaryConj
    (T : QubitMap) (X : SL(2, ℂ)) (i j : Fin 4) :
    pauliTransferEntry (T.comp (unitaryConjLM X.1)) i j =
      ∑ k : Fin 4,
        pauliTransferEntry T i k * (spinorMatrix X k j : ℂ) := by
  rw [pauliTransferEntry, LinearMap.comp_apply, unitaryConjLM_apply,
    sl2Congruence_pauli]
  simp only [map_sum, LinearMap.map_smul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [pauliTransferEntry]
  ring

/-- Matrix form of the left bounded slice of Wolf, Equation (2.43). -/
theorem pauliTransferMatrix_unitaryConj_comp (X : SL(2, ℂ)) (T : QubitMap) :
    pauliTransferMatrix ((unitaryConjLM X.1).comp T) =
      spinorMatrixComplex X * pauliTransferMatrix T := by
  ext i j
  simpa [pauliTransferMatrix, spinorMatrixComplex, Matrix.mul_apply] using
    pauliTransferEntry_unitaryConj_comp X T i j

/-- Matrix form of the right bounded slice of Wolf, Equation (2.43). -/
theorem pauliTransferMatrix_comp_unitaryConj (T : QubitMap) (X : SL(2, ℂ)) :
    pauliTransferMatrix (T.comp (unitaryConjLM X.1)) =
      pauliTransferMatrix T * spinorMatrixComplex X := by
  ext i j
  simpa [pauliTransferMatrix, spinorMatrixComplex, Matrix.mul_apply] using
    pauliTransferEntry_comp_unitaryConj T X i j

/-- Exact Pauli-transfer action of pre- and postfiltering:
`T̂ ↦ L₂ T̂ L₁`, Wolf, Equation (2.43). -/
theorem pauliTransferMatrix_two_sided_filtering
    (X₂ : SL(2, ℂ)) (T : QubitMap) (X₁ : SL(2, ℂ)) :
    pauliTransferMatrix
        ((unitaryConjLM X₂.1).comp (T.comp (unitaryConjLM X₁.1))) =
      spinorMatrixComplex X₂ * pauliTransferMatrix T * spinorMatrixComplex X₁ := by
  calc
    pauliTransferMatrix
        ((unitaryConjLM X₂.1).comp (T.comp (unitaryConjLM X₁.1))) =
        spinorMatrixComplex X₂ *
          pauliTransferMatrix (T.comp (unitaryConjLM X₁.1)) :=
      pauliTransferMatrix_unitaryConj_comp X₂ _
    _ = spinorMatrixComplex X₂ *
        (pauliTransferMatrix T * spinorMatrixComplex X₁) := by
      rw [pauliTransferMatrix_comp_unitaryConj]
    _ = spinorMatrixComplex X₂ * pauliTransferMatrix T *
        spinorMatrixComplex X₁ := Matrix.mul_assoc _ _ _ |>.symm

/-- A Hermiticity-preserving map has real Pauli transfer entries. -/
theorem coe_pauliTransferMatrixReal_of_preservesHermiticity
    (T : QubitMap)
    (hT : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      M.IsHermitian → (T M).IsHermitian)
    (i j : Fin 4) :
    (pauliTransferMatrixReal T i j : ℂ) = pauliTransferMatrix T i j := by
  simp only [pauliTransferMatrixReal, pauliTransferMatrix, pauliTransferEntry]
  rw [← trace_mul_eq_ofReal_re_of_isHermitian (pauliMatrices_isHermitian i)
    (hT (pauliMatrices j) (pauliMatrices_isHermitian j))]
  norm_num

/-- Real form of the exact two-sided filtering action in Wolf,
Equation (2.43). -/
theorem pauliTransferMatrixReal_two_sided_filtering
    (X₂ : SL(2, ℂ)) (T : QubitMap) (X₁ : SL(2, ℂ)) :
    pauliTransferMatrixReal
        ((unitaryConjLM X₂.1).comp (T.comp (unitaryConjLM X₁.1))) =
      spinorMatrix X₂ * pauliTransferMatrixReal T * spinorMatrix X₁ := by
  ext i j
  have h := congrArg (fun M ↦ (M i j).re)
    (pauliTransferMatrix_two_sided_filtering X₂ T X₁)
  simpa [pauliTransferMatrixReal, pauliTransferMatrix, spinorMatrixComplex,
    Matrix.mul_apply, Complex.mul_re] using h

/-- The `SL(2,ℂ)` matrix bundled by an `SLFiltering 2`. -/
def SLFiltering.toSL2 (Phi : SLFiltering 2) : SL(2, ℂ) :=
  ⟨Phi.S, Phi.det_eq_one⟩

/-- Equation (2.43) for the filtering structures used by the Lorentz normal
form development, in Wolf's order `Phi₂ ∘ T ∘ Phi₁`. -/
theorem pauliTransferMatrixReal_slFiltering
    (Phi₂ : SLFiltering 2) (T : QubitMap) (Phi₁ : SLFiltering 2) :
    pauliTransferMatrixReal (Phi₂.map.comp (T.comp Phi₁.map)) =
      spinorMatrix Phi₂.toSL2 * pauliTransferMatrixReal T *
        spinorMatrix Phi₁.toSL2 := by
  rw [Phi₂.map_eq, Phi₁.map_eq]
  exact pauliTransferMatrixReal_two_sided_filtering Phi₂.toSL2 T Phi₁.toSL2

/-- The spinor matrices form a monoid homomorphism. -/
noncomputable def spinorMap : SL(2, ℂ) →* Matrix (Fin 4) (Fin 4) ℝ where
  toFun := spinorMatrix
  map_one' := spinorMatrix_one
  map_mul' := spinorMatrix_mul

/-!
The inclusion of the spinor image in `SO⁺(1,3)` is now formalized. Wolf's
stronger assertion that this map is a surjective double cover, and the explicit
rotation/boost exponential formulas in Equation (2.44), are not inferred from
the three-dimensional `SU(2)` result and are not asserted in this module.
-/

end Wolf
