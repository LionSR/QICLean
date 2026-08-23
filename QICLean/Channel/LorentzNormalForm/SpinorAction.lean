/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.SpinCover.Basic
import QICLean.Channel.LorentzNormalForm.QubitNormalForm
import Mathlib.Algebra.Star.Module
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

/-- The spinor matrices form a monoid homomorphism. -/
noncomputable def spinorMap : SL(2, ℂ) →* Matrix (Fin 4) (Fin 4) ℝ where
  toFun := spinorMatrix
  map_one' := spinorMatrix_one
  map_mul' := spinorMatrix_mul

end Wolf
