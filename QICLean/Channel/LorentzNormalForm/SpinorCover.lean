/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.SpinCover.EulerAngles
import QICLean.Channel.LorentzNormalForm.SpinorAction

/-!
# The spinor epimorphism `SL(2,ℂ) → SO⁺(1,3)`

This module completes the group-theoretic part of Wolf's spinor discussion
(Equations (2.42)--(2.44)): the spinor map of
`QICLean.Channel.LorentzNormalForm.SpinorAction` is shown to be a
homomorphism *onto* the special orthochronous Lorentz group `SO⁺(1,3)`, with
exactly the two-point fibres `{X, -X}` proved in
`Wolf.spinorMatrix_eq_iff_eq_or_eq_neg`.

Following Wolf's rotation--boost discussion, surjectivity is proved without
assuming a preimage: for `L ∈ SO⁺(1,3)` with first column `u`, the canonical
boost `B_u` with `B_u e₀ = u` reduces `L` to a rotation block `1 ⊕ R` fixing
the time axis, the rotation `R ∈ SO(3)` lifts through the Euler-angle cover
`SU(2) → SO(3)` of `QICLean.Algebra.SpinCover.EulerAngles`, and the boost is
lifted by an explicit positive determinant-one matrix `P_u` with
`P_u² = u·σ`.  The product `S = P_u U` then realizes `L` and simultaneously
gives the polar (Cartan) decomposition described by Wolf.

## Main results

* `Wolf.specialOrthochronousLorentzGroup` : `SO⁺(1,3)` as a matrix group
* `Wolf.spinorCoverHom` : the bundled homomorphism `SL(2,ℂ) →* SO⁺(1,3)`
* `Wolf.exists_so3_block_of_fixes_time` : a Lorentz matrix fixing `e₀` is a
  rotation block `1 ⊕ R` with `R ∈ SO(3)`
* `Wolf.spinorMatrix_su2ToSL2` : the rotation lift, `1 ⊕ R(U)` for
  `U ∈ SU(2)`
* `Wolf.boostSpinor` : the boost spinor `P = (M(u) + I)/√(2(1+u₀))`
* `Wolf.boostSpinor_posDef` : the canonical boost spinor satisfies `P > 0`
* `Wolf.spinorMatrix_boostSpinorSL2` : the boost lift,
  `spinorMatrix P_u = B_u`
* `Wolf.exists_sl2_spinorMatrix_eq` : the spinor epimorphism; every
  `L ∈ SO⁺(1,3)` is `spinorMatrix X` for some `X ∈ SL(2,ℂ)`
* `Wolf.spinorCoverHom_surjective` : the bundled epimorphism
* `Wolf.spinorCoverHom_eq_iff_eq_or_eq_neg` : the two-point fibres
* `Wolf.spinorCoverHom_eq_one_iff` : the kernel is `{1, -1}`

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Equations
  (2.42)--(2.44)]
* `Notes/WolfNoteTexSource/ch02_representations.tex`, lines 1037--1081
-/

open scoped Matrix MatrixGroups BigOperators ComplexOrder
open Matrix Finset

noncomputable section

namespace Wolf

/-! ### The special orthochronous Lorentz group `SO⁺(1,3)` -/


@[simp] theorem minkowskiMetric_transpose : minkowskiMetricᵀ = minkowskiMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem IsSpecialOrthochronousLorentz.transpose_mul_metric_mul
    {L : Matrix (Fin 4) (Fin 4) ℝ} (h : IsSpecialOrthochronousLorentz L) :
    Lᵀ * minkowskiMetric * L = minkowskiMetric := by
  obtain ⟨hdet, hlorentz, -⟩ := h
  have hdetunit : IsUnit L.det := by rw [hdet]; exact isUnit_one
  have hinv : L * (minkowskiMetric * Lᵀ * minkowskiMetric) = 1 := by
    calc L * (minkowskiMetric * Lᵀ * minkowskiMetric)
        = (L * minkowskiMetric * Lᵀ) * minkowskiMetric := by simp only [Matrix.mul_assoc]
      _ = minkowskiMetric * minkowskiMetric := by rw [hlorentz]
      _ = 1 := minkowskiMetric_mul_self
  have hLinv : L⁻¹ = minkowskiMetric * Lᵀ * minkowskiMetric := Matrix.inv_eq_right_inv hinv
  have hT : Lᵀ = minkowskiMetric * L⁻¹ * minkowskiMetric := by
    have e : minkowskiMetric * (minkowskiMetric * Lᵀ * minkowskiMetric) * minkowskiMetric
        = Lᵀ := by
      calc minkowskiMetric * (minkowskiMetric * Lᵀ * minkowskiMetric) * minkowskiMetric
          = (minkowskiMetric * minkowskiMetric) * Lᵀ * (minkowskiMetric * minkowskiMetric) := by
            noncomm_ring
        _ = Lᵀ := by rw [minkowskiMetric_mul_self, Matrix.one_mul, Matrix.mul_one]
    rw [← hLinv] at e
    exact e.symm
  calc Lᵀ * minkowskiMetric * L
      = (minkowskiMetric * L⁻¹ * minkowskiMetric) * minkowskiMetric * L := by rw [hT]
    _ = minkowskiMetric * L⁻¹ * (minkowskiMetric * minkowskiMetric) * L := by
        simp only [Matrix.mul_assoc]
    _ = minkowskiMetric * (L⁻¹ * L) := by
        rw [minkowskiMetric_mul_self, Matrix.mul_one, Matrix.mul_assoc]
    _ = minkowskiMetric := by rw [Matrix.nonsing_inv_mul L hdetunit, Matrix.mul_one]

theorem IsSpecialOrthochronousLorentz.inv {L : Matrix (Fin 4) (Fin 4) ℝ}
    (h : IsSpecialOrthochronousLorentz L) : IsSpecialOrthochronousLorentz L⁻¹ := by
  obtain ⟨hdet, hlorentz, h00⟩ := h
  have hdetunit : IsUnit L.det := by rw [hdet]; exact isUnit_one
  have hinv : L * (minkowskiMetric * Lᵀ * minkowskiMetric) = 1 := by
    calc L * (minkowskiMetric * Lᵀ * minkowskiMetric)
        = (L * minkowskiMetric * Lᵀ) * minkowskiMetric := by simp only [Matrix.mul_assoc]
      _ = minkowskiMetric * minkowskiMetric := by rw [hlorentz]
      _ = 1 := minkowskiMetric_mul_self
  have hLinv : L⁻¹ = minkowskiMetric * Lᵀ * minkowskiMetric := Matrix.inv_eq_right_inv hinv
  have hcancelt : ∀ M : Matrix (Fin 4) (Fin 4) ℝ,
      L⁻¹ * (L * M * Lᵀ) * (L⁻¹)ᵀ = M := by
    intro M
    calc L⁻¹ * (L * M * Lᵀ) * (L⁻¹)ᵀ
        = (L⁻¹ * L) * M * (Lᵀ * (L⁻¹)ᵀ) := by noncomm_ring
      _ = M := by
          rw [Matrix.nonsing_inv_mul L hdetunit, Matrix.one_mul,
            ← Matrix.transpose_mul, Matrix.nonsing_inv_mul L hdetunit,
            Matrix.transpose_one, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · have hdetinv := Matrix.det_nonsing_inv_mul_det L hdetunit
    rw [hdet, mul_one] at hdetinv
    exact hdetinv
  · have h1 : L * (L⁻¹ * minkowskiMetric * (L⁻¹)ᵀ) * Lᵀ = L * minkowskiMetric * Lᵀ := by
      calc L * (L⁻¹ * minkowskiMetric * (L⁻¹)ᵀ) * Lᵀ
          = (L * L⁻¹) * minkowskiMetric * ((L⁻¹)ᵀ * Lᵀ) := by noncomm_ring
        _ = minkowskiMetric := by
            rw [Matrix.mul_nonsing_inv L hdetunit, Matrix.one_mul,
              ← Matrix.transpose_mul, Matrix.mul_nonsing_inv L hdetunit,
              Matrix.transpose_one, Matrix.mul_one]
        _ = L * minkowskiMetric * Lᵀ := hlorentz.symm
    have h2 := congrArg (fun M ↦ L⁻¹ * M * (L⁻¹)ᵀ) h1
    rw [hcancelt, hcancelt] at h2
    exact h2
  · rw [hLinv]
    simp only [minkowskiMetric, Fin.isValue, Matrix.mul_apply, Matrix.diagonal_apply,
      reduceIte, Matrix.transpose_apply, ite_mul, one_mul, zero_mul, sum_ite_eq,
      mem_univ, mul_ite, mul_one, mul_neg, mul_zero, sum_ite_eq']
    exact h00

/-- The time-row Minkowski norm identity from `L η Lᵀ = η`. -/
theorem row_norm_of_lorentz {L : Matrix (Fin 4) (Fin 4) ℝ}
    (h : L * minkowskiMetric * Lᵀ = minkowskiMetric) :
    L 0 0 ^ 2 - ∑ k : Fin 3, L 0 k.succ ^ 2 = 1 := by
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMetric,
    Matrix.diagonal_apply, Fin.sum_univ_four] at h00
  rw [Fin.sum_univ_three]
  change L 0 0 ^ 2 - (L 0 1 ^ 2 + L 0 2 ^ 2 + L 0 3 ^ 2) = 1
  linarith [h00]

/-- The time-column Minkowski norm identity from `Lᵀ η L = η`. -/
theorem col_norm_of_lorentz {L : Matrix (Fin 4) (Fin 4) ℝ}
    (h : Lᵀ * minkowskiMetric * L = minkowskiMetric) :
    L 0 0 ^ 2 - ∑ k : Fin 3, L k.succ 0 ^ 2 = 1 := by
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMetric,
    Matrix.diagonal_apply, Fin.sum_univ_four] at h00
  rw [Fin.sum_univ_three]
  change L 0 0 ^ 2 - (L 1 0 ^ 2 + L 2 0 ^ 2 + L 3 0 ^ 2) = 1
  linarith [h00]

theorem IsSpecialOrthochronousLorentz.mul {A B : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : IsSpecialOrthochronousLorentz A) (hB : IsSpecialOrthochronousLorentz B) :
    IsSpecialOrthochronousLorentz (A * B) := by
  obtain ⟨hdetA, hlorA, h00A⟩ := hA
  obtain ⟨hdetB, hlorB, h00B⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_mul, hdetA, hdetB, mul_one]
  · calc (A * B) * minkowskiMetric * (A * B)ᵀ
        = A * (B * minkowskiMetric * Bᵀ) * Aᵀ := by
          rw [Matrix.transpose_mul]; noncomm_ring
      _ = A * minkowskiMetric * Aᵀ := by rw [hlorB]
      _ = minkowskiMetric := hlorA
  · have hrowA := row_norm_of_lorentz hlorA
    have hcolB := col_norm_of_lorentz
      (IsSpecialOrthochronousLorentz.transpose_mul_metric_mul ⟨hdetB, hlorB, h00B⟩)
    have hSA : 0 ≤ ∑ k : Fin 3, A 0 k.succ ^ 2 :=
      Finset.sum_nonneg (fun k _ ↦ sq_nonneg (A 0 k.succ : ℝ))
    have hSB : 0 ≤ ∑ k : Fin 3, B k.succ 0 ^ 2 :=
      Finset.sum_nonneg (fun k _ ↦ sq_nonneg (B k.succ 0 : ℝ))
    have hA0 : 1 ≤ A 0 0 := by
      have hsq : (1 : ℝ) ^ 2 ≤ A 0 0 ^ 2 := by linarith [hrowA, hSA]
      exact le_of_sq_le_sq hsq h00A.le
    have hB0 : 1 ≤ B 0 0 := by
      have hsq : (1 : ℝ) ^ 2 ≤ B 0 0 ^ 2 := by linarith [hcolB, hSB]
      exact le_of_sq_le_sq hsq h00B.le
    have hsum : (A * B) 0 0 =
        A 0 0 * B 0 0 + ∑ k : Fin 3, A 0 k.succ * B k.succ 0 := by
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
    rw [hsum]
    have hcs : (∑ k : Fin 3, A 0 k.succ * B k.succ 0) ^ 2 ≤
        (∑ k : Fin 3, A 0 k.succ ^ 2) * (∑ k : Fin 3, B k.succ 0 ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hkey : (∑ k : Fin 3, A 0 k.succ ^ 2) * (∑ k : Fin 3, B k.succ 0 ^ 2) <
        (A 0 0 * B 0 0) ^ 2 := by
      have e1 : ∑ k : Fin 3, A 0 k.succ ^ 2 = A 0 0 ^ 2 - 1 := by linarith [hrowA]
      have e2 : ∑ k : Fin 3, B k.succ 0 ^ 2 = B 0 0 ^ 2 - 1 := by linarith [hcolB]
      rw [e1, e2]
      nlinarith [hA0, hB0]
    have habs : |∑ k : Fin 3, A 0 k.succ * B k.succ 0| < A 0 0 * B 0 0 := by
      have h1 : (∑ k : Fin 3, A 0 k.succ * B k.succ 0) ^ 2 < (A 0 0 * B 0 0) ^ 2 :=
        lt_of_le_of_lt hcs hkey
      have h2 := (sq_lt_sq).mp h1
      rwa [abs_of_nonneg (by positivity : 0 ≤ A 0 0 * B 0 0)] at h2
    have hle := neg_abs_le (∑ k : Fin 3, A 0 k.succ * B k.succ 0)
    linarith

/-- The identity is special orthochronous Lorentz. -/
theorem isSpecialOrthochronousLorentz_one :
    IsSpecialOrthochronousLorentz (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Matrix.det_one
  · rw [Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
  · norm_num [Matrix.one_apply_eq]

/-- The special orthochronous Lorentz group `SO⁺(1,3)` of Wolf,
Equation (2.42), as a submonoid of real `4×4` matrices.  Membership of `L`
in this submonoid is definitionally `IsSpecialOrthochronousLorentz L`. -/
def specialOrthochronousLorentzGroup : Submonoid (Matrix (Fin 4) (Fin 4) ℝ) where
  carrier := {L | IsSpecialOrthochronousLorentz L}
  one_mem' := isSpecialOrthochronousLorentz_one
  mul_mem' := IsSpecialOrthochronousLorentz.mul

theorem mem_specialOrthochronousLorentzGroup_iff {L : Matrix (Fin 4) (Fin 4) ℝ} :
    L ∈ specialOrthochronousLorentzGroup ↔ IsSpecialOrthochronousLorentz L :=
  Iff.rfl

instance : Group specialOrthochronousLorentzGroup where
  inv := fun L ↦ ⟨L.1⁻¹, L.2.inv⟩
  inv_mul_cancel L := Subtype.ext (Matrix.nonsing_inv_mul L.1 (by
    rw [L.2.1]; exact isUnit_one))

/-- The spinor map as a bundled homomorphism from `SL(2,ℂ)` onto the special
orthochronous Lorentz group `SO⁺(1,3)` of Wolf, Equation (2.42). -/
noncomputable def spinorCoverHom : SL(2, ℂ) →* specialOrthochronousLorentzGroup where
  toFun X := ⟨spinorMatrix X, spinorMatrix_isSpecialOrthochronousLorentz X⟩
  map_one' := Subtype.ext spinorMatrix_one
  map_mul' X Y := Subtype.ext (spinorMatrix_mul X Y)


/-! ### The rotation block `1 ⊕ R` -/


/-- The Lorentz matrix `1 ⊕ R` fixing the time axis. -/
def lorentzRotationBlock (R : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (Fin.cons (Pi.single 0 1) (fun i ↦ Fin.cons 0 (R i)))

@[simp] theorem lorentzRotationBlock_zero_zero (R : Matrix (Fin 3) (Fin 3) ℝ) :
    lorentzRotationBlock R 0 0 = 1 := by
  simp [lorentzRotationBlock, Matrix.of_apply, Fin.cons_zero]

@[simp] theorem lorentzRotationBlock_zero_succ (R : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    lorentzRotationBlock R 0 j.succ = 0 := by
  simp [lorentzRotationBlock, Matrix.of_apply, Fin.cons_zero, Pi.single_eq_of_ne]

@[simp] theorem lorentzRotationBlock_succ_zero (R : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    lorentzRotationBlock R i.succ 0 = 0 := by
  simp [lorentzRotationBlock, Matrix.of_apply, Fin.cons_succ, Fin.cons_zero]

@[simp] theorem lorentzRotationBlock_succ_succ (R : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    lorentzRotationBlock R i.succ j.succ = R i j := by
  simp [lorentzRotationBlock, Matrix.of_apply, Fin.cons_succ]

@[simp] theorem lorentzRotationBlock_one :
    lorentzRotationBlock (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext i j
  rw [Matrix.one_apply]
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [Matrix.one_apply, (Ne.symm (Fin.succ_ne_zero _))]

theorem lorentzRotationBlock_mul (R S : Matrix (Fin 3) (Fin 3) ℝ) :
    lorentzRotationBlock (R * S) = lorentzRotationBlock R * lorentzRotationBlock S := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem lorentzRotationBlock_mulVec_single_zero (R : Matrix (Fin 3) (Fin 3) ℝ) :
    lorentzRotationBlock R *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  ext i
  cases i using Fin.cases <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

@[simp] theorem lorentzRotationBlock_det (R : Matrix (Fin 3) (Fin 3) ℝ) :
    (lorentzRotationBlock R).det = R.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [lorentzRotationBlock_zero_succ, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, lorentzRotationBlock_zero_zero, mul_one, Fin.val_zero, pow_zero, one_mul]
  apply congrArg Matrix.det
  ext i j
  rw [Matrix.submatrix_apply, Fin.succAbove_zero]
  exact lorentzRotationBlock_succ_succ R i j

/-- The `(0, j)` entry of `LᵀηL` when the first column of `L` is `e₀`. -/
theorem transpose_mul_metric_mul_apply_zero {L : Matrix (Fin 4) (Fin 4) ℝ}
    (hcol : L.col 0 = Pi.single (0 : Fin 4) (1 : ℝ)) (j : Fin 4) :
    (Lᵀ * minkowskiMetric * L) 0 j = L 0 j := by
  have h0 : L 0 0 = 1 := by
    have h := congrFun hcol 0
    rwa [Matrix.col_apply, Pi.single_eq_same] at h
  have h1 : L 1 0 = 0 := by
    have h := congrFun hcol 1
    rwa [Matrix.col_apply, Pi.single_eq_of_ne (by decide)] at h
  have h2 : L 2 0 = 0 := by
    have h := congrFun hcol 2
    rwa [Matrix.col_apply, Pi.single_eq_of_ne (by decide)] at h
  have h3 : L 3 0 = 0 := by
    have h := congrFun hcol 3
    rwa [Matrix.col_apply, Pi.single_eq_of_ne (by decide)] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMetric,
    Matrix.diagonal_apply, Fin.sum_univ_four]
  rw [h0, h1, h2, h3]
  simp

/-- The `(i, j)` entry of `LᵀηL` as the Minkowski-weighted column inner
product. -/
theorem transpose_mul_metric_mul_apply {L : Matrix (Fin 4) (Fin 4) ℝ} (i j : Fin 4) :
    (Lᵀ * minkowskiMetric * L) i j =
      L 0 i * L 0 j - (L 1 i * L 1 j + L 2 i * L 2 j + L 3 i * L 3 j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMetric,
    Matrix.diagonal_apply, Fin.sum_univ_four]
  simp
  ring

/-- A Lorentz matrix fixing `e₀` is `1 ⊕ R` with `R ∈ SO(3)`.  This is the
block-diagonalization step of the boost-rotation decomposition after Wolf,
Equation (2.44). -/
theorem exists_so3_block_of_fixes_time {L : Matrix (Fin 4) (Fin 4) ℝ}
    (hfix : L *ᵥ Pi.single 0 1 = Pi.single 0 1)
    (hlorentz : Lᵀ * minkowskiMetric * L = minkowskiMetric) (hdet : L.det = 1) :
    ∃ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, L = lorentzRotationBlock R := by
  have hcol : L.col 0 = Pi.single (0 : Fin 4) (1 : ℝ) := by
    rw [← Matrix.mulVec_single_one L 0]; exact hfix
  have hrow : L.row 0 = Pi.single (0 : Fin 4) (1 : ℝ) := by
    ext j
    have h := congrFun (congrFun hlorentz 0) j
    rw [transpose_mul_metric_mul_apply_zero hcol j] at h
    rw [Matrix.row_apply, h]
    cases j using Fin.cases with
    | zero => simp [minkowskiMetric]
    | succ j => simp [minkowskiMetric, (Ne.symm (Fin.succ_ne_zero _))]
  have h00 : L 0 0 = 1 := by
    have h := congrFun hcol 0
    rwa [Matrix.col_apply, Pi.single_eq_same] at h
  have hcs : ∀ i : Fin 3, L i.succ 0 = 0 := by
    intro i
    have h := congrFun hcol i.succ
    rwa [Matrix.col_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i)] at h
  have hrs : ∀ j : Fin 3, L 0 j.succ = 0 := by
    intro j
    have h := congrFun hrow j.succ
    rwa [Matrix.row_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero j)] at h
  refine ⟨L.submatrix Fin.succ Fin.succ, ?_, ?_⟩
  · rw [Matrix.mem_specialOrthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_orthogonalGroup_iff']
      ext i j
      have h := congrFun (congrFun hlorentz i.succ) j.succ
      rw [transpose_mul_metric_mul_apply] at h
      rw [hrs i, zero_mul, zero_sub] at h
      have hη : minkowskiMetric i.succ j.succ = if i = j then -1 else 0 := by
        simp [minkowskiMetric, Matrix.diagonal_apply, Fin.succ_inj]
      rw [hη] at h
      have hR : ((L.submatrix Fin.succ Fin.succ)ᵀ * L.submatrix Fin.succ Fin.succ) i j =
          L 1 i.succ * L 1 j.succ + L 2 i.succ * L 2 j.succ + L 3 i.succ * L 3 j.succ := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
          Matrix.submatrix_apply]
        change L 1 i.succ * L 1 j.succ + L 2 i.succ * L 2 j.succ + L 3 i.succ * L 3 j.succ =
          L 1 i.succ * L 1 j.succ + L 2 i.succ * L 2 j.succ + L 3 i.succ * L 3 j.succ
        rfl
      rw [Matrix.one_apply, hR]
      by_cases hij : i = j
      · simp only [hij, ite_true] at h ⊢
        linarith [h]
      · simp only [hij, ite_false] at h ⊢
        linarith [h]
    · have hL : L = lorentzRotationBlock (L.submatrix Fin.succ Fin.succ) := by
        ext i j
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => rw [lorentzRotationBlock_zero_zero]; exact h00
            | succ j => rw [lorentzRotationBlock_zero_succ]; exact hrs j
        | succ i =>
            cases j using Fin.cases with
            | zero => rw [lorentzRotationBlock_succ_zero]; exact hcs i
            | succ j => rfl
      rw [← lorentzRotationBlock_det, ← hL, hdet]
  · ext i j
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => rw [lorentzRotationBlock_zero_zero]; exact h00
        | succ j => rw [lorentzRotationBlock_zero_succ]; exact hrs j
    | succ i =>
        cases j using Fin.cases with
        | zero => rw [lorentzRotationBlock_succ_zero]; exact hcs i
        | succ j => rfl


/-! ### The unitary lift through the Euler-angle cover -/
/-- A special unitary matrix regarded as an element of `SL(2,ℂ)`. -/
def su2ToSL2 (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) : SL(2, ℂ) :=
  ⟨U, (Matrix.mem_specialUnitaryGroup_iff.mp hU).2⟩

@[simp] theorem su2ToSL2_coe (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (su2ToSL2 U hU).1 = U := rfl

/-- The spinor matrix entries of a special unitary, in terms of `U` itself. -/
theorem spinorMatrix_su2ToSL2_apply (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 4) :
    spinorMatrix (su2ToSL2 U hU) i j =
      (Matrix.trace (pauliMatrices i * (U * pauliMatrices j * Uᴴ))).re / 2 :=
  spinorMatrix_apply _ _ _

/-- For a special unitary `U`, conjugation uses the conjugate transpose, and
the spinor matrix of `U` is the rotation block `1 ⊕ R(U)`.  This is the
rotation lift of Wolf, Equation (2.44). -/
theorem spinorMatrix_su2ToSL2 (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    spinorMatrix (su2ToSL2 U hU) =
      lorentzRotationBlock (SpinCover.pauliConjAdReal U hU) := by
  have hUunit : U ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp hU).1
  have hUsU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hUunit
  have hsUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hUunit
  have hconj_adj : Uᴴ = U.adjugate := by
    have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv hUsU
    rw [← hinv, Matrix.inv_def, (Matrix.mem_specialUnitaryGroup_iff.mp hU).2]
    simp
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      rw [lorentzRotationBlock_zero_zero, spinorMatrix_su2ToSL2_apply]
      simp only [pauliMatrices_zero, Matrix.mul_one, Matrix.one_mul]
      rw [hUsU]
      simp [Matrix.trace_one]
    | succ j =>
      rw [lorentzRotationBlock_zero_succ, spinorMatrix_su2ToSL2_apply]
      simp only [pauliMatrices_zero, Matrix.one_mul, pauliMatrices_succ]
      have htr : Matrix.trace (U * SpinCover.pauli j * Uᴴ) = 0 := by
        calc Matrix.trace (U * SpinCover.pauli j * Uᴴ)
            = Matrix.trace (Uᴴ * (U * SpinCover.pauli j)) :=
              Matrix.trace_mul_comm _ _
          _ = Matrix.trace ((Uᴴ * U) * SpinCover.pauli j) := by
              rw [Matrix.mul_assoc]
          _ = Matrix.trace (SpinCover.pauli j) := by rw [hsUU, Matrix.one_mul]
          _ = 0 := SpinCover.trace_pauli j
      rw [htr]
      simp
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      rw [lorentzRotationBlock_succ_zero, spinorMatrix_su2ToSL2_apply]
      simp only [pauliMatrices_zero, Matrix.mul_one, pauliMatrices_succ]
      rw [hUsU, Matrix.mul_one]
      rw [SpinCover.trace_pauli i]
      simp
    | succ j =>
      rw [lorentzRotationBlock_succ_succ, spinorMatrix_su2ToSL2_apply]
      simp only [pauliMatrices_succ]
      rw [SpinCover.pauliConjAdReal, SpinCover.pauliConjAd, SpinCover.su2ToGL_coe,
        SpinCover.su2ToGL_inv_coe, ← hconj_adj]
      have hre : ∀ z : ℂ, (z / 2).re = z.re / 2 := by
        intro z
        norm_num [Complex.div_re, Complex.normSq_ofReal]
      simp only [Matrix.mul_assoc, hre]

/-- Every rotation block `1 ⊕ R` with `R ∈ SO(3)` is the spinor matrix of a
special unitary: the rotation factor of Wolf, Equation (2.44) lifts through
the Euler-angle cover `SU(2) → SO(3)`. -/
theorem exists_su2_spinorMatrix_eq_lorentzRotationBlock (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℂ, ∃ hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      spinorMatrix (su2ToSL2 U hU) = lorentzRotationBlock R := by
  obtain ⟨U, hU, hUR⟩ := SpinCover.spinHalfCover_surjective_onto_SO3 R hR
  refine ⟨U, hU, ?_⟩
  rw [spinorMatrix_su2ToSL2]
  congr 1
  ext i j
  have h := congrFun (congrFun hUR i) j
  rw [Matrix.map_apply] at h
  change (SpinCover.pauliConjAd (SpinCover.su2ToGL U hU) i j).re = R i j
  rw [h]
  exact Complex.ofReal_re _

/-! ### The boost spinor -/


/-- The spatial dot product `u₁x₁ + u₂x₂ + u₃x₃`. -/
def spatialDot (u x : MinkowskiSpace) : ℝ :=
  ∑ l : Fin 3, u l.succ * x l.succ

/-- The spatial dot product in coordinates. -/
theorem spatialDot_eq (u x : MinkowskiSpace) :
    spatialDot u x = u 1 * x 1 + u 2 * x 2 + u 3 * x 3 := by
  rw [spatialDot, Fin.sum_univ_three, Fin.succ_zero_eq_one', Fin.succ_one_eq_two',
    show Fin.succ (2 : Fin 3) = 3 from rfl]

/-- The canonical proper orthochronous boost `B_u` with `B_u e₀ = u`,
for `u` on the unit hyperboloid `u₀² - u₁² - u₂² - u₃² = 1`, `u₀ > 0`.
Writing `v` for the spatial part of `u`, the block formula
`B = [[u₀, vᵀ], [v, I + vvᵀ/(1+u₀)]]` is uniform: for zero spatial part it
gives the identity, so no case split is needed (the equivalent coefficient
`(u₀-1)/|v|²` would need one). -/
def lorentzBoost (u : MinkowskiSpace) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (Fin.cons (fun j ↦ u j)
    (fun k ↦ Fin.cons (u k.succ)
      (fun l ↦ (if k = l then 1 else 0) + u k.succ * u l.succ / (1 + u 0))))

@[simp] theorem lorentzBoost_zero_zero (u : MinkowskiSpace) :
    lorentzBoost u 0 0 = u 0 := by
  simp [lorentzBoost, Matrix.of_apply, Fin.cons_zero]

@[simp] theorem lorentzBoost_zero_succ (u : MinkowskiSpace) (j : Fin 3) :
    lorentzBoost u 0 j.succ = u j.succ := by
  simp [lorentzBoost, Matrix.of_apply, Fin.cons_zero]

@[simp] theorem lorentzBoost_succ_zero (u : MinkowskiSpace) (i : Fin 3) :
    lorentzBoost u i.succ 0 = u i.succ := by
  simp [lorentzBoost, Matrix.of_apply, Fin.cons_succ, Fin.cons_zero]

@[simp] theorem lorentzBoost_succ_succ (u : MinkowskiSpace) (i j : Fin 3) :
    lorentzBoost u i.succ j.succ =
      (if i = j then 1 else 0) + u i.succ * u j.succ / (1 + u 0) := by
  simp [lorentzBoost, Matrix.of_apply, Fin.cons_succ]

/-- The time component of the boost action. -/
theorem lorentzBoost_mulVec_zero (u x : MinkowskiSpace) :
    (lorentzBoost u *ᵥ x) 0 = u 0 * x 0 + spatialDot u x := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, spatialDot]

/-- The spatial components of the boost action. -/
theorem lorentzBoost_mulVec_succ (u x : MinkowskiSpace) (k : Fin 3) :
    (lorentzBoost u *ᵥ x) k.succ =
      x k.succ + u k.succ * (x 0 + spatialDot u x / (1 + u 0)) := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, lorentzBoost_succ_zero]
  rw [show (∑ l : Fin 3, lorentzBoost u k.succ l.succ * x l.succ) =
      ∑ l : Fin 3, ((if l = k then x l.succ else 0) +
        u k.succ * (u l.succ * x l.succ) / (1 + u 0)) from
    Finset.sum_congr rfl fun l _ ↦ by
      rw [lorentzBoost_succ_succ]
      by_cases h : k = l
      · subst h
        simp only [ite_true]
        ring
      · have h' := Ne.symm h
        simp only [h, h', ite_false, zero_add]
        ring]
  rw [Finset.sum_add_distrib]
  have hif : (∑ l : Fin 3, if l = k then x l.succ else 0) = x k.succ := by
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
  rw [hif]
  have hu : (∑ l : Fin 3, u k.succ * (u l.succ * x l.succ) / (1 + u 0)) =
      u k.succ * spatialDot u x / (1 + u 0) := by
    simp only [div_eq_mul_inv, spatialDot, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [hu]
  ring

/-- The first column of the canonical boost is `u`: the boost maps the time
axis `e₀` to the hyperboloid point `u`. -/
theorem lorentzBoost_mulVec_single_zero (u : MinkowskiSpace) :
    lorentzBoost u *ᵥ Pi.single 0 1 = u := by
  rw [Matrix.mulVec_single_one]
  ext i
  cases i using Fin.cases <;> simp

/-- Cayley--Hamilton for the Pauli coordinate matrix:
`M(u)² = 2u₀·M(u) - η(u,u)·I`.  This is a polynomial identity; no
hyperboloid hypothesis is needed. -/
theorem pauliMatrixOfMinkowski_mul_self (u : MinkowskiSpace) :
    pauliMatrixOfMinkowski u * pauliMatrixOfMinkowski u =
      (2 * u 0 : ℂ) • pauliMatrixOfMinkowski u - (minkowskiQuadratic u : ℂ) • 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [pauliMatrixOfMinkowski, Fin.sum_univ_four, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, pauliMatrices,
      Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue,
      Fin.mk_zero, Fin.mk_one, Fin.reduceEq, ite_true, ite_false,
      minkowskiQuadratic, Complex.ofReal_sub, Complex.ofReal_pow] <;>
    ring_nf <;> try (simp only [Complex.I_sq]); ring_nf

/-- The anticommutator of two Pauli coordinate matrices, expressed through
the spatial dot product.  A polynomial identity. -/
theorem pauliMatrixOfMinkowski_anticomm (u x : MinkowskiSpace) :
    pauliMatrixOfMinkowski u * pauliMatrixOfMinkowski x +
        pauliMatrixOfMinkowski x * pauliMatrixOfMinkowski u =
      (2 * u 0 : ℂ) • pauliMatrixOfMinkowski x + (2 * x 0 : ℂ) • pauliMatrixOfMinkowski u +
        (2 * (spatialDot u x - u 0 * x 0) : ℂ) • 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [pauliMatrixOfMinkowski, Fin.sum_univ_four, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, pauliMatrices,
      Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue,
      Fin.mk_zero, Fin.mk_one, Fin.reduceEq, ite_true, ite_false,
      spatialDot_eq, Complex.ofReal_mul, Complex.ofReal_add] <;>
    ring_nf <;> try (simp only [Complex.I_sq]); ring_nf

/-- The closed-form boost spinor `P = (M(u) + I)/√(2(1+u₀))`: the positive
determinant-one square root of `M(u)` for `u` on the unit hyperboloid with
`u₀ > 0`.  This is Wolf's `P = exp(m·σ/2)` of Equation (2.44) with
`u = (cosh |m|, sinh |m| m̂)`, written without hyperbolic functions. -/
noncomputable def boostSpinor (u : MinkowskiSpace) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (2 * (1 + u 0)) : ℂ))⁻¹ • (pauliMatrixOfMinkowski u + 1)

/-- The boost spinor is Hermitian. -/
theorem boostSpinor_isHermitian (u : MinkowskiSpace) :
    (boostSpinor u).IsHermitian := by
  rw [Matrix.IsHermitian, boostSpinor, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, (pauliMatrixOfMinkowski_isHermitian u).eq,
    Matrix.conjTranspose_one]
  congr 1
  simp

/-- The canonical boost spinor is positive definite.  This is the `P > 0`
clause in Wolf's polar decomposition immediately before Equation (2.44)
(`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 1067--1077). -/
theorem boostSpinor_posDef (u : MinkowskiSpace) (hu : minkowskiQuadratic u = 1)
    (hu0 : 0 < u 0) :
    (boostSpinor u).PosDef := by
  have hM : (pauliMatrixOfMinkowski u).PosSemidef :=
    (posSemidef_pauliMatrixOfMinkowski_iff u).2 ⟨hu0.le, by rw [hu]; norm_num⟩
  have hbase : (pauliMatrixOfMinkowski u + 1).PosDef :=
    Matrix.PosDef.posSemidef_add hM Matrix.PosDef.one
  have hc : 0 < Real.sqrt (2 * (1 + u 0)) := Real.sqrt_pos.2 (by linarith)
  rw [boostSpinor, ← Complex.ofReal_inv]
  change (((Real.sqrt (2 * (1 + u 0)))⁻¹ : ℝ) •
    (pauliMatrixOfMinkowski u + 1)).PosDef
  exact hbase.smul (inv_pos.mpr hc)

/-- The determinant of `M(u) + I` is `2(1+u₀)` on the unit hyperboloid. -/
theorem det_pauliMatrixOfMinkowski_add_one (u : MinkowskiSpace)
    (hu : minkowskiQuadratic u = 1) :
    (pauliMatrixOfMinkowski u + 1).det = (2 * (1 + u 0) : ℂ) := by
  have h1 : (pauliMatrixOfMinkowski u + 1).det =
      (pauliMatrixOfMinkowski u).det + (pauliMatrixOfMinkowski u).trace + 1 := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
    simp only [Matrix.add_apply, Matrix.one_apply, Fin.reduceEq, ite_true, ite_false]
    ring
  rw [h1, det_pauliMatrixOfMinkowski, hu, trace_pauliMatrixOfMinkowski]
  push_cast
  ring

/-- The boost spinor has determinant one. -/
theorem boostSpinor_det (u : MinkowskiSpace) (hu : minkowskiQuadratic u = 1)
    (hu0 : 0 < u 0) :
    (boostSpinor u).det = 1 := by
  have hc : (0:ℝ) < 2 * (1 + u 0) := by linarith
  rw [boostSpinor, Matrix.det_smul, det_pauliMatrixOfMinkowski_add_one u hu]
  simp only [Fintype.card_fin]
  rw [inv_pow]
  have h2 : ((Real.sqrt (2 * (1 + u 0)) : ℂ)) ^ 2 = (2 * (1 + u 0) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hc.le
  rw [h2]
  exact inv_mul_cancel₀ (by exact_mod_cast hc.ne')

/-- The boost spinor as an element of `SL(2,ℂ)`. -/
noncomputable def boostSpinorSL2 (u : MinkowskiSpace) (hu : minkowskiQuadratic u = 1)
    (hu0 : 0 < u 0) : SL(2, ℂ) :=
  ⟨boostSpinor u, boostSpinor_det u hu hu0⟩

@[simp] theorem boostSpinorSL2_coe (u : MinkowskiSpace) (hu : minkowskiQuadratic u = 1)
    (hu0 : 0 < u 0) :
    (boostSpinorSL2 u hu hu0).1 = boostSpinor u := rfl

/-- The boost spinor squares to `M(u)`: `P_u² = u·σ`. -/
theorem boostSpinor_sq (u : MinkowskiSpace) (hu : minkowskiQuadratic u = 1)
    (hu0 : 0 < u 0) :
    boostSpinor u * boostSpinor u = pauliMatrixOfMinkowski u := by
  have hc : (0:ℝ) < 2 * (1 + u 0) := by linarith
  have hM2 := pauliMatrixOfMinkowski_mul_self u
  rw [boostSpinor, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hexp : (pauliMatrixOfMinkowski u + 1) * (pauliMatrixOfMinkowski u + 1) =
      pauliMatrixOfMinkowski u * pauliMatrixOfMinkowski u +
        2 • pauliMatrixOfMinkowski u + 1 := by
    noncomm_ring
  rw [hexp, hM2]
  have hmat : (2 * (u 0 : ℂ)) • pauliMatrixOfMinkowski u - (minkowskiQuadratic u : ℂ) • 1 +
      2 • pauliMatrixOfMinkowski u + 1 = (2 * u 0 + 2 : ℂ) • pauliMatrixOfMinkowski u := by
    rw [hu]
    module
  have hsc : ((Real.sqrt (2 * (1 + u 0)) : ℂ))⁻¹ * ((Real.sqrt (2 * (1 + u 0)) : ℂ))⁻¹ *
      (2 * u 0 + 2 : ℂ) = 1 := by
    rw [← pow_two, inv_pow,
      show ((Real.sqrt (2 * (1 + u 0)) : ℂ)) ^ 2 = ((2 * (1 + u 0) : ℝ) : ℂ) from
        by exact_mod_cast Real.sq_sqrt hc.le]
    rw [show (2 * (u 0 : ℂ) + 2) = ((2 * (1 + u 0) : ℝ) : ℂ) from by push_cast; ring]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne')
  rw [hmat, smul_smul, hsc, one_smul]

/-- `M(x)` is additive in its coordinates. -/
theorem pauliMatrixOfMinkowski_add (x y : MinkowskiSpace) :
    pauliMatrixOfMinkowski (x + y) =
      pauliMatrixOfMinkowski x + pauliMatrixOfMinkowski y := by
  simp [pauliMatrixOfMinkowski, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- `M(x)` is homogeneous in its coordinates. -/
theorem pauliMatrixOfMinkowski_smul (c : ℝ) (x : MinkowskiSpace) :
    pauliMatrixOfMinkowski (c • x) = (c : ℂ) • pauliMatrixOfMinkowski x := by
  simp [pauliMatrixOfMinkowski, Pi.smul_apply, smul_eq_mul, Finset.smul_sum,
    Complex.ofReal_mul, mul_smul]

/-- The Pauli-coordinate assembly is injective. -/
theorem pauliMatrixOfMinkowski_injective :
    Function.Injective pauliMatrixOfMinkowski := by
  intro x y h
  ext i
  have e1 := pauliMinkowskiCoordinate_pauliMatrixOfMinkowski x i
  have e2 := pauliMinkowskiCoordinate_pauliMatrixOfMinkowski y i
  simp only [pauliMinkowskiCoordinate] at e1 e2
  rw [← e1, ← e2, h]

/-- The spatial part of a Minkowski vector. -/
def spatialPart (u : MinkowskiSpace) : MinkowskiSpace :=
  fun i ↦ if i = 0 then 0 else u i

@[simp] theorem spatialPart_zero (u : MinkowskiSpace) : spatialPart u 0 = 0 := rfl

@[simp] theorem spatialPart_succ (u : MinkowskiSpace) (k : Fin 3) :
    spatialPart u k.succ = u k.succ := by
  simp [spatialPart, Fin.succ_ne_zero]

/-- A Minkowski vector splits into its time component and spatial part. -/
theorem eq_time_smul_single_add_spatialPart (u : MinkowskiSpace) :
    u = (u 0 : ℝ) • Pi.single 0 1 + spatialPart u := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ k => simp

/-- The unscaled conjugation identity: `(M(u)+I) M(x) (M(u)+I)` expanded as a
combination of `M(u)`, `M(x)`, and `I`.  A matrix-level consequence of
Cayley--Hamilton and the anticommutator; no hyperboloid hypothesis. -/
theorem pauliMatrixOfMinkowski_conj_add_one (u x : MinkowskiSpace) :
    (pauliMatrixOfMinkowski u + 1) * pauliMatrixOfMinkowski x * (pauliMatrixOfMinkowski u + 1) =
      (2 * (u 0 * x 0 + spatialDot u x + x 0) : ℂ) • pauliMatrixOfMinkowski u +
        (minkowskiQuadratic u + 2 * u 0 + 1 : ℂ) • pauliMatrixOfMinkowski x +
        (2 * (spatialDot u x - u 0 * x 0 - x 0 * minkowskiQuadratic u) : ℂ) • 1 := by
  have hM2 := pauliMatrixOfMinkowski_mul_self u
  have hanti := pauliMatrixOfMinkowski_anticomm u x
  have hMXM : pauliMatrixOfMinkowski u * pauliMatrixOfMinkowski x * pauliMatrixOfMinkowski u =
      pauliMatrixOfMinkowski u * (pauliMatrixOfMinkowski u * pauliMatrixOfMinkowski x +
        pauliMatrixOfMinkowski x * pauliMatrixOfMinkowski u) -
        pauliMatrixOfMinkowski u * pauliMatrixOfMinkowski u * pauliMatrixOfMinkowski x := by
    noncomm_ring
  have hexp : (pauliMatrixOfMinkowski u + 1) * pauliMatrixOfMinkowski x *
        (pauliMatrixOfMinkowski u + 1) =
      pauliMatrixOfMinkowski u * pauliMatrixOfMinkowski x * pauliMatrixOfMinkowski u +
        (pauliMatrixOfMinkowski u * pauliMatrixOfMinkowski x +
          pauliMatrixOfMinkowski x * pauliMatrixOfMinkowski u) + pauliMatrixOfMinkowski x := by
    noncomm_ring
  rw [hexp, hMXM, hanti, hM2]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_one]
  rw [hM2]
  module

/-- On the unit hyperboloid, the unscaled conjugation by `M(u) + I` is `2(1+u₀)`
times the Lorentz boost action on Pauli coordinates. -/
theorem boostSpinor_conj_scaled (u x : MinkowskiSpace) (hu : minkowskiQuadratic u = 1)
    (hu0 : 0 < u 0) :
    (pauliMatrixOfMinkowski u + 1) * pauliMatrixOfMinkowski x * (pauliMatrixOfMinkowski u + 1) =
      (2 * (1 + u 0) : ℂ) • pauliMatrixOfMinkowski (lorentzBoost u *ᵥ x) := by
  have h1a : (1 : ℝ) + u 0 ≠ 0 := by linarith
  rw [pauliMatrixOfMinkowski_conj_add_one, hu]
  have hy : lorentzBoost u *ᵥ x =
      x + (x 0 + spatialDot u x / (1 + u 0)) • spatialPart u +
        (u 0 * x 0 + spatialDot u x - x 0) • Pi.single 0 1 := by
    ext i
    cases i using Fin.cases with
    | zero =>
        rw [lorentzBoost_mulVec_zero]
        simp
    | succ k =>
        rw [lorentzBoost_mulVec_succ]
        simp
        ring
  have hMu : pauliMatrixOfMinkowski (spatialPart u) =
      pauliMatrixOfMinkowski u - (u 0 : ℂ) • 1 := by
    have e2 : pauliMatrixOfMinkowski u =
        (u 0 : ℂ) • 1 + pauliMatrixOfMinkowski (spatialPart u) := by
      conv_lhs => rw [eq_time_smul_single_add_spatialPart u, pauliMatrixOfMinkowski_add,
        pauliMatrixOfMinkowski_smul, pauliMatrixOfMinkowski_single, pauliMatrices_zero]
    rw [e2]
    module
  rw [hy, pauliMatrixOfMinkowski_add, pauliMatrixOfMinkowski_add, pauliMatrixOfMinkowski_smul,
    pauliMatrixOfMinkowski_smul, pauliMatrixOfMinkowski_single, pauliMatrices_zero, hMu]
  have hsc : (2 * (1 + u 0) : ℂ) * ((x 0 + spatialDot u x / (1 + u 0) : ℝ) : ℂ) =
      ((2 * (u 0 * x 0 + spatialDot u x + x 0) : ℝ) : ℂ) := by
    have hR : (2 : ℝ) * (1 + u 0) * (x 0 + spatialDot u x / (1 + u 0)) =
        2 * (u 0 * x 0 + spatialDot u x + x 0) := by
      field_simp
      ring
    calc (2 * (1 + u 0) : ℂ) * ((x 0 + spatialDot u x / (1 + u 0) : ℝ) : ℂ)
        = (((2 : ℝ) * (1 + u 0) * (x 0 + spatialDot u x / (1 + u 0)) : ℝ) : ℂ) := by norm_cast
      _ = _ := by rw [hR]
  simp only [smul_add, smul_smul]
  rw [hsc]
  push_cast
  module

/-- Conjugation by the boost spinor realizes the Lorentz boost on Pauli
coordinates: `P M(x) Pᴴ = M(B_u x)`.  This is the boost half of Wolf,
Equation (2.44), with `P_u = exp(m·σ/2)` in closed form. -/
theorem boostSpinor_conj (u x : MinkowskiSpace) (hu : minkowskiQuadratic u = 1)
    (hu0 : 0 < u 0) :
    boostSpinor u * pauliMatrixOfMinkowski x * (boostSpinor u)ᴴ =
      pauliMatrixOfMinkowski (lorentzBoost u *ᵥ x) := by
  have hc : (0:ℝ) < 2 * (1 + u 0) := by linarith
  rw [(boostSpinor_isHermitian u).eq, boostSpinor]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_two]
  rw [boostSpinor_conj_scaled u x hu hu0, smul_smul]
  rw [show ((Real.sqrt (2 * (1 + u 0)) : ℂ))⁻¹ ^ 2 * (2 * (1 + u 0) : ℂ) = 1 from by
    rw [inv_pow, show ((Real.sqrt (2 * (1 + u 0)) : ℂ)) ^ 2 = ((2 * (1 + u 0) : ℝ) : ℂ) from
      by exact_mod_cast Real.sq_sqrt hc.le]
    rw [show (2 * (1 + u 0) : ℂ) = ((2 * (1 + u 0) : ℝ) : ℂ) from by norm_cast]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne')]
  rw [one_smul]

/-- The spinor matrix of the boost spinor is the canonical boost: the boost
formula of Wolf, Equation (2.44). -/
theorem spinorMatrix_boostSpinorSL2 (u : MinkowskiSpace) (hu : minkowskiQuadratic u = 1)
    (hu0 : 0 < u 0) :
    spinorMatrix (boostSpinorSL2 u hu hu0) = lorentzBoost u := by
  apply Matrix.mulVec_injective
  funext x
  apply pauliMatrixOfMinkowski_injective
  rw [pauliMatrixOfMinkowski_spinorMatrix_mulVec, boostSpinorSL2_coe,
    boostSpinor_conj u x hu hu0]

/-! ### Surjectivity of the spinor cover -/


/-- The canonical boost of a future unit-hyperboloid point is special
orthochronous Lorentz: it is the spinor matrix of the boost spinor. -/
theorem lorentzBoost_isSpecialOrthochronousLorentz (u : MinkowskiSpace)
    (hu : minkowskiQuadratic u = 1) (hu0 : 0 < u 0) :
    IsSpecialOrthochronousLorentz (lorentzBoost u) := by
  rw [← spinorMatrix_boostSpinorSL2 u hu hu0]
  exact spinorMatrix_isSpecialOrthochronousLorentz _

/-- The Minkowski quadratic form as the squared time component minus the
squared spatial norm. -/
theorem minkowskiQuadratic_eq_sub_sum (x : MinkowskiSpace) :
    minkowskiQuadratic x = x 0 ^ 2 - ∑ k : Fin 3, x k.succ ^ 2 := by
  simp only [minkowskiQuadratic, Fin.sum_univ_three, Fin.succ_zero_eq_one',
    Fin.succ_one_eq_two', show Fin.succ (2 : Fin 3) = 3 from rfl]
  ring

/-- The first column of a special orthochronous Lorentz matrix lies on the
unit hyperboloid. -/
theorem IsSpecialOrthochronousLorentz.minkowskiQuadratic_firstCol
    {L : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsSpecialOrthochronousLorentz L) :
    minkowskiQuadratic (L *ᵥ Pi.single 0 1) = 1 := by
  have hcol := col_norm_of_lorentz hL.transpose_mul_metric_mul
  rw [minkowskiQuadratic_eq_sub_sum]
  have hent : ∀ i : Fin 4, (L *ᵥ Pi.single (0 : Fin 4) (1 : ℝ)) i = L i 0 :=
    fun i ↦ congrFun (Matrix.mulVec_single_one L 0) i
  rw [hent 0]
  have hsum : (∑ k : Fin 3, (L *ᵥ Pi.single (0 : Fin 4) (1 : ℝ)) k.succ ^ 2) =
      ∑ k : Fin 3, L k.succ 0 ^ 2 :=
    Finset.sum_congr rfl fun k _ ↦ by rw [hent k.succ]
  rw [hsum]
  exact hcol

/-- The spinor epimorphism of Wolf, Equation (2.42): every special
orthochronous Lorentz matrix `L ∈ SO⁺(1,3)` is the spinor matrix of some
`X ∈ SL(2,ℂ)`.  The preimage is constructed as the product `X = P_u U` of the
boost spinor of the first column `u = L e₀` and a special unitary lifting the
rotation block, giving the rotation--boost factorization of Wolf,
Equation (2.44). -/
theorem exists_sl2_spinorMatrix_eq {L : Matrix (Fin 4) (Fin 4) ℝ}
    (hL : IsSpecialOrthochronousLorentz L) :
    ∃ X : SL(2, ℂ), spinorMatrix X = L := by
  have hu1 := hL.minkowskiQuadratic_firstCol
  have hu0 : 0 < (L *ᵥ Pi.single (0 : Fin 4) (1 : ℝ)) 0 := by
    have hent : (L *ᵥ Pi.single (0 : Fin 4) (1 : ℝ)) 0 = L 0 0 :=
      congrFun (Matrix.mulVec_single_one L 0) 0
    rw [hent]
    exact hL.2.2
  set u := L *ᵥ Pi.single (0 : Fin 4) (1 : ℝ) with hu
  have hB : IsSpecialOrthochronousLorentz (lorentzBoost u) :=
    lorentzBoost_isSpecialOrthochronousLorentz u hu1 hu0
  have hdetB : IsUnit (lorentzBoost u).det := by rw [hB.1]; exact isUnit_one
  have hBinv_u : (lorentzBoost u)⁻¹ *ᵥ u = Pi.single 0 1 := by
    calc (lorentzBoost u)⁻¹ *ᵥ u
        = (lorentzBoost u)⁻¹ *ᵥ (lorentzBoost u *ᵥ Pi.single 0 1) := by
          rw [lorentzBoost_mulVec_single_zero]
      _ = ((lorentzBoost u)⁻¹ * lorentzBoost u) *ᵥ Pi.single 0 1 :=
          Matrix.mulVec_mulVec _ _ _
      _ = Pi.single 0 1 := by
          rw [Matrix.nonsing_inv_mul _ hdetB, Matrix.one_mulVec]
  have hBL : IsSpecialOrthochronousLorentz ((lorentzBoost u)⁻¹ * L) :=
    hB.inv.mul hL
  have hfix : ((lorentzBoost u)⁻¹ * L) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [← Matrix.mulVec_mulVec]
    exact hBinv_u
  obtain ⟨R, hR, hblk⟩ := exists_so3_block_of_fixes_time hfix
    hBL.transpose_mul_metric_mul hBL.1
  have hLdecomp : L = lorentzBoost u * lorentzRotationBlock R := by
    calc L = lorentzBoost u * ((lorentzBoost u)⁻¹ * L) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetB, Matrix.one_mul]
      _ = lorentzBoost u * lorentzRotationBlock R := by rw [hblk]
  obtain ⟨U, hU, hUlift⟩ := exists_su2_spinorMatrix_eq_lorentzRotationBlock R hR
  refine ⟨boostSpinorSL2 u hu1 hu0 * su2ToSL2 U hU, ?_⟩
  rw [spinorMatrix_mul, spinorMatrix_boostSpinorSL2 u hu1 hu0, hUlift]
  exact hLdecomp.symm

/-- The bundled spinor homomorphism `SL(2,ℂ) → SO⁺(1,3)` is surjective:
Wolf's spinor map of Equation (2.42) is an epimorphism onto the special
orthochronous Lorentz group. -/
theorem spinorCoverHom_surjective : Function.Surjective spinorCoverHom := by
  intro L
  obtain ⟨X, hX⟩ := exists_sl2_spinorMatrix_eq L.2
  exact ⟨X, Subtype.ext hX⟩

/-- The fibres of the spinor cover have exactly two points: together with
`spinorCoverHom_surjective` this says `SL(2,ℂ)` is a double cover of
`SO⁺(1,3)`, as stated after Wolf, Equation (2.42). -/
theorem spinorCoverHom_eq_iff_eq_or_eq_neg (X Y : SL(2, ℂ)) :
    spinorCoverHom X = spinorCoverHom Y ↔ X = Y ∨ X = -Y := by
  rw [Subtype.ext_iff]
  exact spinorMatrix_eq_iff_eq_or_eq_neg X Y

/-- The kernel of the spinor cover is exactly `{1, -1}`. -/
theorem spinorCoverHom_eq_one_iff (X : SL(2, ℂ)) :
    spinorCoverHom X = 1 ↔ X = 1 ∨ X = -1 := by
  have h1 : (1 : ↥specialOrthochronousLorentzGroup) = spinorCoverHom 1 :=
    (map_one spinorCoverHom).symm
  rw [h1]
  exact spinorCoverHom_eq_iff_eq_or_eq_neg X 1

end Wolf
