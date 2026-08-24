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
    simp [Matrix.mul_apply, minkowskiMetric, Matrix.diagonal_apply]
    exact h00

/-- The time-row Minkowski norm identity from `L η Lᵀ = η`. -/
theorem row_norm_of_lorentz {L : Matrix (Fin 4) (Fin 4) ℝ}
    (h : L * minkowskiMetric * Lᵀ = minkowskiMetric) :
    L 0 0 ^ 2 - ∑ k : Fin 3, L 0 k.succ ^ 2 = 1 := by
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMetric,
    Matrix.diagonal_apply, Fin.sum_univ_four] at h00
  rw [Fin.sum_univ_three]
  show L 0 0 ^ 2 - (L 0 1 ^ 2 + L 0 2 ^ 2 + L 0 3 ^ 2) = 1
  linarith [h00]

/-- The time-column Minkowski norm identity from `Lᵀ η L = η`. -/
theorem col_norm_of_lorentz {L : Matrix (Fin 4) (Fin 4) ℝ}
    (h : Lᵀ * minkowskiMetric * L = minkowskiMetric) :
    L 0 0 ^ 2 - ∑ k : Fin 3, L k.succ 0 ^ 2 = 1 := by
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMetric,
    Matrix.diagonal_apply, Fin.sum_univ_four] at h00
  rw [Fin.sum_univ_three]
  show L 0 0 ^ 2 - (L 1 0 ^ 2 + L 2 0 ^ 2 + L 3 0 ^ 2) = 1
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
    have hcolB := col_norm_of_lorentz (IsSpecialOrthochronousLorentz.transpose_mul_metric_mul ⟨hdetB, hlorB, h00B⟩)
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

@[simp] theorem lorentzRotationBlock_one : lorentzRotationBlock (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
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
        show L 1 i.succ * L 1 j.succ + L 2 i.succ * L 2 j.succ + L 3 i.succ * L 3 j.succ =
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


end Wolf
