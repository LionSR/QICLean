/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausMap
import QICLean.Channel.KrausRank
import QICLean.Channel.LorentzNormalForm.SpinorAction

/-!
# Canonical qubit-channel representatives

This module formalizes the three channel representatives displayed in
Verstraete--Verschelde, *On Quantum Channels*, arXiv:quant-ph/0202124v2,
Theorem 8, Equations (17)--(19), and repeated in Wolf, Proposition 2.11
(`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 1021--1035).
The non-diagonal and singular rank statements also appear in cases 2 and 3
of Wolf--Cirac, *Dividing Quantum Channels*, arXiv:math-ph/0611057v3,
Theorem 18.  The diagonal rank formula below instead follows directly from
the Bell family in Verstraete--Verschelde, Equation (18).

Only the displayed representatives are treated here.  In particular, this file
does not prove that every qubit channel has one of these forms, does not derive
the necessary range `0 ≤ x ≤ 1`, and does not construct filtering maps.

The Pauli-transfer convention is Wolf's
`T̂ᵢⱼ = tr[σᵢ T(σⱼ)] / 2`.  QICLean's Choi matrix is normalized, so
for a trace-preserving qubit map
`tau = (1/4) sum i j, T̂ᵢⱼ σᵢ ⊗ σⱼᵀ`.  Consequently a raw Pauli
correlation matrix of `tau` satisfies
`R_raw(tau) = T̂ * diag(1, 1, -1, 1)`; the extra sign in its `σ₂` input
column comes from `σ₂ᵀ = -σ₂`.  Verstraete--Verschelde instead define
`R_Φ` from their first-factor-partially-transposed dual state and use it in the Bloch
action `(1, x') = R_Φ (1, x)`.  Thus their `R_Φ` is the transfer matrix
corresponding to `T̂`, not the raw correlation matrix of `tau`.

Verstraete--Verschelde, Theorem 8 nevertheless prints the constraint
`1 - s₁ - s₂ - s₃ ≥ 0`.  This is inconsistent with their preceding transfer
convention: the identity channel has `R_Φ = diag(1, 1, 1, 1)` and violates that
printed inequality.  The weights below are therefore obtained directly by applying
the Equation (18) Pauli family in Wolf's transfer convention.  In particular the
last weight is `(1 - s₁ - s₂ + s₃) / 4`, in agreement with Wolf's
Equation (2.40); no parameter conversion from the printed all-minus inequality is used.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset

noncomputable section

namespace Wolf

private abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ
private abbrev QubitMap := QubitMatrix →ₗ[ℂ] QubitMatrix

/-! ## The diagonal (bistochastic) representative -/

/-- The four candidate Bell-diagonal weights obtained by inverting the Pauli action of
the Equation (18) family in Wolf's transfer convention.  Under the nonnegativity
hypothesis used below, they are the squared source amplitudes `pᵢ²`.  The final
`+s₃` is the direct Pauli-family sign, not Verstraete--Verschelde's inconsistent
printed all-minus constraint. -/
def diagonalBellWeight (s₁ s₂ s₃ : ℝ) : Fin 4 → ℝ
  | 0 => (1 + s₁ + s₂ + s₃) / 4
  | 1 => (1 + s₁ - s₂ - s₃) / 4
  | 2 => (1 - s₁ + s₂ - s₃) / 4
  | 3 => (1 - s₁ - s₂ + s₃) / 4

/-- The diagonal entries of the Pauli transfer matrix, including the
trace-preserving entry `s₀ = 1`. -/
def diagonalPauliEigenvalue (s₁ s₂ s₃ : ℝ) : Fin 4 → ℝ
  | 0 => 1
  | 1 => s₁
  | 2 => s₂
  | 3 => s₃

/-- Square-root coefficients for the diagonal Pauli family.  When the four
weights are nonnegative, these are the coefficients `pᵢ` in the Equation (18)
family `{p₀ σ₀, p₁ σ₁, p₂ σ₂, p₃ σ₃}`, specialized to `A = B = I` and
related to the transfer parameters by the direct Pauli-action calculation above. -/
def diagonalKrausCoefficient (s₁ s₂ s₃ : ℝ) (i : Fin 4) : ℝ :=
  Real.sqrt (diagonalBellWeight s₁ s₂ s₃ i)

/-- The four-operator Pauli family built from `diagonalKrausCoefficient`.
Under nonnegative weights it is the diagonal representative in
Verstraete--Verschelde, Theorem 8, Equation (18), with `A = B = I`. -/
def diagonalKraus (s₁ s₂ s₃ : ℝ) : Fin 4 → QubitMatrix :=
  fun i ↦ (diagonalKrausCoefficient s₁ s₂ s₃ i : ℂ) • pauliMatrices i

/-- The completely positive Kraus map built from `diagonalKraus`.

If a candidate weight is negative, `Real.sqrt` clips it to zero.  Therefore
the theorems identifying this map with the source diagonal representative and
its parameters explicitly assume that every weight is nonnegative. -/
def diagonalMap (s₁ s₂ s₃ : ℝ) : QubitMap :=
  Kraus.mapLM (diagonalKraus s₁ s₂ s₃)

/-- Indices of the nonzero candidate Bell-diagonal weights. -/
abbrev diagonalBellSupport (s₁ s₂ s₃ : ℝ) :=
  {i : Fin 4 // diagonalBellWeight s₁ s₂ s₃ i ≠ 0}

/-- The four candidate Bell-diagonal weights sum to one. -/
theorem sum_diagonalBellWeight (s₁ s₂ s₃ : ℝ) :
    ∑ i : Fin 4, diagonalBellWeight s₁ s₂ s₃ i = 1 := by
  simp [diagonalBellWeight, Fin.sum_univ_four]
  ring

/-- Simultaneous nonnegativity of the four Bell weights is equivalent to the
four displayed linear inequalities. -/
theorem diagonalBellWeight_nonneg_iff (s₁ s₂ s₃ : ℝ) :
    (∀ i, 0 ≤ diagonalBellWeight s₁ s₂ s₃ i) ↔
      0 ≤ 1 + s₁ + s₂ + s₃ ∧
      0 ≤ 1 + s₁ - s₂ - s₃ ∧
      0 ≤ 1 - s₁ + s₂ - s₃ ∧
      0 ≤ 1 - s₁ - s₂ + s₃ := by
  constructor
  · intro h
    have h₀ := h (0 : Fin 4)
    have h₁ := h (1 : Fin 4)
    have h₂ := h (2 : Fin 4)
    have h₃ := h (3 : Fin 4)
    simp [diagonalBellWeight] at h₀ h₁ h₂ h₃
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩ i
    fin_cases i <;> simp [diagonalBellWeight] <;> linarith

/-- Under Wolf's ordered diagonal convention, the single displayed
Fujiwara--Algoet inequality supplies all four nonnegative Bell-diagonal
eigenvalues. -/
theorem diagonalBellWeight_nonneg_of_ordered
    {s₁ s₂ s₃ : ℝ} (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ s₁)
    (hs₃ : |s₃| ≤ s₂) (hcp : s₁ + s₂ ≤ 1 + s₃) :
    ∀ i, 0 ≤ diagonalBellWeight s₁ s₂ s₃ i := by
  rw [diagonalBellWeight_nonneg_iff]
  constructor
  · nlinarith [le_abs_self s₃, neg_abs_le s₃]
  constructor
  · nlinarith [le_abs_self s₃, neg_abs_le s₃]
  constructor
  · nlinarith [le_abs_self s₃, neg_abs_le s₃]
  · linarith

/-- The source Pauli family is trace preserving whenever its Bell-diagonal
eigenvalues are nonnegative. -/
theorem diagonalKraus_isTP {s₁ s₂ s₃ : ℝ}
    (hweight : ∀ i, 0 ≤ diagonalBellWeight s₁ s₂ s₃ i) :
    Kraus.IsTP (diagonalKraus s₁ s₂ s₃) := by
  have hsqrt (i : Fin 4) :
      Real.sqrt (diagonalBellWeight s₁ s₂ s₃ i) ^ 2 =
        diagonalBellWeight s₁ s₂ s₃ i :=
    Real.sq_sqrt (hweight i)
  have hsqrtℂ (i : Fin 4) :
      (diagonalKrausCoefficient s₁ s₂ s₃ i : ℂ) *
          (diagonalKrausCoefficient s₁ s₂ s₃ i : ℂ) =
        (diagonalBellWeight s₁ s₂ s₃ i : ℂ) := by
    exact_mod_cast (show
      diagonalKrausCoefficient s₁ s₂ s₃ i *
          diagonalKrausCoefficient s₁ s₂ s₃ i =
        diagonalBellWeight s₁ s₂ s₃ i by
      simpa [diagonalKrausCoefficient, pow_two] using hsqrt i)
  have hsumℂ :
      ∑ i : Fin 4, (diagonalBellWeight s₁ s₂ s₃ i : ℂ) = 1 := by
    exact_mod_cast sum_diagonalBellWeight s₁ s₂ s₃
  rw [Kraus.IsTP]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [diagonalKraus, pauliMatrices,
      Fin.sum_univ_four, Matrix.mul_apply, Matrix.conjTranspose_apply,
      hsqrtℂ]
  all_goals simpa [Fin.sum_univ_four] using hsumℂ

/-- The source Pauli family defines a diagonal qubit channel. -/
theorem diagonalMap_isChannel {s₁ s₂ s₃ : ℝ}
    (hweight : ∀ i, 0 ≤ diagonalBellWeight s₁ s₂ s₃ i) :
    IsChannel (diagonalMap s₁ s₂ s₃) :=
  Kraus.isChannel_mapLM _ (diagonalKraus_isTP hweight)

/-- Each Pauli matrix is an eigenvector of the diagonal representative. -/
theorem diagonalMap_pauli {s₁ s₂ s₃ : ℝ}
    (hweight : ∀ i, 0 ≤ diagonalBellWeight s₁ s₂ s₃ i) (j : Fin 4) :
    diagonalMap s₁ s₂ s₃ (pauliMatrices j) =
      (diagonalPauliEigenvalue s₁ s₂ s₃ j : ℂ) • pauliMatrices j := by
  have hsqrtℂ (i : Fin 4) :
      (diagonalKrausCoefficient s₁ s₂ s₃ i : ℂ) *
          (diagonalKrausCoefficient s₁ s₂ s₃ i : ℂ) =
        (diagonalBellWeight s₁ s₂ s₃ i : ℂ) := by
    exact_mod_cast (show
      diagonalKrausCoefficient s₁ s₂ s₃ i *
          diagonalKrausCoefficient s₁ s₂ s₃ i =
        diagonalBellWeight s₁ s₂ s₃ i by
      simpa [diagonalKrausCoefficient, pow_two] using Real.sq_sqrt (hweight i))
  have hsqrtPowℂ (i : Fin 4) :
      (diagonalKrausCoefficient s₁ s₂ s₃ i : ℂ) ^ 2 =
        (diagonalBellWeight s₁ s₂ s₃ i : ℂ) := by
    simpa [pow_two] using hsqrtℂ i
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [diagonalMap, Kraus.map_apply, diagonalKraus, pauliMatrices,
      diagonalPauliEigenvalue, Fin.sum_univ_four, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, hsqrtℂ]
  all_goals try simp [diagonalBellWeight]
  case «2».«0».«1» =>
    have h₀ := hsqrtPowℂ (0 : Fin 4)
    have h₁ := hsqrtPowℂ (1 : Fin 4)
    have h₂ := hsqrtPowℂ (2 : Fin 4)
    have h₃ := hsqrtPowℂ (3 : Fin 4)
    simp [diagonalBellWeight] at h₀ h₁ h₂ h₃
    linear_combination -Complex.I * h₀ + Complex.I * h₁ -
      Complex.I * h₂ + Complex.I * h₃
  case «2».«1».«0» =>
    have h₀ := hsqrtPowℂ (0 : Fin 4)
    have h₁ := hsqrtPowℂ (1 : Fin 4)
    have h₂ := hsqrtPowℂ (2 : Fin 4)
    have h₃ := hsqrtPowℂ (3 : Fin 4)
    simp [diagonalBellWeight] at h₀ h₁ h₂ h₃
    linear_combination Complex.I * h₀ - Complex.I * h₁ +
      Complex.I * h₂ - Complex.I * h₃
  all_goals ring

/-- Exact Pauli-transfer matrix of the diagonal representative. -/
theorem pauliTransferMatrix_diagonalMap {s₁ s₂ s₃ : ℝ}
    (hweight : ∀ i, 0 ≤ diagonalBellWeight s₁ s₂ s₃ i) :
    pauliTransferMatrix (diagonalMap s₁ s₂ s₃) =
      Matrix.diagonal (fun i ↦ (diagonalPauliEigenvalue s₁ s₂ s₃ i : ℂ)) := by
  ext i j
  rw [pauliTransferMatrix, pauliTransferEntry, diagonalMap_pauli hweight]
  fin_cases i <;> fin_cases j <;>
    norm_num [diagonalPauliEigenvalue, pauliMatrices, Matrix.diagonal_apply,
      Matrix.trace_fin_two, Matrix.mul_apply]
  all_goals ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals ring

/-- The source-displayed Pauli channel satisfies the diagonal normal-form
predicate.  This does not assert existence of such a representative in every
filtering orbit. -/
theorem isLorentzDiagonal_diagonalMap {s₁ s₂ s₃ : ℝ}
    (hweight : ∀ i, 0 ≤ diagonalBellWeight s₁ s₂ s₃ i) :
    IsLorentzDiagonal (diagonalMap s₁ s₂ s₃) := by
  refine ⟨diagonalMap_isChannel hweight, ?_, ?_⟩
  · have hpauli : pauliMatrices (0 : Fin 4) = (1 : QubitMatrix) := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [pauliMatrices]
    have h := diagonalMap_pauli hweight (0 : Fin 4)
    rw [hpauli] at h
    simpa [diagonalPauliEigenvalue] using h
  · intro i j hij
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M i j)
      (pauliTransferMatrix_diagonalMap hweight)
    simpa [pauliTransferMatrix, Matrix.diagonal_apply, hij] using h

private theorem pauliMatrices_linearIndependent :
    LinearIndependent ℂ pauliMatrices := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h₀₀ := congrArg (fun M : QubitMatrix ↦ M 0 0) hg
  have h₁₁ := congrArg (fun M : QubitMatrix ↦ M 1 1) hg
  have h₀₁ := congrArg (fun M : QubitMatrix ↦ M 0 1) hg
  have h₁₀ := congrArg (fun M : QubitMatrix ↦ M 1 0) hg
  have h₀₀' : g 0 + g 3 = 0 := by
    simpa [Fin.sum_univ_four, pauliMatrices] using h₀₀
  have h₁₁' : g 0 + -g 3 = 0 := by
    simpa [Fin.sum_univ_four, pauliMatrices] using h₁₁
  have h₀₁' : g 1 + -(g 2 * Complex.I) = 0 := by
    simpa [Fin.sum_univ_four, pauliMatrices] using h₀₁
  have h₁₀' : g 1 + g 2 * Complex.I = 0 := by
    simpa [Fin.sum_univ_four, pauliMatrices] using h₁₀
  have hg₀ : g 0 = 0 := by linear_combination (h₀₀' + h₁₁') / 2
  have hg₃ : g 3 = 0 := by linear_combination (h₀₀' - h₁₁') / 2
  have hg₁ : g 1 = 0 := by linear_combination (h₀₁' + h₁₀') / 2
  have hg₂ : g 2 = 0 := by
    have hI : g 2 * Complex.I = 0 := by
      linear_combination (h₁₀' - h₀₁') / 2
    exact (mul_eq_zero.mp hI).resolve_right Complex.I_ne_zero
  fin_cases i
  · exact hg₀
  · exact hg₁
  · exact hg₂
  · exact hg₃

/-! ## The non-diagonal representative -/

/-- The three fixed matrix directions in the Kraus family of
Verstraete--Verschelde, Equation (19). -/
def nonDiagonalKrausBase : Fin 3 → QubitMatrix
  | 0 => !![1, 0; 0, (1 / Real.sqrt 3 : ℝ)]
  | 1 => !![1, 0; 0, (-1 / Real.sqrt 3 : ℝ)]
  | 2 => !![0, 1; 0, 0]

/-- The three real coefficients in the Kraus family of
Verstraete--Verschelde, Equation (19). -/
def nonDiagonalKrausCoefficient (x : ℝ) : Fin 3 → ℝ
  | 0 => Real.sqrt ((1 + x) / 2)
  | 1 => Real.sqrt ((1 - x) / 2)
  | 2 => Real.sqrt (2 / 3)

/-- The exact three-operator non-diagonal Kraus family from
Verstraete--Verschelde, Equation (19).  The hypotheses `0 ≤ x ≤ 1` are
used only when certifying that this family is trace preserving. -/
def nonDiagonalKraus (x : ℝ) : Fin 3 → QubitMatrix :=
  fun i ↦ (nonDiagonalKrausCoefficient x i : ℂ) • nonDiagonalKrausBase i

/-- The canonical non-diagonal completely positive map whose Pauli-transfer
matrix is the second normal form in Verstraete--Verschelde, Equation (17). -/
def nonDiagonalMap (x : ℝ) : QubitMap :=
  Kraus.mapLM (nonDiagonalKraus x)

/-- The source-displayed non-diagonal Kraus family is trace preserving on
the stated parameter interval. -/
theorem nonDiagonalKraus_isTP {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Kraus.IsTP (nonDiagonalKraus x) := by
  have hplus : 0 ≤ (1 + x) / 2 := by linarith
  have hminus : 0 ≤ (1 - x) / 2 := by linarith
  have hsplus := Real.sq_sqrt hplus
  have hsminus := Real.sq_sqrt hminus
  have hstwo := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / 3 by norm_num)
  have hplus' : 0 ≤ 1 + x := by linarith
  have hminus' : 0 ≤ 1 - x := by linarith
  have hsplus' := Real.sq_sqrt hplus'
  have hsminus' := Real.sq_sqrt hminus'
  have hsqrtTwo := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsqrtThree := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hsqrtTwo_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtThree_ne : Real.sqrt 3 ≠ 0 := by positivity
  have hsqrtTwoFour : Real.sqrt 2 ^ 4 = 4 := by
    rw [show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring, hsqrtTwo]
    norm_num
  rw [Kraus.IsTP]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nonDiagonalKraus, nonDiagonalKrausCoefficient,
      nonDiagonalKrausBase, Fin.sum_univ_three, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      hsplus, hsminus, hstwo]
  all_goals norm_cast
  all_goals field_simp [hsqrtTwo_ne, hsqrtThree_ne]
  all_goals norm_num [hsplus', hsminus', hsqrtTwo, hsqrtThree, hsqrtTwoFour]

/-- The source-displayed non-diagonal Kraus family defines a channel on
`0 ≤ x ≤ 1`.  This is a sufficiency statement, not a derivation of the
parameter range. -/
theorem nonDiagonalMap_isChannel {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    IsChannel (nonDiagonalMap x) :=
  Kraus.isChannel_mapLM _ (nonDiagonalKraus_isTP hx0 hx1)

/-- Entrywise action of the canonical non-diagonal representative. -/
theorem nonDiagonalMap_apply {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (X : QubitMatrix) :
    nonDiagonalMap x X =
      !![X 0 0 + (2 / 3 : ℂ) * X 1 1, (x / Real.sqrt 3 : ℝ) * X 0 1;
         (x / Real.sqrt 3 : ℝ) * X 1 0, (1 / 3 : ℂ) * X 1 1] := by
  have hplus : 0 ≤ (1 + x) / 2 := by linarith
  have hminus : 0 ≤ (1 - x) / 2 := by linarith
  have hsplus : Real.sqrt ((1 + x) / 2) ^ 2 = (1 + x) / 2 := Real.sq_sqrt hplus
  have hsminus : Real.sqrt ((1 - x) / 2) ^ 2 = (1 - x) / 2 := Real.sq_sqrt hminus
  have hstwo : Real.sqrt (2 / 3) ^ 2 = (2 / 3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrtThree : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrtThree_ne : Real.sqrt 3 ≠ 0 := by positivity
  have hplus' : 0 ≤ 1 + x := by linarith
  have hminus' : 0 ≤ 1 - x := by linarith
  have hsplus' : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt hplus'
  have hsminus' : Real.sqrt (1 - x) ^ 2 = 1 - x := Real.sq_sqrt hminus'
  have hsqrtTwo : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtTwo_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hsumReal :
      Real.sqrt (1 + x) / Real.sqrt 2 * (Real.sqrt (1 + x) / Real.sqrt 2) +
        Real.sqrt (1 - x) / Real.sqrt 2 * (Real.sqrt (1 - x) / Real.sqrt 2) = 1 := by
    field_simp [hsqrtTwo_ne]
    nlinarith [hsplus', hsminus', hsqrtTwo]
  have hdiffReal :
      Real.sqrt (1 + x) / Real.sqrt 2 * (Real.sqrt (1 + x) / Real.sqrt 2) -
        Real.sqrt (1 - x) / Real.sqrt 2 * (Real.sqrt (1 - x) / Real.sqrt 2) = x := by
    field_simp [hsqrtTwo_ne]
    nlinarith [hsplus', hsminus', hsqrtTwo]
  have hraiseReal :
      Real.sqrt 2 / Real.sqrt 3 * (Real.sqrt 2 / Real.sqrt 3) = 2 / 3 := by
    field_simp [hsqrtThree_ne, hsqrtTwo_ne]
    nlinarith [hsqrtTwo, hsqrtThree]
  have hinvThreeReal :
      (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = 1 / 3 := by
    field_simp [hsqrtThree_ne]
    nlinarith [hsqrtThree]
  have hsum :
      ((Real.sqrt (1 + x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (((Real.sqrt (1 + x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) +
        ((Real.sqrt (1 - x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (((Real.sqrt (1 - x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) = 1 := by
    exact_mod_cast hsumReal
  have hdiff :
      ((Real.sqrt (1 + x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (((Real.sqrt (1 + x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) -
        ((Real.sqrt (1 - x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (((Real.sqrt (1 - x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) = x := by
    exact_mod_cast hdiffReal
  have hraise :
      ((Real.sqrt 2 : ℝ) : ℂ) / ((Real.sqrt 3 : ℝ) : ℂ) *
          (((Real.sqrt 2 : ℝ) : ℂ) / ((Real.sqrt 3 : ℝ) : ℂ)) =
        ((2 / 3 : ℝ) : ℂ) := by
    exact_mod_cast hraiseReal
  have hinvThree :
      (((Real.sqrt 3 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 3 : ℝ) : ℂ))⁻¹ =
        ((1 / 3 : ℝ) : ℂ) := by
    exact_mod_cast hinvThreeReal
  norm_num at hraise hinvThree
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nonDiagonalMap, Kraus.map_apply, nonDiagonalKraus,
      nonDiagonalKrausCoefficient, nonDiagonalKrausBase, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]
  · linear_combination (X 0 0) * hsum + (X 1 1) * hraise
  · linear_combination (X 0 1 * (((Real.sqrt 3 : ℝ) : ℂ))⁻¹) * hdiff
  · linear_combination (X 1 0 * (((Real.sqrt 3 : ℝ) : ℂ))⁻¹) * hdiff
  · have hdiag :
        ((((Real.sqrt (1 + x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) *
              (((Real.sqrt (1 + x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) +
            (((Real.sqrt (1 - x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) *
              (((Real.sqrt (1 - x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ))) *
            ((((Real.sqrt 3 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 3 : ℝ) : ℂ))⁻¹) = 1 / 3 := by
        rw [hsum, hinvThree]
        norm_num
    linear_combination (X 1 1) * hdiag

/-- Exact Pauli-transfer matrix of the non-diagonal representative in
Wolf, Proposition 2.11 case 2. -/
theorem pauliTransferMatrix_nonDiagonalMap {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    pauliTransferMatrix (nonDiagonalMap x) =
      (!![1, 0, 0, 0;
          0, (x / Real.sqrt 3 : ℝ), 0, 0;
          0, 0, (x / Real.sqrt 3 : ℝ), 0;
          (2 / 3 : ℝ), 0, 0, (1 / 3 : ℝ)] : Matrix (Fin 4) (Fin 4) ℝ).map
        Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliTransferMatrix, pauliTransferEntry,
      nonDiagonalMap_apply hx0 hx1, pauliMatrices, Matrix.trace_fin_two,
      Matrix.mul_apply]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/-- The displayed map satisfies the existing non-diagonal normal-form
predicate.  This does not assert existence of such a representative in every
filtering orbit. -/
theorem isLorentzNonDiagonal_nonDiagonalMap {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    IsLorentzNonDiagonal (nonDiagonalMap x) := by
  refine ⟨nonDiagonalMap_isChannel hx0 hx1, x, hx0, hx1, ?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 3 0)
      (pauliTransferMatrix_nonDiagonalMap hx0 hx1)
    simpa [pauliTransferMatrix] using h
  · have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 1 1)
      (pauliTransferMatrix_nonDiagonalMap hx0 hx1)
    simpa [pauliTransferMatrix] using h
  · have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 2 2)
      (pauliTransferMatrix_nonDiagonalMap hx0 hx1)
    simpa [pauliTransferMatrix] using h
  · have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 3 3)
      (pauliTransferMatrix_nonDiagonalMap hx0 hx1)
    simpa [pauliTransferMatrix] using h
  · intro i j hij htranslation
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M i j)
      (pauliTransferMatrix_nonDiagonalMap hx0 hx1)
    fin_cases i <;> fin_cases j <;> simp_all [pauliTransferMatrix]

/-! ## Choi/Kraus ranks of the displayed family -/

private theorem rank_sum_vecMulVec_eq_card_of_linearIndependent
    {n ι : Type*} [Fintype n] [Fintype ι] (v : ι → n → ℂ)
    (hv : LinearIndependent ℂ v) :
    (∑ i : ι, Matrix.vecMulVec (v i) (star (v i))).rank = Fintype.card ι := by
  let C : Matrix n ι ℂ := fun p i ↦ v i p
  have hsum :
      ∑ i : ι, Matrix.vecMulVec (v i) (star (v i)) = C * Cᴴ := by
    ext p q
    rw [Matrix.sum_apply, Matrix.mul_apply]
    change (∑ i : ι, v i p * star (v i q)) =
      ∑ i : ι, v i p * star (v i q)
    rfl
  rw [hsum, Matrix.rank_self_mul_conjTranspose, Matrix.rank_eq_finrank_span_cols]
  change Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = Fintype.card ι
  simpa using finrank_span_eq_card hv

private theorem choiRank_mapLM_eq_card_of_linearIndependent {r : ℕ}
    (K : Fin r → QubitMatrix) (hK : LinearIndependent ℂ K) :
    Channel.choiRank (Kraus.mapLM K) = r := by
  let c : ℂ := 1 / ((2 : ℝ).sqrt : ℂ)
  let v : Fin r → (Fin 2 × Fin 2) → ℂ :=
    fun j p ↦ c * K j p.1 p.2
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff] at hK ⊢
    intro g hg i
    apply hK g _ i
    apply Matrix.ext
    intro a b
    have hab := congrFun hg (a, b)
    have hentry : c * (∑ j : Fin r, g j * K j a b) = 0 := by
      simpa [v, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hab
    rw [Matrix.sum_apply, show (0 : QubitMatrix) a b = 0 by rfl]
    simpa only [Matrix.smul_apply, smul_eq_mul] using
      (mul_eq_zero.mp hentry).resolve_left hc
  change (ChoiJamiolkowski.choiMatrix (Kraus.mapLM K)).rank = r
  rw [Channel.choiMatrix_mapLM_eq_sum_vecMulVec]
  change (∑ i : Fin r, Matrix.vecMulVec (v i) (star (v i))).rank = r
  simpa using rank_sum_vecMulVec_eq_card_of_linearIndependent v hv

/-- The diagonal representative's Choi/Kraus rank is exactly the number of
nonzero Bell-diagonal eigenvalues.  This includes every rank-drop boundary,
rather than assuming the generic rank-four case. -/
theorem choiRank_diagonalMap {s₁ s₂ s₃ : ℝ}
    (hweight : ∀ i, 0 ≤ diagonalBellWeight s₁ s₂ s₃ i) :
    Channel.choiRank (diagonalMap s₁ s₂ s₃) =
      Fintype.card (diagonalBellSupport s₁ s₂ s₃) := by
  classical
  let c : ℂ := 1 / ((2 : ℝ).sqrt : ℂ)
  let v : Fin 4 → (Fin 2 × Fin 2) → ℂ :=
    fun j p ↦ c * diagonalKraus s₁ s₂ s₃ j p.1 p.2
  let supportV : diagonalBellSupport s₁ s₂ s₃ → (Fin 2 × Fin 2) → ℂ :=
    fun j ↦ v j.1
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hcoeff : ∀ i : diagonalBellSupport s₁ s₂ s₃,
      ((diagonalKrausCoefficient s₁ s₂ s₃ i.1 : ℝ) : ℂ) ≠ 0 := by
    intro i
    apply Complex.ofReal_ne_zero.mpr
    rw [diagonalKrausCoefficient, Real.sqrt_ne_zero']
    exact lt_of_le_of_ne (hweight i.1) (Ne.symm i.2)
  have hK : LinearIndependent ℂ
      (fun i : diagonalBellSupport s₁ s₂ s₃ ↦
        diagonalKraus s₁ s₂ s₃ i.1) := by
    have hrestricted := pauliMatrices_linearIndependent.comp
      (fun i : diagonalBellSupport s₁ s₂ s₃ ↦ i.1) Subtype.val_injective
    rw [Fintype.linearIndependent_iff] at hrestricted ⊢
    intro g hg i
    have hproduct := hrestricted
      (fun j ↦ g j * (diagonalKrausCoefficient s₁ s₂ s₃ j.1 : ℂ)) (by
        calc
          ∑ j, (g j * (diagonalKrausCoefficient s₁ s₂ s₃ j.1 : ℂ)) •
              pauliMatrices j.1 =
              ∑ j, g j • diagonalKraus s₁ s₂ s₃ j.1 := by
                apply Finset.sum_congr rfl
                intro j _
                change (g j * (diagonalKrausCoefficient s₁ s₂ s₃ j.1 : ℂ)) •
                    pauliMatrices j.1 =
                  g j • ((diagonalKrausCoefficient s₁ s₂ s₃ j.1 : ℂ) •
                    pauliMatrices j.1)
                rw [smul_smul]
          _ = 0 := hg) i
    exact (mul_eq_zero.mp hproduct).resolve_right (hcoeff i)
  have hv : LinearIndependent ℂ supportV := by
    rw [Fintype.linearIndependent_iff] at hK ⊢
    intro g hg i
    apply hK g _ i
    apply Matrix.ext
    intro a b
    have hab := congrFun hg (a, b)
    have hentry :
        c * (∑ j, g j * diagonalKraus s₁ s₂ s₃ j.1 a b) = 0 := by
      simpa [supportV, v, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hab
    rw [Matrix.sum_apply, show (0 : QubitMatrix) a b = 0 by rfl]
    simpa only [Matrix.smul_apply, smul_eq_mul] using
      (mul_eq_zero.mp hentry).resolve_left hc
  have hsum :
      ∑ i : Fin 4, Matrix.vecMulVec (v i) (star (v i)) =
        ∑ i : diagonalBellSupport s₁ s₂ s₃,
          Matrix.vecMulVec (supportV i) (star (supportV i)) := by
    let f : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      fun i ↦ Matrix.vecMulVec (v i) (star (v i))
    have hfiltered :
        ∑ i ∈ Finset.univ.filter
              (fun i ↦ diagonalBellWeight s₁ s₂ s₃ i ≠ 0), f i =
          ∑ i : Fin 4, f i := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have hzero : diagonalBellWeight s₁ s₂ s₃ i = 0 := by
        simpa using hi
      ext p q
      simp [f, v, diagonalKraus, diagonalKrausCoefficient, hzero,
        Matrix.vecMulVec_apply]
    calc
      ∑ i : Fin 4, Matrix.vecMulVec (v i) (star (v i)) = ∑ i : Fin 4, f i := rfl
      _ = ∑ i ∈ Finset.univ.filter
            (fun i ↦ diagonalBellWeight s₁ s₂ s₃ i ≠ 0), f i := hfiltered.symm
      _ = ∑ i : diagonalBellSupport s₁ s₂ s₃, f i.1 := by
        simpa [diagonalBellSupport] using
          (Finset.sum_subtype
            (Finset.univ.filter
              (fun i ↦ diagonalBellWeight s₁ s₂ s₃ i ≠ 0))
            (fun i ↦ by simp) f)
      _ = ∑ i : diagonalBellSupport s₁ s₂ s₃,
          Matrix.vecMulVec (supportV i) (star (supportV i)) := rfl
  change (ChoiJamiolkowski.choiMatrix
    (Kraus.mapLM (diagonalKraus s₁ s₂ s₃))).rank = _
  rw [Channel.choiMatrix_mapLM_eq_sum_vecMulVec]
  change (∑ i : Fin 4, Matrix.vecMulVec (v i) (star (v i))).rank = _
  rw [hsum]
  exact rank_sum_vecMulVec_eq_card_of_linearIndependent supportV hv

private theorem nonDiagonalKrausBase_linearIndependent :
    LinearIndependent ℂ nonDiagonalKrausBase := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h00 := congrArg (fun M : QubitMatrix ↦ M 0 0) hg
  have h11 := congrArg (fun M : QubitMatrix ↦ M 1 1) hg
  have h01 := congrArg (fun M : QubitMatrix ↦ M 0 1) hg
  simp [Fin.sum_univ_three, nonDiagonalKrausBase] at h00 h11 h01
  have hsqrt : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by positivity
  field_simp [hsqrt] at h11
  have hg0 : g 0 = 0 := by linear_combination (h00 + h11) / 2
  have hg1 : g 1 = 0 := by linear_combination (h00 - h11) / 2
  fin_cases i
  · exact hg0
  · exact hg1
  · exact h01

private theorem nonDiagonalKraus_linearIndependent {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    LinearIndependent ℂ (nonDiagonalKraus x) := by
  have hcoeff : ∀ i : Fin 3, ((nonDiagonalKrausCoefficient x i : ℝ) : ℂ) ≠ 0 := by
    intro i
    apply Complex.ofReal_ne_zero.mpr
    fin_cases i
    · apply Real.sqrt_ne_zero'.2
      nlinarith
    · apply Real.sqrt_ne_zero'.2
      nlinarith
    · apply Real.sqrt_ne_zero'.2
      norm_num
  let u : Fin 3 → ℂˣ := fun i ↦ Units.mk0 _ (hcoeff i)
  have hli := nonDiagonalKrausBase_linearIndependent.units_smul u
  have heq : u • nonDiagonalKrausBase = nonDiagonalKraus x := by
    ext i a b
    rfl
  rw [← heq]
  exact hli

/-- For `0 ≤ x < 1`, all three operators in Equation (19) are needed:
the canonical non-diagonal channel has Choi/Kraus rank three. -/
theorem choiRank_nonDiagonalMap_eq_three {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Channel.choiRank (nonDiagonalMap x) = 3 :=
  choiRank_mapLM_eq_card_of_linearIndependent _
    (nonDiagonalKraus_linearIndependent hx0 hx1)

/-- The two nonzero Kraus operators left by Equation (19) at `x = 1`. -/
def nonDiagonalBoundaryKraus : Fin 2 → QubitMatrix
  | 0 => nonDiagonalKraus 1 0
  | 1 => nonDiagonalKraus 1 2

/-- The middle operator in Equation (19) vanishes at the endpoint `x = 1`. -/
@[simp] theorem nonDiagonalKraus_one_one : nonDiagonalKraus 1 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nonDiagonalKraus, nonDiagonalKrausCoefficient]

/-- At `x = 1`, the middle operator in Equation (19) vanishes and the
three-operator map equals the displayed two-nonzero-operator map. -/
theorem nonDiagonalMap_one_eq_boundaryMap :
    nonDiagonalMap 1 = Kraus.mapLM nonDiagonalBoundaryKraus := by
  apply LinearMap.ext
  intro X
  simp [nonDiagonalMap, Kraus.map_apply, Fin.sum_univ_three,
    Fin.sum_univ_two, nonDiagonalBoundaryKraus, nonDiagonalKraus,
    nonDiagonalKrausCoefficient]
  norm_cast

private theorem nonDiagonalBoundaryKraus_linearIndependent :
    LinearIndependent ℂ nonDiagonalBoundaryKraus := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h00 := congrArg (fun M : QubitMatrix ↦ M 0 0) hg
  have h01 := congrArg (fun M : QubitMatrix ↦ M 0 1) hg
  have hg0 : g 0 = 0 := by
    simpa [Fin.sum_univ_two, nonDiagonalBoundaryKraus, nonDiagonalKraus,
      nonDiagonalKrausCoefficient, nonDiagonalKrausBase] using h00
  have hg1 : g 1 = 0 := by
    simpa [Fin.sum_univ_two, nonDiagonalBoundaryKraus, nonDiagonalKraus,
      nonDiagonalKrausCoefficient, nonDiagonalKrausBase] using h01
  fin_cases i
  · exact hg0
  · exact hg1

/-- At the endpoint `x = 1`, the canonical non-diagonal channel has
Choi/Kraus rank two, as stated in Wolf, Proposition 2.11. -/
theorem choiRank_nonDiagonalMap_one :
    Channel.choiRank (nonDiagonalMap 1) = 2 := by
  rw [nonDiagonalMap_one_eq_boundaryMap]
  exact choiRank_mapLM_eq_card_of_linearIndependent _
    nonDiagonalBoundaryKraus_linearIndependent

/-! ## The singular constant-output representative -/

/-- The two Kraus operators of the singular representative:
`|0><0|` and `|0><1|`. -/
def singularKraus : Fin 2 → QubitMatrix
  | 0 => !![1, 0; 0, 0]
  | 1 => !![0, 1; 0, 0]

/-- The singular qubit channel from the third normal form in
Verstraete--Verschelde, Equation (17), and Wolf, Proposition 2.11 case 3. -/
def singularMap : QubitMap :=
  Kraus.mapLM singularKraus

/-- The singular two-operator family is trace preserving. -/
theorem singularKraus_isTP : Kraus.IsTP singularKraus := by
  rw [Kraus.IsTP]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [singularKraus, Fin.sum_univ_two, Matrix.mul_apply,
      Matrix.conjTranspose_apply]

/-- The singular representative is a channel. -/
theorem singularMap_isChannel : IsChannel singularMap :=
  Kraus.isChannel_mapLM _ singularKraus_isTP

/-- Exact action of the singular representative on arbitrary matrices.
On density matrices this is the constant output `|0><0|`; on arbitrary
matrices the output is scaled by the input trace. -/
theorem singularMap_apply (X : QubitMatrix) :
    singularMap X = Matrix.trace X • !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singularMap, Kraus.map_apply, singularKraus, Fin.sum_univ_two,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      Matrix.trace_fin_two]

/-- Exact Pauli-transfer matrix of the singular representative in Wolf,
Proposition 2.11 case 3. -/
theorem pauliTransferMatrix_singularMap :
    pauliTransferMatrix singularMap =
      !![1, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, 0;
         1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliTransferMatrix, pauliTransferEntry, singularMap_apply,
      pauliMatrices, Matrix.trace_fin_two, Matrix.mul_apply]

/-- The singular map satisfies the existing singular normal-form predicate. -/
theorem isLorentzSingular_singularMap : IsLorentzSingular singularMap := by
  refine ⟨singularMap_isChannel, ?_, ?_⟩
  · have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 3 0)
      pauliTransferMatrix_singularMap
    simpa [pauliTransferMatrix] using h
  · intro i j hij
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M i j)
      pauliTransferMatrix_singularMap
    fin_cases i <;> fin_cases j <;> simp_all [pauliTransferMatrix]

private theorem singularKraus_linearIndependent :
    LinearIndependent ℂ singularKraus := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h00 := congrArg (fun M : QubitMatrix ↦ M 0 0) hg
  have h01 := congrArg (fun M : QubitMatrix ↦ M 0 1) hg
  have hg0 : g 0 = 0 := by
    simpa [Fin.sum_univ_two, singularKraus] using h00
  have hg1 : g 1 = 0 := by
    simpa [Fin.sum_univ_two, singularKraus] using h01
  fin_cases i
  · exact hg0
  · exact hg1

/-- The singular constant-output channel has Choi/Kraus rank two. -/
theorem choiRank_singularMap : Channel.choiRank singularMap = 2 :=
  choiRank_mapLM_eq_card_of_linearIndependent _ singularKraus_linearIndependent

end Wolf
