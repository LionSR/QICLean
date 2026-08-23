/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.LorentzNormalForm.QubitNormalForm
import QICLean.Channel.PositiveExamples
import QICLean.Channel.Semigroup.CPClosure

/-!
# Pauli-block truncation of qubit maps

This module formalizes the forward implications in Wolf Proposition 2.10,
following Equation (2.39) in Section 2.4.  Qubit Pauli time reversal is
the reduction map `Θ(X) = tr(X) 1 - X`; averaging a map with its double
time-reversal sandwich deletes precisely the two off-diagonal blocks of its
Pauli transfer matrix.  Positivity and complete positivity are preserved.

## References

* `Notes/WolfNoteTexSource/ch02_representations.tex`, Section 2.4,
  Proposition 2.10, lines 984--998. Only the forward implications actually
  proved in lines 992--998 are formalized here.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset

namespace Wolf

private abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ
private abbrev QubitMap := QubitMatrix →ₗ[ℂ] QubitMatrix

/-- Qubit Pauli time reversal, `Θ(X) = tr(X) 1 - X`, realized by the existing
reduction map `Matrix.reductionMap 2 1`.

Source: `Notes/WolfNoteTexSource/ch02_representations.tex`, Section 2.4,
Proposition 2.10, lines 984--998. -/
noncomputable def pauliTimeReversal : QubitMap :=
  Matrix.reductionMap 2 1

/-- The Pauli-block truncation
`T' = (1/2) • (T + Θ ∘ T ∘ Θ)` from Wolf's proof. -/
noncomputable def pauliBlockDiagonalTruncation (T : QubitMap) : QubitMap :=
  ((1 / 2 : ℂ) •
    (T + pauliTimeReversal.comp (T.comp pauliTimeReversal)))

/-- Pauli time reversal fixes `σ₀`. -/
@[simp] theorem pauliTimeReversal_pauli_zero :
    pauliTimeReversal (pauliMatrices 0) = pauliMatrices 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliTimeReversal, Matrix.reductionMap_apply, pauliMatrices,
      Matrix.trace_fin_two]

/-- Pauli time reversal negates every nonidentity Pauli matrix. -/
theorem pauliTimeReversal_pauli_ne_zero (i : Fin 4) (hi : i ≠ 0) :
    pauliTimeReversal (pauliMatrices i) = -pauliMatrices i := by
  fin_cases i <;> simp_all [pauliTimeReversal, Matrix.reductionMap_apply,
    pauliMatrices, Matrix.trace_fin_two]

/-- The diagonal entries of `D = diag(1,-1,-1,-1)`, the Pauli transfer
matrix of qubit time reversal. -/
def pauliTimeReversalDiagonal (i : Fin 4) : ℂ :=
  if i = 0 then 1 else -1

private theorem pauliTimeReversal_pauli (i : Fin 4) :
    pauliTimeReversal (pauliMatrices i) =
      pauliTimeReversalDiagonal i • pauliMatrices i := by
  by_cases hi : i = 0
  · subst i
    simp [pauliTimeReversalDiagonal]
  · simp [pauliTimeReversalDiagonal, hi, pauliTimeReversal_pauli_ne_zero i hi]

/-- Entrywise form of Wolf's identity `D T̂ D`, where
`D = diag(1,-1,-1,-1)` is the Pauli matrix of time reversal. -/
theorem pauliTransferEntry_timeReversal_comp (T : QubitMap) (i j : Fin 4) :
    pauliTransferEntry (pauliTimeReversal.comp (T.comp pauliTimeReversal)) i j =
      pauliTimeReversalDiagonal i * pauliTransferEntry T i j * pauliTimeReversalDiagonal j := by
  rw [pauliTransferEntry, LinearMap.comp_apply, LinearMap.comp_apply,
    pauliTimeReversal_pauli]
  simp only [map_smul]
  rw [pauliTimeReversal_pauli]
  simp [pauliTransferEntry, Matrix.smul_mul, Matrix.trace_smul, mul_assoc, mul_comm,
    mul_left_comm]

/-- The truncation keeps the `(0,0)` entry and the lower-right `3 × 3` Pauli
block, and zeros the two off-diagonal blocks.  This is the public entrywise
summary of `(T̂ + D T̂ D)/2 = T̂₀₀ ⊕ Δ`.

Source: `Notes/WolfNoteTexSource/ch02_representations.tex`, Section 2.4,
Proposition 2.10, lines 984--998. -/
theorem pauliTransferEntry_pauliBlockDiagonalTruncation (T : QubitMap) (i j : Fin 4) :
    pauliTransferEntry (pauliBlockDiagonalTruncation T) i j =
      if (i = 0 ↔ j = 0) then pauliTransferEntry T i j else 0 := by
  rw [pauliBlockDiagonalTruncation, pauliTransferEntry]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Matrix.mul_add, Matrix.trace_add,
    smul_eq_mul, Matrix.smul_mul, Matrix.trace_smul]
  rw [show ((1 : ℂ) / 2) * ((1 : ℂ) / 2) = 1 / 4 by norm_num]
  change 1 / 4 * (Matrix.trace (pauliMatrices i * T (pauliMatrices j)) +
    Matrix.trace (pauliMatrices i *
      (pauliTimeReversal.comp (T.comp pauliTimeReversal)) (pauliMatrices j))) = _
  rw [show Matrix.trace (pauliMatrices i *
      (pauliTimeReversal.comp (T.comp pauliTimeReversal)) (pauliMatrices j)) =
      2 * (pauliTimeReversalDiagonal i * pauliTransferEntry T i j *
        pauliTimeReversalDiagonal j) by
    rw [pauliTransferEntry_timeReversal_comp]
    simp [pauliTransferEntry]]
  rw [show Matrix.trace (pauliMatrices i * T (pauliMatrices j)) =
      2 * pauliTransferEntry T i j by simp [pauliTransferEntry]]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [pauliTimeReversalDiagonal, hi, hj]

/-- Pauli time reversal is positive. -/
theorem pauliTimeReversal_isPositiveMap : IsPositiveMap pauliTimeReversal := by
  simpa [pauliTimeReversal] using
    (Matrix.reductionMap_one_isPositiveMap (D := 2))

private theorem isPositiveMap_comp {S T : QubitMap}
    (hS : IsPositiveMap S) (hT : IsPositiveMap T) : IsPositiveMap (S.comp T) := by
  intro X hX
  exact hS _ (hT X hX)

private theorem isPositiveMap_add {S T : QubitMap}
    (hS : IsPositiveMap S) (hT : IsPositiveMap T) : IsPositiveMap (S + T) := by
  intro X hX
  simpa using (hS X hX).add (hT X hX)

/-- The forward positivity implication actually proved in Wolf Proposition 2.10:
if `T` is positive, deleting its two off-diagonal Pauli blocks by time-reversal
averaging remains positive. The source's Hermiticity-preserving hypothesis is
retained explicitly.

Source: `Notes/WolfNoteTexSource/ch02_representations.tex`, Section 2.4,
Proposition 2.10, lines 984--998. -/
theorem pauliBlockDiagonalTruncation_isPositiveMap
    (T : QubitMap)
    (_hHerm : ∀ X : QubitMatrix, X.IsHermitian → (T X).IsHermitian)
    (hT : IsPositiveMap T) : IsPositiveMap (pauliBlockDiagonalTruncation T) := by
  rw [pauliBlockDiagonalTruncation]
  have hsandwich : IsPositiveMap (pauliTimeReversal.comp (T.comp pauliTimeReversal)) :=
    isPositiveMap_comp pauliTimeReversal_isPositiveMap
      (isPositiveMap_comp hT pauliTimeReversal_isPositiveMap)
  intro X hX
  simpa [LinearMap.smul_apply] using
    (isPositiveMap_add hT hsandwich X hX).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)

private theorem pauliTimeReversal_singleKraus_sandwich
    (A X : QubitMatrix) :
    pauliTimeReversal (A * pauliTimeReversal X * Aᴴ) =
      (pauliMatrices 2 * A.map star * pauliMatrices 2) * X *
        (pauliMatrices 2 * A.map star * pauliMatrices 2)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliTimeReversal, Matrix.reductionMap_apply, pauliMatrices,
      Matrix.trace_fin_two, Matrix.mul_apply]
    <;> ring

private theorem pauliTimeReversal_comp_comp_isCPMap
    {T : QubitMap} (hT : IsCPMap T) :
    IsCPMap (pauliTimeReversal.comp (T.comp pauliTimeReversal)) := by
  obtain ⟨r, K, hK⟩ := hT
  refine ⟨r, fun i => pauliMatrices 2 * (K i).map star * pauliMatrices 2, ?_⟩
  intro X
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hK, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact pauliTimeReversal_singleKraus_sandwich (K i) X

/-- The forward complete-positivity implication actually proved in Wolf
Proposition 2.10. Although time reversal itself is not completely positive,
its double sandwich around a Kraus map has Kraus
operators `σ₂ · conj(Kᵢ) · σ₂`; CP is then preserved by addition and the
nonnegative scalar factor `1/2`.  The source's Hermiticity-preserving
hypothesis is retained explicitly.

Source: `Notes/WolfNoteTexSource/ch02_representations.tex`, Section 2.4,
Proposition 2.10, lines 984--998.  This theorem is
only the forward implication actually proved there; no converse is asserted. -/
theorem pauliBlockDiagonalTruncation_isCPMap
    (T : QubitMap)
    (_hHerm : ∀ X : QubitMatrix, X.IsHermitian → (T X).IsHermitian)
    (hT : IsCPMap T) : IsCPMap (pauliBlockDiagonalTruncation T) := by
  rw [pauliBlockDiagonalTruncation]
  exact (hT.add (pauliTimeReversal_comp_comp_isCPMap hT)).smul_nonneg (by norm_num)

end Wolf
