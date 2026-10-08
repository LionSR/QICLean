/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RestoringNorm

/-! Singular, complex-blank, and empty-system consumers of the actual norm bounds. -/

open Matrix Entropy
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RestoringNormTest

private noncomputable def singularState : Matrix (Bool × Fin 1) (Bool × Fin 1) ℂ :=
  blankOuterProduct (Pi.single (false, 0) 1)

private theorem singularState_projection : IsStarProjection singularState := by
  exact blankOuterProduct_isStarProjection _ (by simp)

private theorem singularState_partialTrace : partialTraceLeft singularState = 1 := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp [singularState, partialTraceLeft_apply, blankOuterProduct, vecMulVec_apply]

/-- The physical state has a zero-probability coordinate. -/
example : singularState (true, 0) (true, 0) = 0 := by
  simp [singularState, blankOuterProduct, vecMulVec_apply]

/-- The actual weighted sum attains the unit bound despite the zero eigenvalue. -/
example : restoringGram {false} (fun x : Bool ↦ if x then 0 else 1)
    singularState (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp [restoringGram, restoringBlock, singularState, blankOuterProduct, vecMulVec_apply]

/-- The source exponential bound applies to both actual operators for a singular
state, including an arbitrary complex phase in the blanks. -/
example :
    ‖restoringOperator {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single false Complex.I) (Pi.single false 1)
      singularState (1 : Matrix (Fin 1) (Fin 1) ℂ)‖ ≤ 1 ∧
    ‖columnOperator {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single false Complex.I) (Pi.single false Complex.I)
      singularState (1 : Matrix (Fin 1) (Fin 1) ℂ)‖ ≤ 1 := by
  have h := restoringOperators_norm_le_exp {false} (fun x : Bool ↦ if x then 0 else 1)
    (by simp) (Pi.single false Complex.I) (Pi.single false 1) (Pi.single false Complex.I)
    (by simp) (by simp) (by simp) singularState_projection
    (IsStarProjection.one (Matrix (Fin 1) (Fin 1) ℂ))
    0 0 0 0 0 (by norm_num) (by simp) (ρ := singularState) (by simp)
    (by simp [singularState_partialTrace])
  simpa using h

/-- Empty physical systems do not require an artificial `Nonempty` assumption. -/
example :
    ‖restoringOperator ∅ (fun _ : Bool ↦ 0) (Pi.single false 1) (Pi.single false 1)
      (0 : Matrix (Bool × Empty) (Bool × Empty) ℂ) 0‖ ≤ 0 := by
  have h := restoringOperator_norm_le ∅ (fun _ : Bool ↦ 0) (by simp)
    (Pi.single false 1) (Pi.single false 1) (by simp) (by simp)
    (IsStarProjection.zero (R := Matrix (Bool × Empty) (Bool × Empty) ℂ))
    (IsStarProjection.zero (R := Matrix Empty Empty ℂ))
    (cX := 0) (cQ := 0) (cY := 0) (by rfl) (by rfl) (by rfl)
    (by simp) (ρ := 0) (by simp) (by simp)
  simpa using h


private noncomputable def plusProjection : Matrix (Fin 1 × Bool) (Fin 1 × Bool) ℂ :=
  fun _ _ ↦ 1 / 2

private noncomputable def coordinateProjection : Matrix Bool Bool ℂ :=
  blankOuterProduct (Pi.single false 1)

private theorem plusProjection_projection : IsStarProjection plusProjection where
  isIdempotentElem := by
    ext i j
    norm_num [plusProjection, Matrix.mul_apply, Fintype.sum_prod_type]
  isSelfAdjoint := by
    ext i j
    norm_num [plusProjection, Matrix.conjTranspose_apply]

private theorem coordinateProjection_projection : IsStarProjection coordinateProjection :=
  blankOuterProduct_isStarProjection _ (by simp)

private theorem compressed_plus_marginal :
    coordinateProjection * partialTraceLeft plusProjection * coordinateProjection =
      (1 / 2 : ℝ) • coordinateProjection := by
  ext i j
  cases i <;> cases j <;>
    norm_num [coordinateProjection, plusProjection, blankOuterProduct, vecMulVec_apply,
      Matrix.mul_apply, partialTraceLeft_apply]

/-- The spectral projectors in this example genuinely do not commute. -/
example : ¬Commute plusProjection ((1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ
    coordinateProjection) := by
  intro h
  have hh := congrArg (fun A ↦ A (0, false) (0, true)) h.eq
  norm_num [plusProjection, coordinateProjection, blankOuterProduct, vecMulVec_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply] at hh

/-- The half-sized marginal improves the bound to `sqrt (1/2)` even though
`Q` and `I ⊗ T` do not commute. -/
example :
    ‖columnOperator {0} (fun _ : Fin 1 ↦ 1) (Pi.single 0 1) (Pi.single 0 1)
      plusProjection coordinateProjection‖ ≤ Real.sqrt (1 / 2) := by
  have h := columnOperator_norm_le {0} (fun _ : Fin 1 ↦ 1) (by simp)
    (Pi.single 0 1) (Pi.single 0 1) (by simp) (by simp)
    plusProjection_projection coordinateProjection_projection
    (cX := 1) (cQ := 1) (cY := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by simp) (ρ := plusProjection) (by simp) (le_of_eq compressed_plus_marginal)
  simpa using h

end RestoringNormTest
