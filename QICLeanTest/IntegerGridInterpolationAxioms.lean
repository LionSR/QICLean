/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.IntegerGridInterpolation
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NormNum

/-!
# Matrix applications of integer-grid interpolation

The first two applications recover a nonzero constant matrix at cutoff zero
and with no coordinates. The third recovers the dependent coefficient family
I₂, 2I₂ from its polynomial values I₂ and 3I₂ at zero and one.
-/

open scoped BigOperators

namespace FiniteScalarInterpolation

/-- At cutoff zero, the actual constant nonzero matrix is recovered from its single sample. -/
private theorem integerGrid_zeroCutoff_matrix_application :
    let I2 : Matrix (Fin 2) (Fin 2) ℂ := 1
    let alpha0 : Fin 1 → Fin 1 := fun _ ↦ 0
    (∑ g : Fin 1 → Fin 1, integerRecoveryGrid (Fin 1) 0 alpha0 g • I2) = I2 ∧ I2 ≠ 0 := by
  classical
  let I2 : Matrix (Fin 2) (Fin 2) ℂ := 1
  let alpha0 : Fin 1 → Fin 1 := fun _ ↦ 0
  have heval (g : Fin 1 → Fin 1) :
      (∑ beta : Fin 1 → Fin 1,
        integerEvaluationGrid (Fin 1) 0 g beta • I2) = I2 := by
    rw [Fintype.sum_subsingleton _ alpha0]
    simp [integerEvaluationGrid, alpha0]
  have h := integerRecoveryGrid_smul (Fin 1) 0 (fun _ ↦ I2) alpha0
  have hEq : (fun a b : Fin 1 ↦ Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq (Fin 1)) := Subsingleton.elim _ _
  rw [hEq] at h
  have hsum := congrArg
    (fun E : (Fin 1 → Fin 1) → Matrix (Fin 2) (Fin 2) ℂ ↦
      ∑ g, integerRecoveryGrid (Fin 1) 0 alpha0 g • E g) (funext heval)
  exact ⟨hsum.symm.trans h, one_ne_zero⟩

/-- With no coordinates, the actual nonzero constant matrix is recovered even at positive cutoff. -/
private theorem integerGrid_emptyCoordinates_matrix_application :
    let I2 : Matrix (Fin 2) (Fin 2) ℂ := 1
    let alpha0 : Fin 0 → Fin 3 := Fin.elim0
    (∑ g : Fin 0 → Fin 3, integerRecoveryGrid (Fin 0) 2 alpha0 g • I2) = I2 ∧ I2 ≠ 0 := by
  classical
  let I2 : Matrix (Fin 2) (Fin 2) ℂ := 1
  let alpha0 : Fin 0 → Fin 3 := Fin.elim0
  have heval (g : Fin 0 → Fin 3) :
      (∑ beta : Fin 0 → Fin 3,
        integerEvaluationGrid (Fin 0) 2 g beta • I2) = I2 := by
    rw [Fintype.sum_subsingleton _ alpha0]
    simp [integerEvaluationGrid]
  have h := integerRecoveryGrid_smul (Fin 0) 2 (fun _ ↦ I2) alpha0
  have hsum := congrArg
    (fun E : (Fin 0 → Fin 3) → Matrix (Fin 2) (Fin 2) ℂ ↦
      ∑ g, integerRecoveryGrid (Fin 0) 2 alpha0 g • E g) (funext heval)
  exact ⟨hsum.symm.trans h, one_ne_zero⟩

/-- The dependent coefficients I₂ and 2I₂ give the sampled polynomial (1+2z)I₂.
The specified grid recovers the nonzero linear coefficient from its actual
samples I₂ and 3I₂ at the nodes zero and one. This illustrates the scalar
interpolation used in AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 626–644,
and ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem integerGrid_dependent_linear_matrix_application :
    let I2 : Matrix (Fin 2) (Fin 2) ℂ := 1
    let f : (Fin 1 → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ :=
      fun beta ↦ if beta 0 = 0 then I2 else (2 : ℂ) • I2
    let g0 : Fin 1 → Fin 2 := fun _ ↦ 0
    let g1 : Fin 1 → Fin 2 := fun _ ↦ 1
    let sample := fun g : Fin 1 → Fin 2 ↦
      ∑ beta : Fin 1 → Fin 2, integerEvaluationGrid (Fin 1) 1 g beta • f beta
    (∀ g, sample g = ((1 : ℂ) + 2 * integerNode 1 (g 0)) • I2) ∧
      sample g0 = I2 ∧ sample g1 = (3 : ℂ) • I2 ∧
      (∑ g : Fin 1 → Fin 2, integerRecoveryGrid (Fin 1) 1 g1 g •
        (((1 : ℂ) + 2 * integerNode 1 (g 0)) • I2)) = (2 : ℂ) • I2 ∧
      (2 : ℂ) • I2 ≠ 0 := by
  classical
  let I2 : Matrix (Fin 2) (Fin 2) ℂ := 1
  let f : (Fin 1 → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ :=
    fun beta ↦ if beta 0 = 0 then I2 else (2 : ℂ) • I2
  let g0 : Fin 1 → Fin 2 := fun _ ↦ 0
  let g1 : Fin 1 → Fin 2 := fun _ ↦ 1
  let sample := fun g : Fin 1 → Fin 2 ↦
    ∑ beta : Fin 1 → Fin 2, integerEvaluationGrid (Fin 1) 1 g beta • f beta
  let e : (Fin 1 → Fin 2) ≃ Fin 2 := Equiv.funUnique (Fin 1) (Fin 2)
  have hsample (g : Fin 1 → Fin 2) :
      sample g = ((1 : ℂ) + 2 * integerNode 1 (g 0)) • I2 := by
    calc
      sample g = (1 : ℂ) • I2 + integerNode 1 (g 0) • ((2 : ℂ) • I2) := by
        change (∑ beta : Fin 1 → Fin 2,
          integerEvaluationGrid (Fin 1) 1 g beta • f beta) = _
        rw [← e.symm.sum_comp
          (fun beta ↦ integerEvaluationGrid (Fin 1) 1 g beta • f beta)]
        simp [e, integerEvaluationGrid, f]
      _ = ((1 : ℂ) + 2 * integerNode 1 (g 0)) • I2 := by
        rw [smul_smul, ← add_smul, mul_comm (integerNode 1 (g 0)) (2 : ℂ)]
  have hsample0 : sample g0 = I2 := by
    have h := hsample g0
    norm_num [integerNode, g0] at h
    exact h
  have hsample1 : sample g1 = (3 : ℂ) • I2 := by
    have h := hsample g1
    norm_num [integerNode, g1] at h
    exact h
  have hrecovery :
      (∑ g : Fin 1 → Fin 2, integerRecoveryGrid (Fin 1) 1 g1 g •
        (((1 : ℂ) + 2 * integerNode 1 (g 0)) • I2)) = (2 : ℂ) • I2 := by
    have h := integerRecoveryGrid_smul (Fin 1) 1 f g1
    have hEq : (fun a b : Fin 1 ↦ Classical.propDecidable (a = b)) =
        (inferInstance : DecidableEq (Fin 1)) := Subsingleton.elim _ _
    rw [hEq] at h
    have hsum := congrArg
      (fun E : (Fin 1 → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ ↦
        ∑ g, integerRecoveryGrid (Fin 1) 1 g1 g • E g) (funext hsample)
    exact hsum.symm.trans h
  have hnonzero : (2 : ℂ) • I2 ≠ 0 := by
    intro hzero
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 0 0) hzero
    norm_num [I2, Matrix.smul_apply] at hentry
  exact ⟨hsample, hsample0, hsample1, hrecovery, hnonzero⟩

end FiniteScalarInterpolation

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``FiniteScalarInterpolation.integerRecovery_sum,
    ``FiniteScalarInterpolation.integerRecoveryGrid_mul_integerEvaluationGrid,
    ``FiniteScalarInterpolation.integerRecoveryGrid_smul,
    ``FiniteScalarInterpolation.integerGrid_zeroCutoff_matrix_application,
    ``FiniteScalarInterpolation.integerGrid_emptyCoordinates_matrix_application,
    ``FiniteScalarInterpolation.integerGrid_dependent_linear_matrix_application] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
