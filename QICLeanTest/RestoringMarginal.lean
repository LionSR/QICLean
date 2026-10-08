/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RestoringMarginal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Concrete singular references and noncommuting projection consumers. -/

open scoped Matrix MatrixOrder ComplexOrder Kronecker

namespace RestoringMarginalTest

private def p0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
private noncomputable def plus : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

private theorem p0_projection : IsStarProjection p0 := by
  constructor
  · change p0 * p0 = p0
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [p0, Matrix.mul_apply, Fin.sum_univ_two]
  · change p0ᴴ = p0
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [p0, Matrix.conjTranspose_apply]

private theorem plus_projection : IsStarProjection plus := by
  constructor
  · change plus * plus = plus
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [plus, Matrix.mul_apply, Fin.sum_univ_two]
  · change plusᴴ = plus
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [plus, Matrix.conjTranspose_apply]

private noncomputable def rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℂ) • (p0 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))

private noncomputable def selected : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ plus

private theorem selected_projection : IsStarProjection selected := by
  constructor
  · change selected * selected = selected
    simp only [selected, ← Matrix.mul_kronecker_mul, one_mul,
      plus_projection.isIdempotentElem.eq]
  · change selectedᴴ = selected
    simpa only [selected, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      Matrix.star_eq_conjTranspose] using
      congrArg ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ·)
        plus_projection.isSelfAdjoint.star_eq

private theorem rho_posSemidef : rho.PosSemidef := by
  exact ((Matrix.nonneg_iff_posSemidef.mp p0_projection.nonneg).kronecker
    Matrix.PosSemidef.one).smul (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1 / 2)

private theorem rho_commute_selected : Commute rho selected := by
  change rho * selected = selected * rho
  simp only [rho, selected, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_kronecker_mul, one_mul, mul_one]

-- The two selected projections genuinely fail to commute, while the
-- reference commutes with its selected spectral projection.
example : ¬ Commute selected ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ p0) := by
  intro h
  have hh := congrArg (fun A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ =>
    A (0, 0) (0, 1)) h.eq
  norm_num [selected, plus, p0, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply] at hh

-- The actual partial-trace expression is positive and below the marginal;
-- there is no assumption of commutation between the two projections.
example : 0 ≤ Matrix.restoringMarginal rho selected p0 ∧
    Matrix.restoringMarginal rho selected p0 ≤ Matrix.partialTraceRight rho := by
  exact ⟨Matrix.restoringMarginal_nonneg rho_posSemidef selected_projection
      rho_commute_selected p0_projection,
    Matrix.restoringMarginal_le rho_posSemidef selected_projection
      rho_commute_selected p0_projection⟩

-- The reference is normalized and has a singular retained marginal.
example : rho.trace = 1 ∧ Matrix.partialTraceRight rho = p0 := by
  constructor
  · norm_num [rho, p0, Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rho, p0, Matrix.partialTraceRight_apply, Fin.sum_univ_two,
        Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply]

-- This numerical coefficient catches a missing projection or partial-trace factor.
example : Matrix.restoringMarginal rho selected p0 = (1 / 4 : ℂ) • p0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.restoringMarginal, rho, selected, plus, p0,
      Matrix.partialTraceRight_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply]

-- An empty traced factor gives a zero reduced matrix without a positive-dimension premise.
example (ρ Q : Matrix (Fin 2 × Fin 0) (Fin 2 × Fin 0) ℂ)
    (T : Matrix (Fin 0) (Fin 0) ℂ) : Matrix.restoringMarginal ρ Q T = 0 := by
  ext i j
  simp [Matrix.restoringMarginal, Matrix.partialTraceRight_apply]

end RestoringMarginalTest
