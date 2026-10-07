import QICLean.Analysis.ShiftedDensityPowers

/-! Regressions for genuine density matrices, including singular densities and zero exponents. -/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

example : IsCompact {A : Matrix Empty Empty ℂ | A.PosSemidef ∧ A.trace = 1} :=
  Matrix.isCompact_setOf_posSemidef_trace_eq_one

example : ¬ Set.Nonempty {A : Matrix Empty Empty ℂ | A.PosSemidef ∧ A.trace = 1} := by
  rintro ⟨A, _, ht⟩
  simp [Matrix.trace] at ht

example : Set.Nonempty {A : Matrix Unit Unit ℂ | A.PosSemidef ∧ A.trace = 1} :=
  Matrix.setOf_posSemidef_trace_eq_one_nonempty

private def singularDensity : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 0]

private theorem singularDensity_psd : singularDensity.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

private theorem singularDensity_trace : singularDensity.trace = 1 := by
  norm_num [singularDensity, Matrix.trace, Fin.sum_univ_two]

example : singularDensity.det = 0 := by
  norm_num [singularDensity, Matrix.det_fin_two]

example {b : ℝ} (hb : 0 < b) : (singularDensity + b • 1).PosDef :=
  singularDensity_psd.add_smul_one_posDef hb

example {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) :
    ‖(singularDensity + b • 1) ^ (-a / 2)‖ ≤ b ^ (-a / 2) :=
  singularDensity_psd.l2_opNorm_add_smul_one_rpow_le_of_nonpos singularDensity_trace hb
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (by norm_num))

example {b : ℝ} (hb : 0 < b) : (singularDensity + b • 1) ^ (0 : ℝ) = 1 :=
  CFC.rpow_zero _ (singularDensity_psd.add_smul_one_posDef hb).posSemidef.nonneg

example {b : ℝ} (hb : 0 < b) (r : ℝ) :
    (singularDensity + b • 1) ^ r * (singularDensity + b • 1) ^ (-r) = 1 :=
  CFC.rpow_mul_rpow_neg _ (singularDensity_psd.add_smul_one_posDef hb).isStrictlyPositive

example {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) :
    ‖(singularDensity + b • 1) ^ (a / 2)‖ ≤ (1 + b) ^ (a / 2) :=
  singularDensity_psd.l2_opNorm_add_smul_one_rpow_le_of_nonneg singularDensity_trace hb
    (div_nonneg ha (by norm_num))

example {b : ℝ} (hb : 0 < b) (r : ℝ) :
    ContinuousOn (fun A : Matrix (Fin 2) (Fin 2) ℂ ↦ (A + b • 1) ^ r)
      {A | A.PosSemidef ∧ A.trace = 1} :=
  (Matrix.continuousOn_add_smul_one_rpow hb r).mono fun _ h ↦ h.1
