import QICLean.Analysis.ShiftedDensityTruncation
import QICLean.Analysis.CfcConjugation

/-! Closed-threshold, singular, empty-space, and exponent regressions for spectral truncation. -/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

example (A : Matrix Empty Empty ℂ) (b r : ℝ) :
    A.shiftedPowerHead b r = 0 ∧ A.shiftedPowerTail b r = 0 :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

example (A : Matrix Empty Empty ℂ) (b : ℝ) : A.spectralProjectionGE b = 0 :=
  Subsingleton.elim _ _

example (A : Matrix Empty Empty ℂ) (hA : A.PosSemidef) {b r : ℝ}
    (hb : 0 < b) (hr : 0 ≤ r) : ‖A.shiftedPowerTail b r‖ ≤ (2 * b) ^ r :=
  hA.l2_opNorm_shiftedPowerTail_le hb hr

example {n : Type*} [Fintype n] [DecidableEq n] {b : ℝ} (hb : 0 < b) :
    (0 : Matrix n n ℂ).spectralProjectionGE b = 0 := by
  simp [spectralProjectionGE, not_le.mpr hb]

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) {b : ℝ} (hb : 0 < b) :
    A.shiftedPowerHead b 0 = A.spectralProjectionGE b ∧
      A.shiftedPowerTail b 0 = 1 - A.spectralProjectionGE b := by
  simp [shiftedPowerHead, shiftedPowerTail,
    CFC.rpow_zero _ (hA.add_smul_one_posDef hb).posSemidef.nonneg]

example {n : Type*} [Fintype n] [DecidableEq n] {b : ℝ} (hb : 0 < b) (r : ℝ) :
    (0 : Matrix n n ℂ).shiftedPowerTail b r = b ^ r • 1 := by
  rw [PosSemidef.shiftedPowerTail_eq_cfc PosSemidef.zero hb]
  simp [not_le.mpr hb, Algebra.algebraMap_eq_smul_one]

private def singularDensity : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (fun i ↦ (![1, 0] i : ℝ))

private theorem singularDensity_psd : singularDensity.PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

private theorem singularDensity_trace : singularDensity.trace = 1 := by
  norm_num [singularDensity, trace, Fin.sum_univ_two]

example : singularDensity.det = 0 := by
  norm_num [singularDensity, det_fin_two]

example {b : ℝ} (hb : 0 < b) (r : ℝ) :
    (singularDensity.shiftedPowerHead b r).rank ≤ 1 / b :=
  singularDensity_psd.rank_shiftedPowerHead_le singularDensity_trace hb r

example : singularDensity.spectralProjectionGE (1 / 4) = diagonal ![1, 0] := by
  rw [spectralProjectionGE, singularDensity, cfc_diagonal _ _ ((Set.finite_range _).continuousOn _)]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

private theorem singularDensity_projection_two : singularDensity.spectralProjectionGE 2 = 0 := by
  rw [spectralProjectionGE, singularDensity, cfc_diagonal _ _ ((Set.finite_range _).continuousOn _)]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

example (r : ℝ) : singularDensity.shiftedPowerHead 2 r = 0 := by
  simp only [shiftedPowerHead, singularDensity_projection_two, mul_zero]

example (r : ℝ) : (singularDensity.shiftedPowerHead 2 r).rank = 0 := by
  rw [singularDensity_psd.rank_shiftedPowerHead (by norm_num), singularDensity_projection_two]
  exact rank_zero

example {b : ℝ} (hb : 0 < b) (r : ℝ) :
    (singularDensity + b • 1) ^ (-r) * (singularDensity + b • 1) ^ r = 1 :=
  CFC.rpow_neg_mul_rpow r (singularDensity_psd.add_smul_one_posDef hb).isStrictlyPositive

private def boundaryDensity : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (fun _ ↦ ((1 / 2 : ℝ) : ℂ))

private theorem boundaryDensity_psd : boundaryDensity.PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ ((1 / 2 : ℝ) : ℂ)
  exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num)

private theorem boundaryDensity_trace : boundaryDensity.trace = 1 := by
  norm_num [boundaryDensity, trace, Fin.sum_univ_two]

example : boundaryDensity.spectralProjectionGE (1 / 2) = 1 := by
  rw [spectralProjectionGE, boundaryDensity, cfc_diagonal _ _ ((Set.finite_range _).continuousOn _)]
  norm_num [diagonal_one]

example (r : ℝ) : boundaryDensity.shiftedPowerTail (1 / 2) r = 0 := by
  rw [boundaryDensity_psd.shiftedPowerTail_eq_cfc (by norm_num), boundaryDensity,
    cfc_diagonal _ _ ((Set.finite_range _).continuousOn _)]
  norm_num

example : (boundaryDensity.shiftedPowerHead (1 / 2) 1).rank = 2 := by
  rw [boundaryDensity_psd.rank_shiftedPowerHead (by norm_num), spectralProjectionGE,
    boundaryDensity, cfc_diagonal _ _ ((Set.finite_range _).continuousOn _)]
  norm_num [diagonal_one, rank_one]

example : (boundaryDensity.shiftedPowerHead 2 1).rank ≤ 1 / (2 : ℝ) :=
  boundaryDensity_psd.rank_shiftedPowerHead_le boundaryDensity_trace (by norm_num) 1

/-- The tail bound is false for negative exponents, even for a singular trace-one density. -/
example : ¬ ‖singularDensity.shiftedPowerTail (1 / 4) (-1)‖ ≤
    (2 * (1 / 4 : ℝ)) ^ (-1 : ℝ) := by
  have heq : singularDensity.shiftedPowerTail (1 / 4) (-1) = diagonal ![0, 4] := by
    rw [singularDensity_psd.shiftedPowerTail_eq_cfc (by norm_num), singularDensity,
      cfc_diagonal _ _ ((Set.finite_range _).continuousOn _)]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Real.rpow_neg_one]
  rw [heq, l2_opNorm_diagonal]
  intro h
  have hv := norm_le_pi_norm (![0, 4] : Fin 2 → ℂ) 1
  norm_num [Real.rpow_neg_one] at h hv
  linarith

/-- A shifted inverse-filter tail need not be a contraction. -/
example : ¬ ‖boundaryDensity.shiftedPowerTail 1 1‖ ≤ 1 := by
  rw [boundaryDensity_psd.shiftedPowerTail_eq_cfc (by norm_num), boundaryDensity,
    cfc_diagonal _ _ ((Set.finite_range _).continuousOn _), l2_opNorm_diagonal]
  norm_num
