import QICLean.Analysis.ShiftedPowerDerivative

/-! Regressions for scalar-shift derivatives, including singular and empty matrices. -/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

example (A : Matrix Empty Empty ℂ) (hA : A.PosSemidef) {b : ℝ}
    (hb : 0 < b) (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (A + s • 1) ^ r) (r • (A + b • 1) ^ (r - 1)) b :=
  hA.hasDerivAt_add_smul_one_rpow hb r

example (A : Matrix Empty Empty ℂ) (hA : A.PosSemidef) (R r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (A + Real.exp (-s) • 1) ^ r)
      ((-r * Real.exp (-R)) • (A + Real.exp (-R) • 1) ^ (r - 1)) R :=
  hA.hasDerivAt_add_exp_neg_smul_one_rpow R r

example (A : Matrix Empty Empty ℂ) (hA : A.PosSemidef) {b : ℝ} (hb : 0 < b) :
    ‖b • (A + b • 1) ^ (-1 : ℝ)‖ ≤ 1 :=
  hA.l2_opNorm_smul_add_smul_one_rpow_neg_one_le hb

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) {b : ℝ} (hb : 0 < b) :
    HasDerivAt (fun s : ℝ ↦ (A + s • 1) ^ (0 : ℝ)) 0 b := by
  simpa using hA.hasDerivAt_add_smul_one_rpow hb 0

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (R : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (A + Real.exp (-s) • 1) ^ (0 : ℝ)) 0 R := by
  simpa using hA.hasDerivAt_add_exp_neg_smul_one_rpow R 0

private def singularDensity : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 0]

private theorem singularDensity_psd : singularDensity.PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

example : singularDensity.det = 0 := by
  norm_num [singularDensity, det_fin_two]

example {b : ℝ} (hb : 0 < b) (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (singularDensity + s • 1) ^ r)
      (r • (singularDensity + b • 1) ^ (r - 1)) b :=
  singularDensity_psd.hasDerivAt_add_smul_one_rpow hb r

example {b : ℝ} (hb : 0 < b) :
    ‖b • (singularDensity + b • 1) ^ (-1 : ℝ)‖ ≤ 1 :=
  singularDensity_psd.l2_opNorm_smul_add_smul_one_rpow_neg_one_le hb

example {n : Type*} [Fintype n] [DecidableEq n] {b : ℝ} (hb : 0 < b) (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ((0 : Matrix n n ℂ) + s • 1) ^ r)
      (r • ((0 : Matrix n n ℂ) + b • 1) ^ (r - 1)) b :=
  PosSemidef.zero.hasDerivAt_add_smul_one_rpow hb r

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (R a : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (A + Real.exp (-s) • 1) ^ (-a / 2))
      (((a / 2) * Real.exp (-R)) •
        ((A + Real.exp (-R) • 1) ^ (-1 : ℝ) *
          (A + Real.exp (-R) • 1) ^ (-a / 2))) R := by
  have heq : -a / 2 - 1 = (-1 : ℝ) + (-a / 2) := by ring
  have h := hA.hasDerivAt_add_exp_neg_smul_one_rpow R (-a / 2)
  rw [heq, CFC.rpow_add (hA.add_smul_one_posDef
    (Real.exp_pos (-R))).isStrictlyPositive.isUnit] at h
  simpa only [neg_div, neg_neg] using h

/-- Nonnegativity alone does not discharge the strictly positive shift hypothesis. -/
example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (_hA : A.PosSemidef) (_r : ℝ) : True := by
  fail_if_success have := _hA.hasDerivAt_add_smul_one_rpow (b := 0) (le_refl 0) _r
  fail_if_success have :=
    _hA.l2_opNorm_smul_add_smul_one_rpow_neg_one_le (b := 0) (le_refl 0)
  trivial

/-- The inverse contraction bound fails at a negative shift even for a positive matrix. -/
example : ¬ ‖(-2 : ℝ) • (((3 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) +
    (-2 : ℝ) • 1) ^ (-1 : ℝ)‖ ≤ 1 := by
  have hsum : ((3 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) + (-2 : ℝ) • 1 = 1 := by
    rw [← add_smul]
    norm_num
  rw [hsum, CFC.one_rpow, norm_smul]
  norm_num

/-- No inverse identity at zero follows from these positive-shift results. -/
example : (0 : Matrix (Fin 1) (Fin 1) ℂ) ^ (-1 : ℝ) * 0 ≠ 1 := by
  simp
