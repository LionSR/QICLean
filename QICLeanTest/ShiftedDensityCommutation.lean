import QICLean.Analysis.ShiftedDensityCommutation

/-! Exponent zero can erase the commutation information of a positive shift. -/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private def x : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, 1]
private def ρ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 1 1

example : x.PosSemidef ∧
    Commute ρ ((x + (1 : Matrix (Fin 2) (Fin 2) ℂ)) ^ (0 : ℝ)) ∧
    ¬Commute ρ x := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [x, Matrix.posSemidef_diagonal_iff, Fin.forall_fin_two]
  · have hx : x.PosSemidef := by
      norm_num [x, Matrix.posSemidef_diagonal_iff, Fin.forall_fin_two]
    simpa only [CFC.rpow_zero _ (by
      simpa using (hx.add_smul_one_posDef zero_lt_one).posSemidef.nonneg)] using
      Commute.one_right ρ
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 0 1) h.eq
    norm_num [x, ρ, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-! The commutant statements do not require a nonempty index type. -/

example (σ : Matrix (Fin 0) (Fin 0) ℂ) {r : ℝ} (hr : r ≠ 0) :
    Commute ((0 + (1 : ℝ) • (1 : Matrix (Fin 0) (Fin 0) ℂ)) ^ r) σ ↔
      Commute (0 : Matrix (Fin 0) (Fin 0) ℂ) σ := by
  exact Matrix.PosSemidef.zero.commute_add_smul_one_rpow_iff zero_lt_one hr

/-! A singular positive semidefinite matrix becomes positive definite after a positive shift. -/

example : x.det = 0 ∧ (x + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosDef := by
  constructor
  · norm_num [x, Matrix.det_fin_two, Matrix.diagonal]
  · have hx : x.PosSemidef := by
      norm_num [x, Matrix.posSemidef_diagonal_iff, Fin.forall_fin_two]
    exact hx.add_smul_one_posDef zero_lt_one

example (σ : Matrix (Fin 2) (Fin 2) ℂ) {b r : ℝ} (hb : 0 < b) (hr : r ≠ 0) :
    Commute ((x + b • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ^ r) σ ↔ Commute x σ := by
  have hx : x.PosSemidef := by
    norm_num [x, Matrix.posSemidef_diagonal_iff, Fin.forall_fin_two]
  exact hx.commute_add_smul_one_rpow_iff hb hr

/-! Exponent two recovers commutation with the positive definite filter itself. -/

example {n : Type*} [Fintype n] [DecidableEq n] {L σ : Matrix n n ℂ}
    (hL : L.PosDef) (hcomm : Commute (L ^ (2 : ℝ)) σ) : Commute L σ := by
  exact (hL.commute_rpow_iff (by norm_num : (2 : ℝ) ≠ 0)).mp hcomm

/-! The inverse-power implication allows singular input and an arbitrary second matrix. -/

example {σ : Matrix (Fin 2) (Fin 2) ℂ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcomm : Commute σ ((x + b • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ^ (-a / 2))) :
    Commute σ x := by
  have hx : x.PosSemidef := by
    norm_num [x, Matrix.posSemidef_diagonal_iff, Fin.forall_fin_two]
  exact hx.commute_of_commute_shifted_inverse_power ha hb hcomm
