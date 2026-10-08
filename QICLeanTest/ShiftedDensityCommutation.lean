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
