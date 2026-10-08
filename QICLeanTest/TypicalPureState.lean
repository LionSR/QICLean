import QICLean.Entropy.TypicalPureState

/-! Tests of full and empty spectral selections, including singular marginals. -/

open scoped Matrix InnerProductSpace ComplexOrder

noncomputable section

namespace TypicalPureStateTest

/-- A two-dimensional first factor and a one-dimensional complementary factor
force a singular first marginal. Selecting the entire spectrum nevertheless
returns the original unit vector, including its zero eigenvalue. -/
theorem fullSelection_singular (ψ : EuclideanSpace ℂ (Fin 2 × Fin 1)) (hψ : ‖ψ‖ = 1) :
    Matrix.typicalPureState ψ Finset.univ = ψ := by
  have htr : (Matrix.partialTraceRight (Matrix.vecMulVec ψ (star ψ))).trace = 1 := by
    rw [Matrix.trace_partialTraceRight]
    change ⟪ψ, ψ⟫_ℂ = 1
    simp [hψ]
  let hρ := (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceRight
  have hz : hρ.isHermitian.spectralRestrictionMass Finset.univ = 1 := by
    simpa [Matrix.IsHermitian.spectralRestrictionMass, htr] using
      hρ.isHermitian.re_trace_eq_sum_eigenvalues.symm
  have he := Matrix.norm_sub_typicalPureState_sq ψ Finset.univ hψ
    (by simpa only [hz] using (zero_lt_one : (0 : ℝ) < 1))
  rw [hz, Real.sqrt_one, sub_self, mul_zero] at he
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he))).symm

/-- Empty selection has zero mass and gives the zero vector. -/
theorem emptySelection (ψ : EuclideanSpace ℂ (Fin 2 × Fin 3)) :
    Matrix.typicalPureState ψ ∅ = 0 := by
  simp [Matrix.typicalPureState, Matrix.IsHermitian.spectralRestrictionMass]

end TypicalPureStateTest
