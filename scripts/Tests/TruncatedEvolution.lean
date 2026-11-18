import QICLean.ManyBody.Dynamics.TruncatedEvolution

/-! Audit the finite truncation package and exercise the comparison at negative time,
with no local-dimension or nonemptiness assumption. -/
open scoped Matrix.Norms.L2Operator
open ManyBody

#print axioms hasDerivAt_exp_conjugation_variable
#print axioms ManyBody.hasDerivAt_relative_heisenberg
#print axioms ManyBody.norm_heisenbergEvolution_sub_le_of_commutator_bound
#print axioms ManyBody.norm_heisenbergEvolution_sub_le_of_sum_commutator_bound
#print axioms ManyBody.norm_heisenbergEvolution_sub_le_graphDistance
#print axioms ManyBody.norm_heisenbergEvolution_sub_spatial_truncation_le

example {n : Type*} [Fintype n] [DecidableEq n]
    {H K : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    (hc : ∀ s ∈ Set.uIcc (-1 : ℝ) 0,
      (K - H) * heisenbergEvolution K s A = heisenbergEvolution K s A * (K - H)) :
    heisenbergEvolution K (-1) A = heisenbergEvolution H (-1) A := by
  have h := norm_heisenbergEvolution_sub_le_of_commutator_bound hH A (-1) 0 (by
    intro s hs
    rw [hc s (by simpa [Set.uIcc_comm] using hs), sub_self, norm_zero])
  simpa using sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using h) (norm_nonneg _)))
