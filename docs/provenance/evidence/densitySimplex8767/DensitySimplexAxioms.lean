import QICLean.Analysis.DensitySimplex

/-! Public kernel reports for the regularized density simplex. -/

set_option linter.hashCommand false

#print axioms Entropy.simplex_ratio_conditions_of_isMinOn
#print axioms Entropy.simplexFilterObjective
#print axioms Entropy.normalizedFilterWeights
#print axioms Entropy.hasFDerivAt_simplexFilterObjective
#print axioms Entropy.simplexFilterObjective_pos
#print axioms Entropy.normalizedFilterWeights_nonneg
#print axioms Entropy.sum_normalizedFilterWeights
#print axioms Entropy.normalizedFilterWeights_clipped_of_isMinOn
