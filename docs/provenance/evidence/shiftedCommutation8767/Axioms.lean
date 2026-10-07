import QICLean.Analysis.ShiftedDensityCommutation

/-! Public axiom audit for commutation recovered from a shifted inverse power. -/

set_option linter.hashCommand false

#print axioms Matrix.PosDef.commute_rpow_iff
#print axioms Matrix.PosSemidef.commute_add_smul_one_rpow_iff
#print axioms Matrix.PosSemidef.commute_of_commute_shifted_inverse_power
