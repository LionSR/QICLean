import QICLean.Analysis.PolarUnitaryCorrectionKronecker

/-! Raw axiom reports for the polar-unitary correction theorems. -/

set_option linter.hashCommand false

#print axioms Matrix.PosSemidef.norm_le_norm_add_toEuclideanCLM
#print axioms Matrix.PosSemidef.norm_sub_le_add_residuals
#print axioms Matrix.PosSemidef.norm_one_sub_le_norm_one_sub_sq
#print axioms Matrix.norm_unitary_sub_le_add_residuals_of_mul_posSemidef
#print axioms Matrix.exists_unitary_polar_correction
#print axioms Matrix.unitary_polar_correction_kronecker_one
