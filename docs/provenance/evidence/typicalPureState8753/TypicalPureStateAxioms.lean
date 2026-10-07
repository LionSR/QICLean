import QICLean.Entropy.TypicalPureState

/-! Kernel dependency reports for the public typical pure-state declarations. -/

set_option linter.hashCommand false

#print axioms Matrix.leftFilteredVector
#print axioms Matrix.leftFilteredVector_eq_kronecker
#print axioms Matrix.partialTraceLeft_projection_split
#print axioms Matrix.typicalPureState
#print axioms Matrix.partialTraceRight_typicalPureState
#print axioms Matrix.norm_typicalPureState
#print axioms Matrix.inner_typicalPureState
#print axioms Matrix.norm_sub_typicalPureState_sq
#print axioms Matrix.norm_sub_typicalPureState_sq_le
#print axioms Matrix.partialTraceLeft_typicalPureState
#print axioms Matrix.partialTraceLeft_typicalPureState_decomposition
#print axioms Matrix.partialTraceLeft_typicalPureState_le
#print axioms Matrix.entropy_partialTraceLeft_typicalPureState_le
