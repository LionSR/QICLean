import QICLean.Analysis.ReplicaExcitationSymmetry

/-! Exact kernel dependency reports for the three excitation-symmetry results. -/

-- Printing the reports is the purpose of this audit file.
set_option linter.hashCommand false

#print axioms Matrix.permOp_mul_replicaExcitationProjection
#print axioms Matrix.commute_replicaExcitationProjection_kronecker_of_image_eq
#print axioms Matrix.replicaExcitationProjection_kronecker_mulVec_preserves_fixed
