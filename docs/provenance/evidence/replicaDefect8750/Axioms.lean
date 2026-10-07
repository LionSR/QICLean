import QICLean.Analysis.ReplicaExcitationDecomposition

/-! Exact kernel axiom reports for the physical replica declarations. -/

set_option linter.hashCommand false

#print axioms Matrix.replicaHamiltonian
#print axioms Matrix.replicaDefectCount
#print axioms Matrix.replicaHamiltonian_mulVec_prod
#print axioms Matrix.replicaMeanHamiltonian_kronecker_mulVec_prod
#print axioms Matrix.PosSemidef.replica_gap
#print axioms Matrix.posSemidef_replicaDefectCount
#print axioms Matrix.spectralCutoff_replica_gap_mass_ge
#print axioms Matrix.replicaExcitationProjection
#print axioms Matrix.isStarProjection_replicaExcitationProjection
#print axioms Matrix.sum_replicaExcitationProjection
#print axioms Matrix.replicaDefectCount_mul_replicaExcitationProjection
#print axioms Matrix.cfc_replicaDefectCount_eq_sum_replicaExcitationProjection
#print axioms Matrix.replicaExcitationProjection_mul_of_ne
#print axioms Matrix.replicaDefectCutoff_decomposition
