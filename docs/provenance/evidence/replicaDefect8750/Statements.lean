import QICLean.Analysis.ReplicaExcitationDecomposition

/-! Complete public statements and physical replica definitions. -/

set_option linter.hashCommand false

#check Matrix.replicaHamiltonian
#check Matrix.replicaDefectCount
#check Matrix.replicaHamiltonian_mulVec_prod
#check Matrix.replicaMeanHamiltonian_kronecker_mulVec_prod
#check Matrix.PosSemidef.replica_gap
#check Matrix.posSemidef_replicaDefectCount
#check Matrix.spectralCutoff_replica_gap_mass_ge
#check Matrix.replicaExcitationProjection
#check Matrix.isStarProjection_replicaExcitationProjection
#check Matrix.sum_replicaExcitationProjection
#check Matrix.replicaDefectCount_mul_replicaExcitationProjection
#check Matrix.cfc_replicaDefectCount_eq_sum_replicaExcitationProjection
#check Matrix.replicaExcitationProjection_mul_of_ne
#check Matrix.replicaDefectCutoff_decomposition

#print Matrix.replicaHamiltonian
#print Matrix.replicaDefectCount
#print Matrix.replicaExcitationProjection
