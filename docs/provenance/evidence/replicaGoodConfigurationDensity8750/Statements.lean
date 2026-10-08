import QICLean.Analysis.ReplicaGoodConfigurationDensity

/-! Exact imported full-good configuration declaration audit. -/
set_option linter.hashCommand false
#check TensorPower.fiveFactorCopiesEquiv
#check Matrix.replicaGoodConfigurationMarginal
#check Matrix.symProj_mul_replicaGoodConfigurationMarginal
