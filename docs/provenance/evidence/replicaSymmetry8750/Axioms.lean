/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaPermutationCovariance

/-! Exact-name stock-kernel reports for replica copy symmetry. -/

-- These diagnostic commands are the purpose of this evidence file.
set_option linter.hashCommand false

#print axioms Matrix.commute_replicaHamiltonian_permOp
#print axioms Matrix.commute_cfc_replicaDefectCount_permOp
#print axioms Matrix.commute_cfc_replicaDefectCount_kronecker
#print axioms Matrix.cfc_replicaDefectCount_kronecker_mulVec_preserves_fixed
#print axioms Matrix.commute_finKronecker_const_permOp
