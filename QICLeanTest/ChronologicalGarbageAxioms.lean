/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ChronologicalGarbage

/-! Kernel axiom audit for every public declaration in ChronologicalGarbage. -/

#print axioms Matrix.garbageInventory
#print axioms Matrix.garbageInventoryFintype
#print axioms Matrix.garbageInventoryDecidableEq
#print axioms Matrix.euclideanTensorVector
#print axioms Matrix.euclideanTensorVector_apply
#print axioms Matrix.norm_euclideanTensorVector
#print axioms Matrix.euclideanOuterProduct_tensorVector
#print axioms Matrix.trace_euclideanOuterProduct_self
#print axioms Matrix.partialTraceRight_tensorVector
#print axioms Matrix.idleGarbageLift
#print axioms Matrix.appendGarbageGate
#print axioms Matrix.idleGarbageLift_mulVec
#print axioms Matrix.idleGarbageLift_append_mulVec
#print axioms Matrix.idleGarbageLift_eq_kronecker_submatrix
#print axioms Matrix.norm_idleGarbageLift_le
#print axioms Matrix.idleGarbageLift_sub
#print axioms Matrix.norm_idleGarbageLift_sub_le
#print axioms Matrix.appendGarbageGate_mulVec
#print axioms Matrix.norm_appendGarbageGate_le
#print axioms Matrix.kronecker_one_tensorVector
#print axioms Matrix.cumulativeGarbageVector
#print axioms Matrix.chronologicalGarbageChain
#print axioms Matrix.chronologicalReplacementChain
#print axioms Matrix.chronologicalReplacementChain_sub_norm_le
#print axioms Matrix.chronologicalReplacementChain_norm_le_one
#print axioms Matrix.norm_cumulativeGarbageVector
#print axioms Matrix.chronologicalGarbageChain_prefix_vector
#print axioms Matrix.chronologicalGarbageChain_discard_density
#print axioms Matrix.chronologicalGarbageChain_norm_le_one
#print axioms Matrix.chronologicalGarbageReadout
#print axioms Matrix.chronologicalGarbageReadout_eq
#print axioms Matrix.chronologicalGarbageReadout_discard_density
