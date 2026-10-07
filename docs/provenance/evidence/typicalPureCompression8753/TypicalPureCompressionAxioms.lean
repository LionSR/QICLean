/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.TypicalPureCompression

/-! Public kernel dependencies of the selected-space pure-vector construction. -/

set_option linter.hashCommand false

#print axioms Matrix.IsHermitian.spectralSelectionEmbedding
#print axioms Matrix.IsHermitian.isIsometry_spectralSelectionEmbedding
#print axioms Matrix.IsHermitian.spectralSelectionEmbedding_mul_conjTranspose
#print axioms Matrix.compressedTypicalPureState
#print axioms Matrix.kronecker_mulVec_compressedTypicalPureState
#print axioms Matrix.partialTraceRight_compressedTypicalPureState
#print axioms Matrix.partialTraceLeft_compressedTypicalPureState
#print axioms Matrix.norm_compressedTypicalPureState
