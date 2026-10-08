/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.PairMergeMoment

/-! Exact stock-kernel reports for the seven original paired merge declarations. -/
set_option linter.hashCommand false
#print axioms TensorPower.pairCopyLeft
#print axioms TensorPower.pairCopyRight
#print axioms TensorPower.pairCopyBoth
#print axioms TensorPower.commute_pairCopy
#print axioms TensorPower.pairCopyBoth_eq_mul
#print axioms TensorPower.pair_merge_moment_le
#print axioms TensorPower.pair_merge_moment_le_mul_trace
