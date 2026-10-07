/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchmidtBellPrevector

/-! Exact-name stock-kernel reports for the actual Schmidt and Bell prevector identities. -/

-- These diagnostic commands are the purpose of this evidence file.
set_option linter.hashCommand false

#print axioms TensorPower.selectedBellProjection_replicaPrevector
#print axioms TensorPower.exists_label_sequence_schmidtBellPrevector
