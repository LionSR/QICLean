/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.SchurSectorMass

/-! Exact-name stock-kernel reports for the Schur-sector mass theorems. -/

-- Diagnostic commands are the purpose of this evidence file.
set_option linter.hashCommand false in
#print axioms TensorPower.exists_labelProj_trace_mass_ge

set_option linter.hashCommand false in
#print axioms TensorPower.exists_labelProj_norm_mass_ge
