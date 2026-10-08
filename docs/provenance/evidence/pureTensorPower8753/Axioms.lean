/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.PureTensorPower

/-! Exact-name stock-kernel reports for actual pure tensor-power identities. -/

-- These diagnostic commands are the purpose of this evidence file.
set_option linter.hashCommand false

#print axioms Matrix.partialTraceLeft_vecMulVec_prod
#print axioms Matrix.norm_sq_one_kronecker_mulVec_prod
