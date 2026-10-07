/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ExcitationSubsetCounts

/-! # Kernel dependencies of the excitation-subset bounds -/

-- Printing kernel dependencies is the purpose of this audit file.
set_option linter.hashCommand false

#print axioms Real.log_choose_le_mul_binEntropy
#print axioms Real.choose_le_exp_mul_binEntropy
#print axioms Real.sum_choose_le_mul_exp_binEntropy
#print axioms Finset.card_filter_powerset_le_mul_exp_binEntropy
