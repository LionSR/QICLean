/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.Renyi.VonNeumannBound

/-! # Axioms for the bound of Rényi entropies of order above one by the von Neumann entropy -/

set_option linter.hashCommand false

/-- info: 'Entropy.inv_one_sub_mul_log_sum_rpow_le_probabilityEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.inv_one_sub_mul_log_sum_rpow_le_probabilityEntropy

/-- info: 'renyiEntropy_le_vonNeumannEntropy_of_one_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms renyiEntropy_le_vonNeumannEntropy_of_one_lt

/-- info: 'Matrix.PosSemidef.renyiEntropy_le_vonNeumannEntropy_of_one_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.renyiEntropy_le_vonNeumannEntropy_of_one_lt
