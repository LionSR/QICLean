/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.TypicalSpectrum

/-! Axiom audit for the typical-spectrum entropy estimates. -/

set_option linter.hashCommand false

#print axioms Entropy.normalizedRestriction
#print axioms Entropy.sum_normalizedRestriction
#print axioms Entropy.normalizedRestriction_pos
#print axioms Entropy.log_card_typical_centered
#print axioms Entropy.entropy_normalizedRestriction_typical_centered
#print axioms Entropy.typicalSpectrum_entropy_bounds
