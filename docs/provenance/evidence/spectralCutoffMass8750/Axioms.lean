/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralCutoffMass

/-! Strict kernel audit of the actual closed spectral cutoff bounds. -/

set_option linter.hashCommand false

#print axioms Matrix.PosSemidef.smul_one_sub_spectralCutoff_le
#print axioms Matrix.PosSemidef.spectralCutoff_mass_ge
