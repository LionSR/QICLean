/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.TypicalDensity

/-! Axiom audit for the actual typical spectral restrictions. -/

set_option linter.hashCommand false

#print axioms Matrix.IsHermitian.spectralSelection
#print axioms Matrix.IsHermitian.spectralRestrictionMass
#print axioms Matrix.IsHermitian.normalizedSpectralRestriction
#print axioms Matrix.IsHermitian.isStarProjection_spectralSelection
#print axioms Matrix.IsHermitian.commute_spectralSelection
#print axioms Matrix.PosSemidef.normalizedSpectralRestriction_posSemidef
#print axioms Matrix.IsHermitian.trace_normalizedSpectralRestriction
#print axioms Matrix.IsHermitian.normalizedSpectralRestriction_eq
#print axioms Matrix.PosSemidef.spectralRestrictionMass_le_one
#print axioms Matrix.IsHermitian.rank_normalizedSpectralRestriction
#print axioms Matrix.PosSemidef.entropy_normalizedSpectralRestriction
#print axioms Matrix.PosSemidef.typicalSpectralRestriction_entropy_bounds
