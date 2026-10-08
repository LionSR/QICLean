/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FiniteProductInformation
import QICLean.Entropy.FiniteProductSplitting
import QICLean.Entropy.TypicalDensity
import QICLean.Entropy.TypicalSpectrum

/-! Kernel dependencies of the combined area-law proof components. -/

set_option linter.hashCommand false

#print axioms Entropy.normalizedRestriction
#print axioms Entropy.sum_normalizedRestriction
#print axioms Entropy.normalizedRestriction_pos
#print axioms Entropy.log_card_typical_centered
#print axioms Entropy.entropy_normalizedRestriction_typical_centered
#print axioms Entropy.typicalSpectrum_entropy_bounds
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
#print axioms FiniteProduct.splitTwoRegionsEquiv
#print axioms FiniteProduct.splitTwoRegionsState
#print axioms FiniteProduct.partialTraceRight_splitTwoRegionsState
#print axioms FiniteProduct.splitTwoRegionsState_unit
#print axioms FiniteProduct.exists_isIsometry_splitTwoRegionsState_norm_sub_le
#print axioms FiniteProduct.exists_isIsometry_splitTwoRegionsState_norm_sub_le_zpow
#print axioms FiniteProduct.conditionalMutualInformation_nonneg
#print axioms FiniteProduct.entropy_submodular
#print axioms FiniteProduct.mutualInformation_mono_left
