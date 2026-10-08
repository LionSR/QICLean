import QICLean.Analysis.SpectralProjectionIntertwiner
import QICLean.Representation.PairMergeDeficit

/-! Imported checks of the frozen merge-positivity contribution. -/
#check PermutationRepresentation.posSemidef_mergeDeficit
#check TensorPower.posSemidef_pairMergeDeficit
#check Matrix.PosSemidef.spectralProjectionGE_zero
#check Matrix.spectralProjectionGE_zero_mul_of_intertwine
