import QICLean.Analysis.WeightedTraceHolder
import QICLean.Representation.GroupedLabelEntropy
import QICLean.Representation.MergeExponential
import QICLean.Representation.SchurSurprisal

/-! Exact-name checks of five new and six refactored public declarations. -/
set_option linter.hashCommand false
set_option pp.width 140
#check @Matrix.IsOrthogonalResolution.prod_hom_fst
#check @Matrix.IsOrthogonalResolution.prod_hom_snd
#check @Matrix.PosSemidef.re_trace_mul_exp_smul_add_le
#check @Matrix.PosSemidef.re_trace_mul_exp_sum_le_prod
#check @Matrix.PosSemidef.re_trace_mul_exp_nonneg
#check @PermutationRepresentation.joint_hom_fst
#check @PermutationRepresentation.joint_hom_snd
#check @TensorPower.groupedCopies_labelEntropy_bounds
#check @PermutationRepresentation.exp_mergeDeficit_eq_sum
#check @PermutationRepresentation.re_trace_mul_exp_mergeDeficit_eq_sum
#check @PermutationRepresentation.posSemidef_mergeDeficit
