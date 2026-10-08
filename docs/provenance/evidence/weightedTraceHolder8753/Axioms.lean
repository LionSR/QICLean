import QICLean.Analysis.WeightedTraceHolder
import QICLean.Representation.GroupedLabelEntropy
import QICLean.Representation.MergeExponential
import QICLean.Representation.SchurSurprisal

/-! Exact-name checks of five new and six refactored public declarations. -/
set_option linter.hashCommand false
#print axioms Matrix.IsOrthogonalResolution.prod_hom_fst
#print axioms Matrix.IsOrthogonalResolution.prod_hom_snd
#print axioms Matrix.PosSemidef.re_trace_mul_exp_smul_add_le
#print axioms Matrix.PosSemidef.re_trace_mul_exp_sum_le_prod
#print axioms Matrix.PosSemidef.re_trace_mul_exp_nonneg
#print axioms PermutationRepresentation.joint_hom_fst
#print axioms PermutationRepresentation.joint_hom_snd
#print axioms TensorPower.groupedCopies_labelEntropy_bounds
#print axioms PermutationRepresentation.exp_mergeDeficit_eq_sum
#print axioms PermutationRepresentation.re_trace_mul_exp_mergeDeficit_eq_sum
#print axioms PermutationRepresentation.posSemidef_mergeDeficit
