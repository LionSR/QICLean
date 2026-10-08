import QICLean.Representation.SchurLabelMoments

/-! Exact-name checks of the three centered Schur-label moment transfers. -/
set_option linter.hashCommand false
#check PermutationRepresentation.re_trace_mul_exp_centered_labelEntropy_le
#check PermutationRepresentation.re_trace_mul_exp_neg_centered_labelEntropy_le
#check TensorPower.centered_labelEntropy_moments_le
