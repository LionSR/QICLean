import QICLean.Entropy.IidSurprisal
import QICLean.Analysis.IidTailThreshold

/-! Exact-name kernel audit of the four concentration results and numerical threshold. -/

set_option linter.hashCommand false

#print axioms Matrix.PosSemidef.re_trace_finKronecker_mul_cfc_surprisal
#print axioms Entropy.surprisalTail_pi_le_variance
#print axioms Matrix.PosSemidef.re_trace_surprisalTail_finKronecker_le
#print axioms Matrix.PosSemidef.re_trace_surprisalTail_finKronecker_three_quarters_le
#print axioms Real.eventually_iid_tail_error_le_half
