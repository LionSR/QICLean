import QICLean.Entropy.IidSurprisal

/-! Exact-name kernel audit of the four independent-copy concentration results. -/

set_option linter.hashCommand false

#print axioms Matrix.PosSemidef.re_trace_finKronecker_mul_cfc_surprisal
#print axioms Entropy.surprisalTail_pi_le_variance
#print axioms Matrix.PosSemidef.re_trace_surprisalTail_finKronecker_le
#print axioms Matrix.PosSemidef.re_trace_surprisalTail_finKronecker_three_quarters_le
