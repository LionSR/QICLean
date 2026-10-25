import QICLean.Analysis.SpectralTailTraceNorm

/-! # Axiom guards for Ky-Fan tail stabilization -/

/-- info:
'Matrix.IsHermitian.kyFanNorm_eq_trace_re_of_card_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.IsHermitian.kyFanNorm_eq_trace_re_of_card_le

/-- info:
'Matrix.IsHermitian.trace_sub_kyFanNorm_le_add_traceDistance' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.IsHermitian.trace_sub_kyFanNorm_le_add_traceDistance
