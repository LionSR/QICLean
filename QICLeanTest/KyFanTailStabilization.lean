import QICLean.Analysis.SpectralTailTraceNorm

open scoped Matrix ComplexOrder MatrixOrder

-- Stabilization also covers the empty matrix type.
example (A : Matrix (Fin 0) (Fin 0) ℂ) (hA : A.IsHermitian) :
    hA.kyFanNorm 3 = A.trace.re := by
  exact hA.kyFanNorm_eq_trace_re_of_card_le (by simp)

-- At an oversized cutoff, tail stability reduces to nonnegativity of trace distance.
example (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (htr : A.trace = B.trace) :
    A.trace.re - hA.kyFanNorm 5 ≤
      B.trace.re - hB.kyFanNorm 5 + Matrix.traceDistance A B := by
  exact hA.trace_sub_kyFanNorm_le_add_traceDistance hB htr 5
