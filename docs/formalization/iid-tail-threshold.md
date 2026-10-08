# A numerical threshold for independent-copy tail estimates

For any fixed real coefficient V and natural degree m, the module
`QICLean/Analysis/IidTailThreshold.lean` proves that, eventually for k ≥ 1,

V/√k + (k + 1)ᵐ exp(−k³⁄⁴/2) ≤ 1/2.

The division by two is inside the exponential. The coefficient need not
be nonnegative, so the theorem includes its intended application to a
surprisal variance without a further specialization. The degree and
coefficient are fixed while k tends to infinity. The conclusion gives an
eventual threshold; it does not provide an explicit value for that threshold.

The proof uses Mathlib's decay of tˢ exp(−bt) for b > 0, with t = k³⁄⁴,
s = 4m/3 and b = 1/2. For k ≥ 1, the shifted polynomial is at most 2ᵐkᵐ.
The inverse-square-root term also tends to zero. No density matrix,
spectral cutoff, label or assumed concentration estimate occurs in the
statement or proof.

The source is OpenAI, *A two-dimensional area law from a global spectral
gap* (September 24, 2026), `07-comparators.tex`, lines 255–281,
`comparator:high-label`, at mathematical source commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. This is the numerical step that
allows the independent-copy surprisal tail and the label-observable tail
to have total mass at most one half. Their actual spectral estimates and
the subsequent label selection are separate results.

The proof was independently formalized; no upstream Lean proof text was
reused. The unique mathematical fragment is
`blueprint/src/fragment/iid_tail_threshold.tex`.
