# Public finite quadratic dyadic moment

`Real.sum_quadratic_div_dyadic_le` in
`Analysis/ProbabilityEntropyRankTails.lean` is now public. Its statement
and proof are unchanged. The existing finite potential proof bounds
$\sum_{i<M}(ai^2+bi+c)/2^{i+1}$ by $3a+b+c$ for nonnegative coefficients.
The same result supplies the generic entropy theorem already in this
module and the actual changing-target AKLV entropy summation in TNLean.
No second moment lemma, potential proof, or module is introduced.

The actual modified module passed a strict private check in 5.76 seconds
against the fully checked QIC snapshot
`ec3434f7d6fbdfc5318dc55934feb9532e239b81`, using the exact matching
package of fully checked TNLean mathematical source
`28e38efedb8621056c907c8ad20e1edd24003a20` and documentation-only successor
`7f87bdc8f1b2354be4950ad515dedda7ee9bec96`.
The selected imported source and ordinary objects were guarded, and the
new object was written only to a private temporary namespace. No cache
or provider was edited or copied, no Mathlib source was built, and no
ordinary build was queued. A temporary imported foundation inspection passed in 3.03 seconds and
found only `propext`, `Classical.choice`, and `Quot.sound`. The new
blueprint entry covers the public declaration; ordinary
build and compiled blueprint checks remain integration gates.

The new chapter belongs near the existing finite rank-tail entropy
estimate in Chapter 12. Chapter registration and generated aggregators
are excluded.
