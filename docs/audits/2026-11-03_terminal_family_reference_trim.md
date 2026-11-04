# A deterministic terminal full-family image and original-reference trim

The terminal theorem applies the same fixed family once to the current space
and collectively trims its actual image with the same original-target reference.
There is no new sample or existential replacement for the image or trim.
All family, target and reference data precede the current input space.

Starting from original-target error `0.04`, mutual target closeness `1/200`
gives improving-target input error `9/100`. The theorem retains the exact
image error `Delta / (91/100)^2` for every improving target. The existing
scalar estimate, under `D >= 2` and `D^12 * Delta <= 1/100000`, bounds this
by `1/10000`, without a sign assumption on `Delta`. Transfer back and weighted
original-reference trimming yield original-target output error `3/200`.
The reference conditions remain explicit intermediate hypotheses.

A separate unconditional theorem bounds both the literal image and its trim
by `card(iota) * finrank(W)`. It has no target, viability, increasing-cut or
positive-threshold hypothesis. The terminal theorem retains the resulting
`D^2 * finrank(W)` bounds under the family-cardinality assumption. This handles
the case where a stopped resampling process takes no active round; it does
not identify the process with the printed sample-once Figure, prove joint
probability, or assert a running-time bound.
