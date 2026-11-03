# Linear control of the logarithmic interleaved count

For fixed `U>=1` and every `w>=1`, put `v=U+log(1+w)`. Mathlib's logarithm-versus-positive-power estimate at exponent `1/16` gives `v <= (U+17) w^(1/16)`. Consequently, `v^7 <= (U+17)^7 w` and `sqrt(w) v^4 <= (U+17)^4 w`.

The actual calibrated count estimate has the form `log D <= A (v^7/g + sqrt(w) v^4/sqrt(g))`. The new inequalities make its right-hand side linear in `w`, with a coefficient fixed before `w`. At `w=1+log r+2log(L+1)`, exponentiation therefore bounds the honest length- and rank-dependent count polynomially at fixed physical dimension and gap. The physical count estimate and the actual final-output costs are separate inputs to that subsequent application; no desired polynomial bound is supplied as a hypothesis of a physical theorem.

The proof reuses Mathlib's power monotonicity, real-power multiplication and logarithm estimate. It introduces no new proof automation or resource option. Strict actual-name elaboration passes in 4.394 seconds at the default budget. Imported inspection of both public declarations passes in 4.198 seconds with only `propext`, `Classical.choice` and `Quot.sound`; the temporary source is deleted. This is auxiliary to ALVV, arXiv:1602.08828v2, lines 1797–1817, for the corrected interleaved parameters. It does not assert the printed parameter dependence or runtime.
