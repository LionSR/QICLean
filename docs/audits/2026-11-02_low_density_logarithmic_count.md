# A regularized logarithmic bound for the actual low-density count

The generic count calculation is separated from the absorption and
suppression argument. The new generic count theorem retains both the
sharper linear-in-degree bound used in suppression and the cubic
logarithmic bound used in the final dimension estimate. No physical
hypothesis is an input of these scalar results.

For fixed bandwidth `eta > 0`, define `B = max(12, eta)` and
`F = 102 + log B`. At deficit `0 < v ≤ eta`, the cap
`vbar = min(v, eta/2)` satisfies `vbar ≥ v/2`. Thus
`g = min(vbar/6, 1)` has `1/g ≤ B/v`. Choosing
`m = q * ceil(exp 100)` gives `log m ≤ log q + 101` and meets the
dyadic count regularity. The actual initial count satisfies

    log(D³) ≤ K / v * (1 + log q + log(1 + 1/v))³,

where

    K = 66 * (C + 1) * (6 + 2 * log(C + 1)) * B * F³.

This coefficient depends only on the ceiling constant and bandwidth,
before the local dimension or deficit. The positive regularized
logarithm and consistent power are explained in
`docs/paper-gaps/alvv16_low_density_sampling.tex`.
